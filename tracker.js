// Csound Mod Tracker - Full Featured Version
// Uses @csound/browser (Csound 7 WASM)
//
// =============================================================================
// IMPORTANT: NOTE DURATION / NOTE OFF BEHAVIOR
// =============================================================================
// Notes use Csound i-statement (see: csound.com/docs/manual/i.html)
// This applies EVERYWHERE: pattern editor, live preview, playback, AND CSD export.
//
// - p3 (duration) is CALCULATED from BPM: stepDuration = 60 / (bpm * lpb)
// - Duration = steps until next NOTE_OFF or new note in same column * stepDuration
// - If NO NOTE_OFF or new note found: duration = -1 (indefinite, held until stopped)
// - Notes continue (sustain) through empty cells
// - A NOTE_OFF ('OFF') or NEW NOTE in the same track/column ends the previous note
// - Fractional instrument numbers (e.g., 1.00, 1.01) allow polyphony per track
// - Live preview uses -1 duration (held until keyup)
// - Double-click STOP button to kill all notes (panic)
// - Panic uses instr 999 with turnoff2 to kill ALL instances of ALL instruments
//
// =============================================================================
// TIMING ARCHITECTURE (Web Audio Lookahead Scheduler)
// =============================================================================
// Uses precise Web Audio API timing for sample-accurate playback:
// - AudioContext.currentTime is the reference clock (hardware crystal precision)
// - Lookahead scheduler runs every 25ms, scheduling notes 100ms ahead
// - Notes use p2 offset calculated from AudioContext time
// - Visual updates are DECOUPLED from audio - calculated from elapsed time
// - This prevents timing jitter when browser is busy with rendering
// See: MDN Web Audio API Advanced Techniques, "A Tale of Two Clocks"
// =============================================================================

// Global Csound instance
var csound = null;

// Default instruments for 128 tracks (DAW-style)
var defaultInstruments = [];
(function() {
    for (var i = 1; i <= 128; i++) {
        if (i === 1) {
            defaultInstruments.push(`instr 1
; Default instrument template
ifreq = p4
iamp = p5
aenv linsegr 0, 0.01, 1, 0.1, 0.7, 0.1, 0
asig oscil iamp * aenv, ifreq
outs asig, asig
endin`);
        } else {
            defaultInstruments.push(`instr ` + i + `
endin`);
        }
    }
})();

// Piano keyboard mapping (z=C-4, ]=G)
// Lower row: z-/ = C to E (with black keys s,d,g,h,j)
// Upper row: q-] = C+1oct to G+2oct (with black keys 2,3,5,6,7,9,0,=)
var keyboardMap = {
    // Lower octave (z row)
    'z': 0,  's': 1,  'x': 2,  'd': 3,  'c': 4,  'v': 5,
    'g': 6,  'b': 7,  'h': 8,  'n': 9,  'j': 10, 'm': 11,
    ',': 12, 'l': 13, '.': 14, ';': 15, '/': 16,
    // Upper octave (q row)
    'q': 12, '2': 13, 'w': 14, '3': 15, 'e': 16, 'r': 17,
    '5': 18, 't': 19, '6': 20, 'y': 21, '7': 22, 'u': 23,
    'i': 24, '9': 25, 'o': 26, '0': 27, 'p': 28, '-': 29,
    '[': 30, '=': 31, ']': 31
};

var noteNames = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
var NOTE_OFF = 'OFF';

// Track currently pressed keys for live keyboard playing
// Maps key -> { instrNum, freq, track, col }
var pressedKeys = {};

// Web Audio precise timing scheduler
// Uses lookahead scheduling for sample-accurate timing (see MDN Web Audio API guide)
var audioCtx = null;  // AudioContext from Csound WASM
var schedulerTimerId = null;
var scheduleAheadTime = 0.1;  // Schedule notes 100ms ahead (seconds)
var lookahead = 25;           // Check every 25ms (milliseconds)
var nextStepTime = 0;         // When the next step should play (AudioContext time)
var playbackStartTime = 0;    // When playback started (AudioContext time)

// Tracker state - DAW model with 128 tracks and clip-based timeline
var state = {
    csoundReady: false,
    isPlaying: false,
    isRecording: false,
    currentBeat: 0,           // Current playback position in beats (replaces currentStep)
    currentStep: 0,           // Step within current pattern (for step sequencer view)
    bpm: 120,
    lpb: 4,                   // Global default LPB (patterns can override)
    editStep: 1,
    timeSignature: { num: 4, den: 4 },

    // 128 tracks (DAW-style), each corresponds to a Csound instrument
    tracks: [],               // Initialized in initTracks()
    visibleTrackStart: 0,     // First visible track index (scroll position)
    visibleTrackCount: 16,    // Number of visible tracks
    selectedTrack: 0,         // Currently selected track for editing

    // Pattern library - reusable pattern templates
    // Each pattern is single-track data (not multi-track like before)
    patterns: [],

    // Currently selected clip for editing (DAW-style - patterns only exist as clips)
    selectedClip: { trackId: null, clipId: null },

    instruments: defaultInstruments.slice(),
    currentInstrument: 0,
    opcodes: '',
    // Sample library: imported samples not yet loaded to ftables
    sampleLibrary: [],
    // Ftable pool: samples loaded into Csound ftables
    ftablePool: [],
    // Track which ftable numbers are in use (for reuse on delete)
    usedFtables: {},  // tableNum -> true
    nextFtableNum: 100,  // Start ftables at 100 (leave 1-99 for user/system)
    samples: [],  // Legacy, kept for backwards compatibility
    playInterval: null,
    baseOctave: 3,
    focusedTrack: 0,
    focusedNoteCol: 0,
    focusedColumn: 0,
    focusedStep: 0,
    focusedType: 'note',
    activeNotes: new Array(128).fill(null).map(() => ({})),

    // Quantize settings for recording
    quantize: '1/16',         // 'off', '1/4', '1/8', '1/16', '1/32', '1/4T', '1/8T', '1/16T'

    // Piano roll state
    pianoRoll: {
        enabled: false,
        notes: [],            // MIDI-style: { pitch, startBeat, duration, velocity }
        viewStart: 0,         // Scroll position in beats
        viewLength: 16        // Visible beats
    },

    // MIDI state
    midi: {
        enabled: false,
        inputDevice: null,
        ccMappings: {}        // CC number -> parameter mapping
    },

    // Timeline view
    timeline: {
        zoom: 1,              // Pixels per beat
        scrollX: 0,           // Scroll position in pixels
        totalBeats: 64,       // Total timeline length in beats (starts small, auto-extends)
        totalMeasures: 16,    // Total measures (derived from totalBeats / beatsPerMeasure)
        loopEnabled: false,   // Whether loop region is active
        loopStart: 0,         // Loop start in beats
        loopEnd: 16,          // Loop end in beats
        snapToMeasure: true,  // Snap clip placement to measure boundaries
        // Grid snap value in beats: 1/256=0.015625, 1/128=0.03125, 1/64=0.0625, 1/32=0.125, 1/16=0.25, 1/8=0.5, 1/4=1, 1/2=2, 1bar=4
        gridSnap: 1,          // Default: 1 beat (quarter note)
        gridSnapOptions: [
            { label: '1/256', beats: 1/64 },
            { label: '1/128', beats: 1/32 },
            { label: '1/64', beats: 1/16 },
            { label: '1/32', beats: 1/8 },
            { label: '1/16', beats: 1/4 },
            { label: '1/8', beats: 1/2 },
            { label: '1/4', beats: 1 },
            { label: '1/2', beats: 2 },
            { label: '1 Bar', beats: 4 }
        ]
    }
};

// DOM cache
var domCache = {};

// Pattern grid cache
var patternGridCache = {};
var currentGridPatternIndex = -1;

// Incremental compilation tracking - stores last compiled state
var lastCompiled = {
    instruments: [],    // Array of instrument code strings (indexed by instrument number)
    opcodes: '',        // Last compiled UDO code
    ftables: {}         // Map of tableNum -> { fileName, code }
};

// Playback timing
var pendingVisualUpdate = null;
var lastPlayedStep = -1;

// Track last scheduled step for each clip to prevent duplicate triggers
// Key: "trackId_clipId", Value: { step: number, loopCount: number }
var clipLastStep = {};

// Voice allocation counter for unique fractional instrument instances
// Increments for each new note, wraps at 999
var voiceCounter = 1;

// Track active voices per track/noteCol (persists across clips on same track)
// Key: "trackId_noteCol", Value: { instrInstance: string, freq: number, amp: number, fxCount: number, instrNum: number, noteName: string }
var activeVoices = {};

// Debug mode for voice tracking (set to true to see voice operations in console)
var voiceDebugMode = true;

// Log voice operation to console if debug mode is enabled
function logVoice(operation, voiceKey, details) {
    if (!voiceDebugMode) return;
    var msg = '[VOICE] ' + operation + ' | key=' + voiceKey;
    if (details) {
        for (var k in details) {
            msg += ' | ' + k + '=' + details[k];
        }
    }
    consoleLog(msg);
}

// Get a summary of all active voices (for debugging)
function getActiveVoicesSummary() {
    var summary = [];
    for (var key in activeVoices) {
        var v = activeVoices[key];
        summary.push(key + ': i' + v.instrInstance + ' (' + (v.noteName || '?') + ')');
    }
    return summary.length > 0 ? summary.join(', ') : '(none)';
}

// Turn off all active voices by sending note-off messages to Csound
// Called on loop/wrap to ensure held notes don't bleed into the next iteration
function turnOffAllActiveVoices(p2) {
    if (!state.csoundReady) return;

    var voiceKeys = Object.keys(activeVoices);
    if (voiceKeys.length === 0) return;

    var p2Str = (p2 || 0).toFixed(4);

    for (var i = 0; i < voiceKeys.length; i++) {
        var voiceKey = voiceKeys[i];
        var voice = activeVoices[voiceKey];
        if (voice && voice.instrInstance) {
            try {
                // Use instrument 998 (note killer) to turn off each voice
                var offMsg = 'i 998 ' + p2Str + ' 0.01 ' + voice.instrInstance;
                csound.inputMessage(offMsg);
                logVoice('OFF-LOOP', voiceKey, { instr: voice.instrInstance, note: voice.noteName });
            } catch (err) {
                logVoice('OFF-LOOP-ERROR', voiceKey, { error: err.message || err });
            }
        }
    }
}

// Sample Editor state
var sampleEditor = {
    currentSample: null,        // Currently loaded sample in editor
    audioBuffer: null,          // Decoded AudioBuffer
    zoom: 1,                    // Zoom level (1 = fit to view)
    scrollOffset: 0,            // Scroll position in samples
    selection: null,            // { start: samples, end: samples }
    slices: [],                 // Array of slice positions in samples
    selectedSlice: -1,          // Currently selected slice index
    isDragging: false,          // Is a slice being dragged
    dragSliceIndex: -1,         // Which slice is being dragged
    canvas: null,               // Canvas element
    ctx: null,                  // Canvas 2D context
    waveformData: null,         // Pre-computed waveform peaks for display
    undoStack: [],              // Undo stack for slice operations
    maxUndo: 50                 // Maximum undo levels
};

// Clipboard
var clipboard = {
    type: null,
    data: null,
    isRange: false,
    width: 0,
    height: 0
};

// Selection state - uses absolute column index for simple rectangular selection
var selection = {
    active: false,
    startStep: -1,
    startAbsCol: -1,  // Absolute column index across all note columns
    startNoteCol: 0,
    startCol: -1,
    startType: null,
    endStep: -1,
    endAbsCol: -1,
    endNoteCol: 0,
    endCol: -1,
    endType: null
};

// Selected cells array
var selectedCells = [];

// Drag state
var dragState = {
    active: false,
    startX: 0,
    startY: 0
};

// Edit input
var editInput = null;
var editingCell = null;

// Console
var consoleLines = [];
var maxConsoleLines = 512;

function consoleLog(msg) {
    if (!domCache.console) return;
    consoleLines.push(msg);
    if (consoleLines.length > maxConsoleLines) {
        consoleLines.shift();
    }
    domCache.console.textContent = consoleLines.join('\n');
    domCache.console.scrollTop = domCache.console.scrollHeight;
}

window.handleMessage = function(msg) {
    consoleLog(msg.trim());
};

// ============================================
// INITIALIZATION
// ============================================

function initTracks() {
    state.tracks = [];
    // Start with just 1 track - user can add more
    addTrack();
}

// Add a new track
function addTrack() {
    var trackNum = state.tracks.length;
    state.tracks.push({
        id: trackNum,
        visible: true,
        muted: false,
        soloed: false,
        volume: 1.0,
        pan: 0,
        name: 'Track ' + (trackNum + 1),
        clips: []             // Pattern clip instances on this track
        // Clip format: { patternId, startBeat, loopCount }
    });
    return trackNum;
}

// Remove the last track (if more than 1)
function removeTrack() {
    if (state.tracks.length <= 1) return false;
    state.tracks.pop();
    // Adjust selected track if needed
    if (state.selectedTrack >= state.tracks.length) {
        state.selectedTrack = state.tracks.length - 1;
    }
    // Adjust visible track start if needed
    if (state.visibleTrackStart >= state.tracks.length) {
        state.visibleTrackStart = Math.max(0, state.tracks.length - state.visibleTrackCount);
    }
    return true;
}

// Create a new empty tracker pattern (step sequencer style, single-track)
// Structure: multiple note columns, each with note (p4), amp (p5), and expandable FX
function createTrackerPattern(steps, lpb, trackId) {
    var patternNum = state.patterns ? state.patterns.length : 0;
    var pattern = {
        id: patternNum,
        name: 'Pattern ' + (patternNum + 1),
        type: 'tracker',
        trackId: trackId || 0,    // Which track this pattern is placed on (for timeline)
        instrument: 1,            // Which Csound instrument to use (1-128)
        steps: steps || 16,
        lpb: lpb || state.lpb,
        noteColumns: 1,           // Number of note columns (each has note, amp, expandable fx)
        data: new Array(steps || 16)
    };
    for (var step = 0; step < pattern.steps; step++) {
        pattern.data[step] = {
            columns: [
                { note: '', amp: '', fx: [] }  // First note column with expandable FX
            ]
        };
    }
    return pattern;
}

// Add a note column to pattern
function addNoteColumn(patternIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    pattern.noteColumns = (pattern.noteColumns || 1) + 1;

    // Add column to each step
    for (var step = 0; step < pattern.steps; step++) {
        if (!pattern.data[step].columns) {
            pattern.data[step].columns = [{ note: '', amp: '', fx: [] }];
        }
        pattern.data[step].columns.push({ note: '', amp: '', fx: [] });
    }

    markPatternDirty(patternIndex);
}

// Remove a note column from pattern
function removeNoteColumn(patternIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern || (pattern.noteColumns || 1) <= 1) return;

    pattern.noteColumns = pattern.noteColumns - 1;

    // Remove last column from each step
    for (var step = 0; step < pattern.steps; step++) {
        if (pattern.data[step].columns && pattern.data[step].columns.length > 1) {
            pattern.data[step].columns.pop();
        }
    }

    markPatternDirty(patternIndex);
}

// Add FX column to a specific note column in pattern
function addFxColumn(patternIndex, noteColIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    // Update each step's data
    for (var step = 0; step < pattern.steps; step++) {
        var col = pattern.data[step].columns[noteColIndex];
        if (col) {
            col.fx.push('');
        }
    }

    markPatternDirty(patternIndex);
}

// Remove FX column from a specific note column in pattern
function removeFxColumn(patternIndex, noteColIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    // Update each step's data
    for (var step = 0; step < pattern.steps; step++) {
        var col = pattern.data[step].columns[noteColIndex];
        if (col && col.fx.length > 0) {
            col.fx.pop();
        }
    }

    markPatternDirty(patternIndex);
}

// Get FX count for a note column
function getFxCount(pattern, noteColIndex) {
    if (!pattern || !pattern.data || !pattern.data[0]) return 0;
    var col = pattern.data[0].columns[noteColIndex];
    return col ? col.fx.length : 0;
}

// Create a new empty piano roll pattern (MIDI-style notes, single-track)
function createPianoPattern(beats, lpb, trackId) {
    var patternNum = state.patterns ? state.patterns.length : 0;
    var pattern = {
        id: patternNum,
        name: 'Piano ' + (patternNum + 1),
        type: 'piano',            // 'tracker' or 'piano'
        trackId: trackId || 0,    // Which track this pattern belongs to
        beats: beats || 4,        // Length in beats
        lpb: lpb || state.lpb,
        notes: []                 // Array of { pitch, startBeat, duration, velocity }
    };
    return pattern;
}

function initPatterns() {
    // Start with empty pattern library - patterns are created when clips are added
    state.patterns = [];
    state.selectedClip = { trackId: null, clipId: null };
}

// ============================================
// CLIP MANAGEMENT (DAW Timeline)
// ============================================

// Add a clip to a track at a specific beat position
function addClipToTrack(trackId, patternId, startBeat, loopCount) {
    if (trackId < 0 || trackId >= state.tracks.length) return null;
    if (patternId < 0 || patternId >= state.patterns.length) return null;

    // Snap to measure if enabled
    var actualStartBeat = startBeat || 0;
    if (state.timeline.snapToMeasure) {
        actualStartBeat = snapToMeasureStart(actualStartBeat);
    }

    var clip = {
        id: Date.now() + Math.random(),  // Unique clip ID
        patternId: patternId,
        startBeat: actualStartBeat,
        loopCount: loopCount || 1,
        offset: 0  // Offset into pattern in beats (for split clips)
    };

    state.tracks[trackId].clips.push(clip);

    // Auto-extend timeline if clip goes beyond current bounds
    autoExtendTimeline();

    return clip;
}

// Remove a clip from a track
function removeClipFromTrack(trackId, clipId) {
    if (trackId < 0 || trackId >= state.tracks.length) return false;

    var clips = state.tracks[trackId].clips;
    for (var i = 0; i < clips.length; i++) {
        if (clips[i].id === clipId) {
            clips.splice(i, 1);
            return true;
        }
    }
    return false;
}

// Get clip duration in beats (supports fractional loopCount and offset)
function getClipDurationBeats(clip) {
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return 0;

    var patternBeats;
    if (pattern.type === 'piano') {
        patternBeats = pattern.beats || 4;
    } else {
        var patternLpb = pattern.lpb || state.lpb;
        patternBeats = pattern.steps / patternLpb;
    }
    return patternBeats * clip.loopCount - (clip.offset || 0);
}

// Get the raw pattern length in beats (ignoring loop/offset)
function getPatternBeats(clip) {
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return 0;
    if (pattern.type === 'piano') return pattern.beats || 4;
    var patternLpb = pattern.lpb || state.lpb;
    return pattern.steps / patternLpb;
}

// Get clip end beat
function getClipEndBeat(clip) {
    return clip.startBeat + getClipDurationBeats(clip);
}

// Find all clips active at a given beat position
function getClipsAtBeat(beat) {
    var activeClips = [];
    for (var t = 0; t < state.tracks.length; t++) {
        var track = state.tracks[t];
        for (var c = 0; c < track.clips.length; c++) {
            var clip = track.clips[c];
            if (beat >= clip.startBeat && beat < getClipEndBeat(clip)) {
                activeClips.push({
                    trackId: t,
                    clip: clip,
                    localBeat: beat - clip.startBeat  // Position within clip
                });
            }
        }
    }
    return activeClips;
}

// Convert beat position to step within a pattern (accounting for loops)
// Returns { step, loopCount } for tracking duplicate triggers
function beatToPatternStep(clip, beat) {
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return { step: -1, loopCount: 0 };

    var localBeat = beat - clip.startBeat + (clip.offset || 0);
    if (localBeat < 0) return { step: -1, loopCount: 0 };

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;

    // Calculate which loop iteration we're in
    var loopCount = Math.floor(localBeat / patternBeats);

    // Check if we've exceeded the clip's loopCount (fractional loops)
    var clipDuration = getClipDurationBeats(clip);
    if ((beat - clip.startBeat) >= clipDuration) return { step: -1, loopCount: loopCount };

    // Handle looping: wrap local beat within pattern length
    var loopBeat = localBeat % patternBeats;
    var step = Math.floor(loopBeat * patternLpb);

    return { step: Math.min(step, pattern.steps - 1), loopCount: loopCount };
}

// ============================================
// MEASURE HELPERS
// ============================================

// Get beats per measure based on time signature
function getBeatsPerMeasure() {
    return state.timeSignature.num;
}

// Convert beats to measures
function beatsToMeasures(beats) {
    return Math.ceil(beats / getBeatsPerMeasure());
}

// Convert measures to beats
function measuresToBeats(measures) {
    return measures * getBeatsPerMeasure();
}

// Snap beat position to nearest measure boundary
function snapToMeasure(beat) {
    var beatsPerMeasure = getBeatsPerMeasure();
    return Math.round(beat / beatsPerMeasure) * beatsPerMeasure;
}

// Snap beat position to measure start (floor)
function snapToMeasureStart(beat) {
    var beatsPerMeasure = getBeatsPerMeasure();
    return Math.floor(beat / beatsPerMeasure) * beatsPerMeasure;
}

// Snap beat position to measure end (ceil)
function snapToMeasureEnd(beat) {
    var beatsPerMeasure = getBeatsPerMeasure();
    return Math.ceil(beat / beatsPerMeasure) * beatsPerMeasure;
}

// Get current measure count based on clip positions
function getMeasureCountFromClips() {
    var maxEndBeat = getMaxClipEndBeat();
    if (maxEndBeat === 0) return 4; // Default minimum measures
    return Math.max(4, beatsToMeasures(maxEndBeat) + 2); // Add 2 measures padding
}

// Auto-extend timeline to fit all clips with measure boundary
function autoExtendTimeline() {
    var neededMeasures = getMeasureCountFromClips();
    var neededBeats = measuresToBeats(neededMeasures);

    if (neededBeats > state.timeline.totalBeats) {
        state.timeline.totalBeats = neededBeats;
        state.timeline.totalMeasures = neededMeasures;
        return true; // Timeline was extended
    }
    return false;
}

// Set loop region to measure boundaries
function setLoopRegion(startMeasure, endMeasure) {
    state.timeline.loopStart = measuresToBeats(startMeasure);
    state.timeline.loopEnd = measuresToBeats(endMeasure);
    state.timeline.loopEnabled = true;
}

// Set loop region to match all clips (loop entire arrangement)
function setLoopToArrangement() {
    var maxEndBeat = getMaxClipEndBeat();
    if (maxEndBeat > 0) {
        state.timeline.loopStart = 0;
        state.timeline.loopEnd = snapToMeasureEnd(maxEndBeat);
        state.timeline.loopEnabled = true;
    }
}

// Get the currently selected clip's pattern (DAW-style - editing via clip selection)
function getCurrentPattern() {
    if (!state.selectedClip || state.selectedClip.trackId === null || state.selectedClip.clipId === null) {
        return null;
    }
    var track = state.tracks[state.selectedClip.trackId];
    if (!track) return null;

    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === state.selectedClip.clipId) {
            return state.patterns[track.clips[i].patternId];
        }
    }
    return null;
}

function getCurrentPatternIndex() {
    if (!state.selectedClip || state.selectedClip.trackId === null || state.selectedClip.clipId === null) {
        return -1;
    }
    var track = state.tracks[state.selectedClip.trackId];
    if (!track) return -1;

    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === state.selectedClip.clipId) {
            return track.clips[i].patternId;
        }
    }
    return -1;
}

// ============================================
// TRACK LIST SIDEBAR (DAW-style)
// ============================================

function renderTrackList() {
    var list = document.getElementById('track-list');
    if (!list) return;  // Not using DAW layout yet

    list.innerHTML = '';

    var totalTracks = state.tracks.length;
    var start = state.visibleTrackStart;
    var end = Math.min(start + state.visibleTrackCount, totalTracks);

    for (var i = start; i < end; i++) {
        var track = state.tracks[i];
        if (!track) continue;

        var item = document.createElement('div');
        item.className = 'track-list-item';
        item.setAttribute('data-track-id', i);

        if (i === state.selectedTrack) {
            item.classList.add('selected');
        }
        if (track.muted) {
            item.classList.add('muted');
        }

        var nameSpan = document.createElement('span');
        nameSpan.className = 'track-name';
        nameSpan.textContent = (i + 1) + ': ' + track.name;
        item.appendChild(nameSpan);

        var controls = document.createElement('div');
        controls.className = 'track-controls';

        var muteBtn = document.createElement('button');
        muteBtn.className = 'btn-track-mute' + (track.muted ? ' active' : '');
        muteBtn.setAttribute('data-track-id', i);
        muteBtn.textContent = 'M';
        muteBtn.title = 'Mute';
        controls.appendChild(muteBtn);

        var soloBtn = document.createElement('button');
        soloBtn.className = 'btn-track-solo' + (track.soloed ? ' active' : '');
        soloBtn.setAttribute('data-track-id', i);
        soloBtn.textContent = 'S';
        soloBtn.title = 'Solo';
        controls.appendChild(soloBtn);

        item.appendChild(controls);
        list.appendChild(item);
    }

    // Update range display
    var rangeDisplay = document.getElementById('track-range-display');
    if (rangeDisplay) {
        rangeDisplay.textContent = (start + 1) + '-' + end + ' / ' + totalTracks;
    }
}

function handleTrackListClick(e) {
    var target = e.target;

    if (target.classList.contains('btn-track-mute')) {
        var trackId = parseInt(target.getAttribute('data-track-id'));
        state.tracks[trackId].muted = !state.tracks[trackId].muted;
        target.classList.toggle('active', state.tracks[trackId].muted);
        renderTrackList();
        updateTrackAudibilityVisuals();
        return;
    }

    if (target.classList.contains('btn-track-solo')) {
        var trackId = parseInt(target.getAttribute('data-track-id'));
        state.tracks[trackId].soloed = !state.tracks[trackId].soloed;
        target.classList.toggle('active', state.tracks[trackId].soloed);
        renderTrackList();
        updateTrackAudibilityVisuals();
        return;
    }

    // Click on track item to select
    var item = target.closest('.track-list-item');
    if (item) {
        var trackId = parseInt(item.getAttribute('data-track-id'));
        state.selectedTrack = trackId;
        state.focusedTrack = trackId;
        renderTrackList();
        renderTimeline();
    }
}

function scrollTracksUp() {
    if (state.visibleTrackStart > 0) {
        state.visibleTrackStart = Math.max(0, state.visibleTrackStart - state.visibleTrackCount);
        renderTrackList();
        renderTimeline();
    }
}

function scrollTracksDown() {
    var totalTracks = state.tracks.length;
    if (state.visibleTrackStart + state.visibleTrackCount < totalTracks) {
        state.visibleTrackStart = Math.min(totalTracks - state.visibleTrackCount, state.visibleTrackStart + state.visibleTrackCount);
        renderTrackList();
        renderTimeline();
    }
}

// ============================================
// TIMELINE (DAW-style horizontal clip view)
// ============================================

var timelinePixelsPerBeat = 30;

// Clip clipboard for copy/cut/paste
var clipboardClip = null;

function renderTimeline() {
    var container = document.getElementById('timeline-tracks');
    if (!container) return;

    container.innerHTML = '';

    var start = state.visibleTrackStart;
    var end = Math.min(start + state.visibleTrackCount, state.tracks.length);

    // Auto-extend timeline based on clips (measure-aligned)
    autoExtendTimeline();
    var totalBeats = state.timeline.totalBeats;

    var totalWidth = totalBeats * timelinePixelsPerBeat;

    // Create inner content wrapper that holds the full width (enables scrolling)
    var content = document.createElement('div');
    content.className = 'timeline-content';
    content.style.width = totalWidth + 'px';
    content.style.minWidth = totalWidth + 'px';
    content.style.position = 'relative';

    // Use CSS background for grid lines instead of DOM elements (much faster)
    // Grid lines reflect the current snap resolution
    var beatsPerBar = state.timeSignature.num;
    var barWidth = beatsPerBar * timelinePixelsPerBeat;
    var snapBeats = state.timeline.gridSnap || 1;
    var snapWidth = snapBeats * timelinePixelsPerBeat;

    // Only show snap grid lines if they're at least 3 pixels apart (otherwise too dense)
    if (snapWidth >= 3) {
        content.style.backgroundImage =
            'repeating-linear-gradient(90deg, #0f3460 0px, #0f3460 1px, transparent 1px, transparent ' + snapWidth + 'px),' +
            'repeating-linear-gradient(90deg, #1a5a7a 0px, #1a5a7a 1px, transparent 1px, transparent ' + timelinePixelsPerBeat + 'px),' +
            'repeating-linear-gradient(90deg, #4ecca3 0px, #4ecca3 2px, transparent 2px, transparent ' + barWidth + 'px)';
        content.style.backgroundSize = snapWidth + 'px 100%, ' + timelinePixelsPerBeat + 'px 100%, ' + barWidth + 'px 100%';
    } else {
        // Snap grid too dense, only show beat and bar lines
        content.style.backgroundImage =
            'repeating-linear-gradient(90deg, #0f3460 0px, #0f3460 1px, transparent 1px, transparent ' + timelinePixelsPerBeat + 'px),' +
            'repeating-linear-gradient(90deg, #4ecca3 0px, #4ecca3 2px, transparent 2px, transparent ' + barWidth + 'px)';
        content.style.backgroundSize = timelinePixelsPerBeat + 'px 100%, ' + barWidth + 'px 100%';
    }

    // Render loop region if enabled
    if (state.timeline.loopEnabled) {
        var loopRegion = document.createElement('div');
        loopRegion.className = 'timeline-loop-region';
        loopRegion.style.left = (state.timeline.loopStart * timelinePixelsPerBeat) + 'px';
        loopRegion.style.width = ((state.timeline.loopEnd - state.timeline.loopStart) * timelinePixelsPerBeat) + 'px';
        content.appendChild(loopRegion);

        // Loop start marker (draggable)
        var loopStartMarker = document.createElement('div');
        loopStartMarker.className = 'timeline-loop-start';
        loopStartMarker.id = 'loop-start-marker';
        loopStartMarker.style.left = (state.timeline.loopStart * timelinePixelsPerBeat - 4) + 'px';
        loopStartMarker.title = 'Drag to change loop start (Measure ' + (beatsToMeasures(state.timeline.loopStart) + 1) + ')';
        content.appendChild(loopStartMarker);

        // Loop end marker (draggable)
        var loopEndMarker = document.createElement('div');
        loopEndMarker.className = 'timeline-loop-end';
        loopEndMarker.id = 'loop-end-marker';
        loopEndMarker.style.left = (state.timeline.loopEnd * timelinePixelsPerBeat - 4) + 'px';
        loopEndMarker.title = 'Drag to change loop end (Measure ' + beatsToMeasures(state.timeline.loopEnd) + ')';
        content.appendChild(loopEndMarker);
    }

    // Render track rows
    for (var i = start; i < end; i++) {
        var track = state.tracks[i];
        var row = document.createElement('div');
        row.className = 'timeline-track-row';
        row.setAttribute('data-track-id', i);

        // Render clips on this track
        for (var c = 0; c < track.clips.length; c++) {
            var clip = track.clips[c];
            var clipEl = createClipElement(clip, i);
            row.appendChild(clipEl);
        }

        content.appendChild(row);
    }

    // Render arrangement end marker (snapped to measure boundary after last clip)
    var maxClipEnd = getMaxClipEndBeat();
    var arrangementEnd = maxClipEnd > 0 ? snapToMeasureEnd(maxClipEnd) : measuresToBeats(4);
    var arrangementMarker = document.createElement('div');
    arrangementMarker.className = 'timeline-arrangement-end';
    arrangementMarker.style.left = (arrangementEnd * timelinePixelsPerBeat) + 'px';
    arrangementMarker.title = 'Arrangement end (Measure ' + beatsToMeasures(arrangementEnd) + ')';
    content.appendChild(arrangementMarker);

    // Render song end marker (draggable)
    var endMarker = document.createElement('div');
    endMarker.className = 'timeline-end-marker';
    endMarker.id = 'timeline-end-marker';
    endMarker.style.left = totalWidth + 'px';
    endMarker.title = 'Drag to extend song length';
    content.appendChild(endMarker);

    // Render playhead
    var playhead = document.createElement('div');
    playhead.className = 'timeline-playhead';
    playhead.id = 'timeline-playhead';
    playhead.style.left = (state.currentBeat * timelinePixelsPerBeat) + 'px';
    playhead.style.display = state.isPlaying ? 'block' : 'none';
    content.appendChild(playhead);

    // Add content wrapper to container
    container.appendChild(content);

    // Render ruler
    renderTimelineRuler();

    // Update measure count display
    updateMeasureDisplay();

    // Update timeline scrollbar
    updateTimelineScrollbar();
}

// Get the furthest beat position where any clip ends
function getMaxClipEndBeat() {
    var maxEnd = 0;
    for (var t = 0; t < state.tracks.length; t++) {
        var track = state.tracks[t];
        for (var c = 0; c < track.clips.length; c++) {
            var clip = track.clips[c];
            var clipEnd = clip.startBeat + getClipDurationBeats(clip);
            if (clipEnd > maxEnd) maxEnd = clipEnd;
        }
    }
    return maxEnd;
}

function createClipElement(clip, trackId) {
    var pattern = state.patterns[clip.patternId];
    var duration = getClipDurationBeats(clip);
    var clipWidth = duration * timelinePixelsPerBeat - 2;

    var el = document.createElement('div');
    el.className = 'timeline-clip';
    el.setAttribute('data-clip-id', clip.id);
    el.setAttribute('data-track-id', trackId);
    el.style.left = (clip.startBeat * timelinePixelsPerBeat) + 'px';
    el.style.width = clipWidth + 'px';

    // Color based on pattern type
    if (pattern && pattern.type === 'piano') {
        el.style.background = 'linear-gradient(180deg, #6c63ff 0%, #4a42d4 100%)';
        el.classList.add('piano-clip');
    } else {
        el.style.background = 'linear-gradient(180deg, #4ecca3 0%, #3ba888 100%)';
        el.classList.add('tracker-clip');
    }

    // Clip header with name
    var header = document.createElement('div');
    header.className = 'clip-header';
    var label = pattern ? pattern.name : 'Pattern ' + (clip.patternId + 1);
    if (clip.loopCount > 1) {
        label += ' ×' + clip.loopCount;
    }
    header.textContent = label;
    el.appendChild(header);

    // Note visualization canvas
    var noteViz = document.createElement('canvas');
    noteViz.className = 'clip-note-viz';
    noteViz.width = Math.max(clipWidth, 1);
    noteViz.height = 40;
    el.appendChild(noteViz);

    // Render note data to canvas
    if (pattern && pattern.data) {
        renderClipNotes(noteViz, pattern, clip.loopCount);
    }

    // Loop handle (top-left) - changes loop count
    var loopHandle = document.createElement('div');
    loopHandle.className = 'clip-loop-handle';
    loopHandle.title = 'Drag to change loop count';
    loopHandle.innerHTML = '⟳';
    el.appendChild(loopHandle);

    // Expand handle (mid-left) - changes pattern steps
    var expandHandle = document.createElement('div');
    expandHandle.className = 'clip-expand-handle';
    expandHandle.title = 'Drag to resize pattern (change steps)';
    expandHandle.innerHTML = '⇔';
    el.appendChild(expandHandle);

    // Right resize handle for loop count (drag edge)
    var resizeHandle = document.createElement('div');
    resizeHandle.className = 'clip-resize-handle';
    resizeHandle.title = 'Drag to change loop count';
    el.appendChild(resizeHandle);

    // Split handle (shows on hover at loop boundaries)
    var splitHandle = document.createElement('div');
    splitHandle.className = 'clip-split-handle';
    splitHandle.title = 'Click to split clip here';
    splitHandle.innerHTML = '✂';
    splitHandle.style.display = 'none';
    el.appendChild(splitHandle);

    // Show split handle on hover at grid snap positions
    if (pattern) {
        el.addEventListener('mousemove', function(e) {
            if (clipDragState.active) {
                splitHandle.style.display = 'none';
                return;
            }

            var rect = el.getBoundingClientRect();
            var x = e.clientX - rect.left;
            var clipBeats = getClipDurationBeats(clip);
            if (clipBeats <= 0) return;
            var pixelsPerBeat = clipWidth / clipBeats;
            var gridSnap = state.timeline.gridSnap || 1;
            var gridPixels = gridSnap * pixelsPerBeat;

            // Only show if grid snap markers are far enough apart
            if (gridPixels < 6) {
                splitHandle.style.display = 'none';
                return;
            }

            // Find nearest grid snap position
            var beatInClip = x / pixelsPerBeat;
            var snappedBeat = Math.round(beatInClip / gridSnap) * gridSnap;
            var snappedX = snappedBeat * pixelsPerBeat;

            // Show if near a grid line (within 8px) and not at clip edges
            if (Math.abs(x - snappedX) < 8 && snappedBeat > 0.001 && snappedBeat < clipBeats - 0.001) {
                splitHandle.style.display = 'flex';
                splitHandle.style.left = (snappedX - 10) + 'px';
                splitHandle.setAttribute('data-split-beat', clip.startBeat + snappedBeat);
                return;
            }

            splitHandle.style.display = 'none';
        });

        el.addEventListener('mouseleave', function() {
            splitHandle.style.display = 'none';
        });
    }

    return el;
}

// Render note visualization on clip canvas
function renderClipNotes(canvas, pattern, loopCount) {
    var ctx = canvas.getContext('2d');
    var width = canvas.width;
    var height = canvas.height;

    ctx.clearRect(0, 0, width, height);

    if (!pattern.data || pattern.steps === 0) return;

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;
    var totalBeats = patternBeats * loopCount;
    var pixelsPerBeat = width / totalBeats;

    // Find note range for scaling
    var minNote = 127, maxNote = 0;
    var notes = [];

    for (var step = 0; step < pattern.steps; step++) {
        var stepData = pattern.data[step];
        if (!stepData || !stepData.columns) continue;

        for (var nc = 0; nc < stepData.columns.length; nc++) {
            var colData = stepData.columns[nc];
            if (!colData || !colData.note || colData.note === '' || colData.note === NOTE_OFF) continue;

            var midiNote = noteNameToMidi(colData.note);
            if (midiNote !== null) {
                minNote = Math.min(minNote, midiNote);
                maxNote = Math.max(maxNote, midiNote);

                // Find duration (until next note or note-off in same column)
                var durationSteps = 1;
                for (var s = step + 1; s < pattern.steps; s++) {
                    var sd = pattern.data[s];
                    if (sd && sd.columns && sd.columns[nc]) {
                        var cd = sd.columns[nc];
                        if (cd.note && cd.note !== '') {
                            break;
                        }
                    }
                    durationSteps++;
                }

                notes.push({
                    step: step,
                    note: midiNote,
                    duration: durationSteps,
                    noteCol: nc
                });
            }
        }
    }

    if (notes.length === 0) return;

    // Add some padding to note range
    var noteRange = Math.max(maxNote - minNote, 12);
    var noteCenter = (maxNote + minNote) / 2;
    minNote = Math.floor(noteCenter - noteRange / 2);
    maxNote = Math.ceil(noteCenter + noteRange / 2);

    // Draw notes for each loop
    ctx.fillStyle = 'rgba(255, 255, 255, 0.8)';

    for (var loop = 0; loop < loopCount; loop++) {
        var loopOffset = loop * patternBeats;

        for (var i = 0; i < notes.length; i++) {
            var n = notes[i];
            var stepBeat = n.step / patternLpb;
            var x = (loopOffset + stepBeat) * pixelsPerBeat;
            var w = Math.max((n.duration / patternLpb) * pixelsPerBeat - 1, 2);
            var y = height - ((n.note - minNote) / (maxNote - minNote)) * (height - 4) - 2;
            var h = Math.max(2, (height - 4) / noteRange);

            ctx.fillRect(x, y, w, h);
        }

        // Draw loop separator line
        if (loop > 0) {
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.3)';
            ctx.beginPath();
            ctx.moveTo(loopOffset * pixelsPerBeat, 0);
            ctx.lineTo(loopOffset * pixelsPerBeat, height);
            ctx.stroke();
        }
    }
}

// Convert note name to MIDI number
function noteNameToMidi(noteName) {
    if (!noteName || noteName === '' || noteName === NOTE_OFF) return null;

    var noteMap = { 'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11 };
    var match = noteName.match(/^([A-G])([#b]?)(\d+)$/i);
    if (!match) return null;

    var note = noteMap[match[1].toUpperCase()];
    if (note === undefined) return null;

    if (match[2] === '#') note++;
    else if (match[2] === 'b') note--;

    var octave = parseInt(match[3]);
    return note + (octave + 1) * 12;
}

// Zoom timeline by factor, optionally centered on a mouse X position
function zoomTimeline(factor, mouseX) {
    var timelineTracks = document.getElementById('timeline-tracks');
    if (!timelineTracks) return;

    var oldZoom = timelinePixelsPerBeat;
    // Allow zooming from 5 (zoomed out) to 500 (zoomed in to see 128th/256th notes)
    timelinePixelsPerBeat = Math.max(5, Math.min(500, timelinePixelsPerBeat * factor));

    // Adjust scroll position to zoom towards mouse position
    if (mouseX !== undefined) {
        var rect = timelineTracks.getBoundingClientRect();
        var scrollX = timelineTracks.scrollLeft;
        var relativeX = mouseX - rect.left + scrollX;
        var beatAtMouse = relativeX / oldZoom;
        var newX = beatAtMouse * timelinePixelsPerBeat;
        timelineTracks.scrollLeft = newX - (mouseX - rect.left);
    }

    renderTimeline();
    renderTimelineRuler();
}

function renderTimelineRuler() {
    var ruler = document.getElementById('timeline-ruler');
    if (!ruler) return;

    var totalWidth = state.timeline.totalBeats * timelinePixelsPerBeat;
    var beatsPerBar = state.timeSignature.num;

    ruler.innerHTML = '';
    ruler.style.position = 'relative';
    ruler.style.width = totalWidth + 'px';
    ruler.style.minWidth = totalWidth + 'px';

    // Calculate visible range based on scroll position
    var container = document.getElementById('timeline-tracks');
    var scrollLeft = container ? container.scrollLeft : 0;
    var viewWidth = container ? container.clientWidth : 1000;

    var startBeat = Math.max(0, Math.floor(scrollLeft / timelinePixelsPerBeat) - beatsPerBar);
    var endBeat = Math.min(state.timeline.totalBeats, Math.ceil((scrollLeft + viewWidth) / timelinePixelsPerBeat) + beatsPerBar);

    // Determine finest subdivision to show based on zoom level (min ~20px between labels)
    // Each level is a subdivision of a beat
    var subdivisions = [
        { div: 1/64, label: '/256' },   // 256th notes (1/64 of a beat in 4/4)
        { div: 1/32, label: '/128' },   // 128th notes
        { div: 1/16, label: '/64' },    // 64th notes
        { div: 1/8,  label: '/32' },    // 32nd notes
        { div: 1/4,  label: '/16' },    // 16th notes
        { div: 1/2,  label: '/8' },     // 8th notes
        { div: 1,    label: '' },       // quarter notes (beats)
    ];

    // Find finest subdivision where markers are at least 20px apart
    var subDiv = 1; // default to beats
    var subLabel = '';
    for (var s = 0; s < subdivisions.length; s++) {
        var pxApart = subdivisions[s].div * timelinePixelsPerBeat;
        if (pxApart >= 20) {
            subDiv = subdivisions[s].div;
            subLabel = subdivisions[s].label;
            break;
        }
    }

    // Render markers at subdivision resolution within visible range
    var stepSize = subDiv;
    var snapStart = Math.floor(startBeat / stepSize) * stepSize;

    // Cap marker count to avoid performance issues
    var maxMarkers = Math.ceil(viewWidth / 15) + 20;
    var markerCount = 0;

    for (var pos = snapStart; pos <= endBeat && markerCount < maxMarkers; pos += stepSize) {
        // Round to avoid floating point errors
        var beatPos = Math.round(pos * 10000) / 10000;
        if (beatPos < 0) continue;

        var xPos = beatPos * timelinePixelsPerBeat;
        var marker = document.createElement('span');
        marker.style.position = 'absolute';
        marker.style.left = xPos + 'px';

        var isBar = (Math.abs(beatPos % beatsPerBar) < 0.0001) || (Math.abs(beatPos % beatsPerBar - beatsPerBar) < 0.0001);
        var isBeat = (Math.abs(beatPos % 1) < 0.0001) || (Math.abs(beatPos % 1 - 1) < 0.0001);

        if (isBar) {
            var bar = Math.floor(beatPos / beatsPerBar) + 1;
            marker.className = 'bar-marker';
            marker.textContent = bar;
        } else if (isBeat) {
            var beatInBar = Math.round(beatPos % beatsPerBar) + 1;
            marker.className = 'beat-marker';
            marker.textContent = '·' + beatInBar;
        } else {
            // Sub-beat marker - show as tick
            marker.className = 'sub-marker';
            marker.textContent = '·';
        }

        ruler.appendChild(marker);
        markerCount++;
    }
}

// Update ruler when scrolling (render visible bar numbers)
function updateRulerOnScroll() {
    renderTimelineRuler();
}

// Update measure count display in UI
function updateMeasureDisplay() {
    var maxClipEnd = getMaxClipEndBeat();
    var usedMeasures = maxClipEnd > 0 ? beatsToMeasures(maxClipEnd) : 0;
    var totalMeasures = beatsToMeasures(state.timeline.totalBeats);

    // Update track range display to show measure info
    var displayEl = document.getElementById('track-range-display');
    if (displayEl) {
        var trackStart = state.visibleTrackStart + 1;
        var trackEnd = Math.min(state.visibleTrackStart + state.visibleTrackCount, state.tracks.length);
        displayEl.textContent = trackStart + '-' + trackEnd + ' / ' + state.tracks.length + ' | M:' + usedMeasures + '/' + totalMeasures;
    }
}

// Toggle loop region on/off
function toggleLoopRegion() {
    if (state.timeline.loopEnabled) {
        state.timeline.loopEnabled = false;
        consoleLog('Loop disabled');
    } else {
        // Set loop to arrangement bounds
        setLoopToArrangement();
        consoleLog('Loop enabled: ' + beatsToMeasures(state.timeline.loopStart) + ' - ' + beatsToMeasures(state.timeline.loopEnd) + ' measures');
    }
    renderTimeline();
}

// Toggle snap to measure
function toggleSnapToMeasure() {
    state.timeline.snapToMeasure = !state.timeline.snapToMeasure;
    consoleLog('Snap to measure: ' + (state.timeline.snapToMeasure ? 'ON' : 'OFF'));
}

// Update loop button visual state
function updateLoopButton() {
    var btn = document.getElementById('btn-loop');
    if (btn) {
        btn.classList.toggle('active', state.timeline.loopEnabled);
    }
}

// Update snap button visual state
function updateSnapButton() {
    var btn = document.getElementById('btn-snap');
    if (btn) {
        btn.classList.toggle('active', state.timeline.snapToMeasure);
    }
}

// Update timeline position display to show current scroll position and song length
function updateTimelineScrollbar() {
    var positionDisplay = document.getElementById('timeline-position-display');
    var timelineTracks = document.getElementById('timeline-tracks');

    if (!positionDisplay || !timelineTracks) return;

    var currentBeat = timelineTracks.scrollLeft / timelinePixelsPerBeat;
    var totalBeats = state.timeline.totalBeats;
    var arrangementEnd = getMaxClipEndBeat();
    if (arrangementEnd > 0) {
        totalBeats = snapToMeasureEnd(arrangementEnd);
    }

    // Convert beats to time (MM:SS) based on BPM
    var currentTime = (currentBeat / state.bpm) * 60;
    var totalTime = (totalBeats / state.bpm) * 60;

    var currentMin = Math.floor(currentTime / 60);
    var currentSec = Math.floor(currentTime % 60);
    var totalMin = Math.floor(totalTime / 60);
    var totalSec = Math.floor(totalTime % 60);

    // Also show measure info
    var currentMeasure = Math.floor(currentBeat / getBeatsPerMeasure()) + 1;
    var totalMeasures = beatsToMeasures(totalBeats);

    positionDisplay.textContent = currentMin + ':' + (currentSec < 10 ? '0' : '') + currentSec +
        ' / ' + totalMin + ':' + (totalSec < 10 ? '0' : '') + totalSec +
        ' | M' + currentMeasure + '/' + totalMeasures;
}

function handleTimelineClick(e) {
    var target = e.target;

    // Hide context menu on click
    hideTimelineContextMenu();

    // Click on split handle
    if (target.classList.contains('clip-split-handle')) {
        e.stopPropagation();
        var clipEl = target.closest('.timeline-clip');
        if (clipEl) {
            var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
            var trackId = parseInt(clipEl.getAttribute('data-track-id'));
            var splitBeat = parseFloat(target.getAttribute('data-split-beat'));
            if (!isNaN(splitBeat)) {
                splitClipAtBeat(trackId, clipId, splitBeat);
            }
        }
        return;
    }

    // Click on clip or its children (except handles)
    var clipEl = target.closest('.timeline-clip');
    if (clipEl && !target.classList.contains('clip-loop-handle') &&
        !target.classList.contains('clip-expand-handle') &&
        !target.classList.contains('clip-resize-handle')) {
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));
        selectClip(trackId, clipId);
        return;
    }

    // Click on empty track row - just select the track
    var row = target.closest('.timeline-track-row');
    if (row) {
        var trackId = parseInt(row.getAttribute('data-track-id'));
        state.selectedTrack = trackId;
        state.focusedTrack = trackId;
        renderTrackList();
    }
}

// Split a clip at a specific beat
function splitClipAtBeat(trackId, clipId, splitBeat) {
    var track = state.tracks[trackId];
    if (!track) return;

    var clip = null;
    var clipIndex = -1;
    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipId) {
            clip = track.clips[i];
            clipIndex = i;
            break;
        }
    }

    if (!clip) return;

    var pattern = state.patterns[clip.patternId];
    if (!pattern) return;

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;

    // Calculate split position within clip
    var localBeat = splitBeat - clip.startBeat;
    var clipDuration = getClipDurationBeats(clip);
    if (localBeat <= 0.001 || localBeat >= clipDuration - 0.001) return;

    // Calculate where in the looped pattern the split falls
    var beatInPattern = ((clip.offset || 0) + localBeat) % patternBeats;
    var totalBeatFromStart = (clip.offset || 0) + localBeat;

    // New clip: starts at splitBeat, offset into pattern, remaining duration
    var newOffset = totalBeatFromStart % patternBeats;
    var remainingDuration = clipDuration - localBeat;
    var newLoopCount = (remainingDuration + newOffset) / patternBeats;

    var newClip = {
        id: Date.now() + Math.random(),
        patternId: clip.patternId,
        startBeat: splitBeat,
        loopCount: newLoopCount,
        offset: newOffset
    };

    // Shrink original clip to end at split point
    var originalDuration = localBeat;
    clip.loopCount = (originalDuration + (clip.offset || 0)) / patternBeats;

    track.clips.push(newClip);

    renderTimeline();
    consoleLog('Split clip at beat ' + splitBeat.toFixed(2));
}

// Timeline right-click context menu
var timelineContextState = {
    trackId: 0,
    beat: 0,
    clipId: null
};

function handleTimelineContextMenu(e) {
    e.preventDefault();

    var target = e.target;
    var menu = document.getElementById('timeline-context-menu');
    if (!menu) return;

    // Get track and beat from click position
    var row = target.closest('.timeline-track-row');
    if (row) {
        timelineContextState.trackId = parseInt(row.getAttribute('data-track-id'));
        var rect = row.getBoundingClientRect();
        timelineContextState.beat = Math.floor((e.clientX - rect.left) / timelinePixelsPerBeat);
    }

    // Check if clicking on a clip
    if (target.classList.contains('timeline-clip')) {
        timelineContextState.clipId = parseFloat(target.getAttribute('data-clip-id'));
        menu.querySelector('[data-action="delete-clip"]').style.display = 'block';
    } else {
        timelineContextState.clipId = null;
        menu.querySelector('[data-action="delete-clip"]').style.display = 'none';
    }

    // Position and show menu
    menu.style.left = e.clientX + 'px';
    menu.style.top = e.clientY + 'px';
    menu.style.display = 'block';
}

function hideTimelineContextMenu() {
    var menu = document.getElementById('timeline-context-menu');
    if (menu) menu.style.display = 'none';
}

function handleTimelineContextAction(action) {
    hideTimelineContextMenu();

    switch (action) {
        case 'add-pattern':
            addPatternToTrack(timelineContextState.trackId, timelineContextState.beat);
            break;
        case 'copy-clip':
            if (timelineContextState.clipId !== null) {
                state.selectedClip = { trackId: timelineContextState.trackId, clipId: timelineContextState.clipId };
                copyClip();
            }
            break;
        case 'cut-clip':
            if (timelineContextState.clipId !== null) {
                state.selectedClip = { trackId: timelineContextState.trackId, clipId: timelineContextState.clipId };
                cutClip();
            }
            break;
        case 'paste-clip':
            pasteClip(timelineContextState.trackId, timelineContextState.beat);
            break;
        case 'delete-clip':
            if (timelineContextState.clipId !== null) {
                removeClipFromTrack(timelineContextState.trackId, timelineContextState.clipId);
                renderTimeline();
                consoleLog('Deleted clip');
            }
            break;
    }
}

function addPatternToTrack(trackId, beat) {
    // Create a new tracker pattern with default 16 steps
    var stepsInput = document.getElementById('pattern-steps');
    var lpbInput = document.getElementById('pattern-lpb');
    var steps = stepsInput ? parseInt(stepsInput.value) || 16 : 16;
    var lpb = lpbInput ? parseInt(lpbInput.value) || state.lpb : state.lpb;

    var pattern = createTrackerPattern(steps, lpb, trackId);
    state.patterns.push(pattern);
    var patternId = state.patterns.length - 1;

    // Add clip to track
    var clip = addClipToTrack(trackId, patternId, beat, 1);
    if (clip) {
        renderTimeline();
        selectClip(trackId, clip.id);
        consoleLog('Added pattern to track ' + (trackId + 1));
    }
}

function selectClip(trackId, clipId) {
    // Deselect all clips
    document.querySelectorAll('.timeline-clip.selected').forEach(function(el) {
        el.classList.remove('selected');
    });

    // Select this clip
    var clipEl = document.querySelector('.timeline-clip[data-clip-id="' + clipId + '"]');
    if (clipEl) {
        clipEl.classList.add('selected');
    }

    // Update selected clip state (DAW-style - this is how we edit patterns)
    state.selectedClip = { trackId: trackId, clipId: clipId };
    state.selectedTrack = trackId;
    state.focusedTrack = trackId;

    // Find the clip and its pattern
    var track = state.tracks[trackId];
    var clip = null;
    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipId) {
            clip = track.clips[i];
            break;
        }
    }

    if (clip) {
        var pattern = state.patterns[clip.patternId];
        if (pattern) {
            // Update pattern title display
            updatePatternPianoTitle(trackId, pattern);
            switchEditorView('pattern');
            renderTrackerGrid(true);
        }
    }

    renderTrackList();
}

function updatePatternPianoTitle(trackId, pattern) {
    var titleEl = document.getElementById('pattern-editor-title');
    if (titleEl) {
        titleEl.textContent = 'Pattern: ' + (pattern.name || 'Untitled') + ' (Track ' + (trackId + 1) + ')';
    }

    // Update pattern controls
    var stepsInput = document.getElementById('pattern-steps');
    var lpbInput = document.getElementById('pattern-lpb');

    if (stepsInput) {
        stepsInput.value = pattern.steps || 16;
    }
    if (lpbInput) {
        lpbInput.value = pattern.lpb || state.lpb;
    }
}

function updateTimelinePlayhead() {
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) {
        playhead.style.left = (state.currentBeat * timelinePixelsPerBeat) + 'px';
    }

    // Update position display during playback
    var positionDisplay = document.getElementById('timeline-position-display');
    if (positionDisplay && state.isPlaying) {
        var currentBeat = state.currentBeat;
        var totalBeats = state.timeline.loopEnabled ? state.timeline.loopEnd : getMaxClipEndBeat();
        if (totalBeats <= 0) totalBeats = state.timeline.totalBeats;

        // Convert beats to time (MM:SS) based on BPM
        var currentTime = (currentBeat / state.bpm) * 60;
        var totalTime = (totalBeats / state.bpm) * 60;

        var currentMin = Math.floor(currentTime / 60);
        var currentSec = Math.floor(currentTime % 60);
        var totalMin = Math.floor(totalTime / 60);
        var totalSec = Math.floor(totalTime % 60);

        // Also show measure info
        var currentMeasure = Math.floor(currentBeat / getBeatsPerMeasure()) + 1;
        var totalMeasures = beatsToMeasures(totalBeats);

        positionDisplay.textContent = currentMin + ':' + (currentSec < 10 ? '0' : '') + currentSec +
            ' / ' + totalMin + ':' + (totalSec < 10 ? '0' : '') + totalSec +
            ' | M' + currentMeasure + '/' + totalMeasures;
    }
}

// ============================================
// CLIP DRAGGING AND RESIZING
// ============================================

var clipDragState = {
    active: false,
    mode: null,       // 'move', 'resize', or 'end-marker'
    clipId: null,
    trackId: null,
    startX: 0,
    startBeat: 0,
    startLoopCount: 1,
    clipElement: null,
    startTotalBeats: 0
};

function handleTimelineMouseDown(e) {
    var target = e.target;

    // Check if clicking on song end marker
    if (target.classList.contains('timeline-end-marker')) {
        e.preventDefault();
        clipDragState.active = true;
        clipDragState.mode = 'end-marker';
        clipDragState.startX = e.clientX;
        clipDragState.startTotalBeats = state.timeline.totalBeats;
        clipDragState.clipElement = target;
        document.body.style.cursor = 'ew-resize';
        return;
    }

    // Check if clicking on loop start marker
    if (target.classList.contains('timeline-loop-start')) {
        e.preventDefault();
        clipDragState.active = true;
        clipDragState.mode = 'loop-start';
        clipDragState.startX = e.clientX;
        clipDragState.startBeat = state.timeline.loopStart;
        clipDragState.clipElement = target;
        document.body.style.cursor = 'ew-resize';
        return;
    }

    // Check if clicking on loop end marker
    if (target.classList.contains('timeline-loop-end')) {
        e.preventDefault();
        clipDragState.active = true;
        clipDragState.mode = 'loop-end';
        clipDragState.startX = e.clientX;
        clipDragState.startBeat = state.timeline.loopEnd;
        clipDragState.clipElement = target;
        document.body.style.cursor = 'ew-resize';
        return;
    }

    // Check if clicking on resize handle (right edge)
    if (target.classList.contains('clip-resize-handle') || target.classList.contains('clip-handle')) {
        e.preventDefault();
        var clipEl = target.closest('.timeline-clip');
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));

        var track = state.tracks[trackId];
        var clip = null;
        for (var i = 0; i < track.clips.length; i++) {
            if (track.clips[i].id === clipId) {
                clip = track.clips[i];
                break;
            }
        }

        if (clip) {
            clipDragState.active = true;
            clipDragState.mode = 'resize';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.startX = e.clientX;
            clipDragState.startLoopCount = clip.loopCount;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'ew-resize';
        }
        return;
    }

    // Check if clicking on loop handle (top-left)
    if (target.classList.contains('clip-loop-handle')) {
        e.preventDefault();
        var clipEl = target.closest('.timeline-clip');
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));

        var track = state.tracks[trackId];
        var clip = null;
        for (var i = 0; i < track.clips.length; i++) {
            if (track.clips[i].id === clipId) {
                clip = track.clips[i];
                break;
            }
        }

        if (clip) {
            clipDragState.active = true;
            clipDragState.mode = 'loop-handle';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.startX = e.clientX;
            clipDragState.startLoopCount = clip.loopCount;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'ew-resize';
        }
        return;
    }

    // Check if clicking on expand handle (mid-left) - changes pattern steps
    if (target.classList.contains('clip-expand-handle')) {
        e.preventDefault();
        var clipEl = target.closest('.timeline-clip');
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));

        var track = state.tracks[trackId];
        var clip = null;
        for (var i = 0; i < track.clips.length; i++) {
            if (track.clips[i].id === clipId) {
                clip = track.clips[i];
                break;
            }
        }

        if (clip) {
            var pattern = state.patterns[clip.patternId];
            clipDragState.active = true;
            clipDragState.mode = 'expand';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.startX = e.clientX;
            clipDragState.startSteps = pattern ? pattern.steps : 16;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'ew-resize';
        }
        return;
    }

    // Check if clicking on clip (for dragging) - but not on handles
    var clipEl = target.closest('.timeline-clip');
    if (clipEl && !target.classList.contains('clip-loop-handle') &&
        !target.classList.contains('clip-expand-handle') &&
        !target.classList.contains('clip-resize-handle') &&
        !target.classList.contains('clip-split-handle')) {
        e.preventDefault();
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));

        var track = state.tracks[trackId];
        var clip = null;
        for (var i = 0; i < track.clips.length; i++) {
            if (track.clips[i].id === clipId) {
                clip = track.clips[i];
                break;
            }
        }

        if (clip) {
            clipDragState.active = true;
            clipDragState.mode = 'move';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.startX = e.clientX;
            clipDragState.startBeat = clip.startBeat;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'grabbing';

            // Select clip and show its pattern in the editor
            selectClip(trackId, clipId);
        }
    }
}

// Copy selected clip to clipboard
function copyClip() {
    if (!state.selectedClip || state.selectedClip.clipId === null) {
        consoleLog('No clip selected to copy');
        return;
    }

    var track = state.tracks[state.selectedClip.trackId];
    if (!track) return;

    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === state.selectedClip.clipId) {
            clipboardClip = JSON.parse(JSON.stringify(track.clips[i]));
            clipboardClip.sourceTrackId = state.selectedClip.trackId;
            consoleLog('Copied clip');
            return;
        }
    }
}

// Cut selected clip (copy and delete)
function cutClip() {
    if (!state.selectedClip || state.selectedClip.clipId === null) {
        consoleLog('No clip selected to cut');
        return;
    }

    copyClip();
    removeClipFromTrack(state.selectedClip.trackId, state.selectedClip.clipId);
    state.selectedClip = null;
    renderTimeline();
    consoleLog('Cut clip');
}

// Paste clip at current position
function pasteClip(targetTrackId, targetBeat) {
    if (!clipboardClip) {
        consoleLog('No clip in clipboard');
        return;
    }

    var startBeat = targetBeat !== undefined ? targetBeat : clipboardClip.startBeat;

    // Snap to measure if enabled
    if (state.timeline.snapToMeasure) {
        startBeat = snapToMeasureStart(startBeat);
    }

    var newClip = {
        id: Date.now() + Math.random(),
        patternId: clipboardClip.patternId,
        startBeat: startBeat,
        loopCount: clipboardClip.loopCount
    };

    var trackId = targetTrackId !== undefined ? targetTrackId : state.selectedTrack;
    state.tracks[trackId].clips.push(newClip);

    // Auto-extend timeline if needed
    autoExtendTimeline();

    renderTimeline();
    consoleLog('Pasted clip to track ' + (trackId + 1));
}

function handleTimelineMouseMove(e) {
    if (!clipDragState.active) return;

    var deltaX = e.clientX - clipDragState.startX;
    var deltaBeat = deltaX / timelinePixelsPerBeat;

    // Handle end marker dragging (snapped to measures)
    if (clipDragState.mode === 'end-marker') {
        var newTotalBeats = Math.max(16, Math.round(clipDragState.startTotalBeats + deltaBeat));

        // Snap to measure boundary
        newTotalBeats = snapToMeasureEnd(newTotalBeats);

        // Ensure it's beyond the furthest clip
        var minBeats = snapToMeasureEnd(getMaxClipEndBeat()) + getBeatsPerMeasure();
        newTotalBeats = Math.max(minBeats, newTotalBeats);

        state.timeline.totalBeats = newTotalBeats;
        state.timeline.totalMeasures = beatsToMeasures(newTotalBeats);
        clipDragState.clipElement.style.left = (newTotalBeats * timelinePixelsPerBeat) + 'px';
        updateMeasureDisplay();
        return;
    }

    // Handle loop start marker dragging
    if (clipDragState.mode === 'loop-start') {
        var newStart = Math.max(0, Math.round(clipDragState.startBeat + deltaBeat));

        // Snap to measure boundary
        newStart = snapToMeasureStart(newStart);

        // Ensure start is before end (leave at least 1 measure)
        var minEnd = newStart + getBeatsPerMeasure();
        if (minEnd > state.timeline.loopEnd) {
            newStart = state.timeline.loopEnd - getBeatsPerMeasure();
        }

        state.timeline.loopStart = Math.max(0, newStart);
        renderTimeline();
        return;
    }

    // Handle loop end marker dragging
    if (clipDragState.mode === 'loop-end') {
        var newEnd = Math.max(getBeatsPerMeasure(), Math.round(clipDragState.startBeat + deltaBeat));

        // Snap to measure boundary
        newEnd = snapToMeasureEnd(newEnd);

        // Ensure end is after start (leave at least 1 measure)
        var minEnd = state.timeline.loopStart + getBeatsPerMeasure();
        if (newEnd < minEnd) {
            newEnd = minEnd;
        }

        state.timeline.loopEnd = newEnd;
        renderTimeline();
        return;
    }

    var track = state.tracks[clipDragState.trackId];
    var clip = null;
    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipDragState.clipId) {
            clip = track.clips[i];
            break;
        }
    }

    if (!clip) return;

    if (clipDragState.mode === 'move') {
        // Move clip position (with optional measure snapping)
        var newBeat = Math.max(0, Math.round(clipDragState.startBeat + deltaBeat));

        // Snap to measure if enabled
        if (state.timeline.snapToMeasure) {
            newBeat = snapToMeasureStart(newBeat);
        }

        clip.startBeat = newBeat;
        clipDragState.clipElement.style.left = (newBeat * timelinePixelsPerBeat) + 'px';

        // Auto-extend timeline if clip moved beyond bounds
        autoExtendTimeline();
    } else if (clipDragState.mode === 'resize') {
        // Resize (change loop count)
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        // Calculate pattern length in beats
        var patternLpb = pattern.lpb || state.lpb;
        var patternBeats = pattern.steps / patternLpb;

        // Calculate new loop count based on drag distance
        var loopsChange = deltaBeat / patternBeats;
        var newLoopCount = Math.max(1, Math.round(clipDragState.startLoopCount + loopsChange));

        clip.loopCount = newLoopCount;

        // Update visual width
        var duration = getClipDurationBeats(clip);
        clipDragState.clipElement.style.width = (duration * timelinePixelsPerBeat - 2) + 'px';

        // Update label in header
        var label = pattern.name || ('Pattern ' + (clip.patternId + 1));
        if (newLoopCount > 1) {
            label += ' ×' + newLoopCount;
        }
        var header = clipDragState.clipElement.querySelector('.clip-header');
        if (header) {
            header.textContent = label;
        }

        // Auto-extend timeline if clip resized beyond bounds
        autoExtendTimeline();
    } else if (clipDragState.mode === 'loop-handle') {
        // Resize clip to any grid snap position (fractional loops)
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        var patternLpb = pattern.lpb || state.lpb;
        var patternBeats = pattern.steps / patternLpb;
        var gridSnap = state.timeline.gridSnap || 1;

        // Calculate new total duration snapped to grid
        var oldDuration = patternBeats * clipDragState.startLoopCount - (clip.offset || 0);
        var newDuration = oldDuration + deltaBeat;
        // Snap duration to grid
        newDuration = Math.max(gridSnap, Math.round(newDuration / gridSnap) * gridSnap);
        // Convert back to loopCount (accounting for offset)
        var newLoopCount = (newDuration + (clip.offset || 0)) / patternBeats;
        // Minimum: enough to fill at least one grid snap beyond offset
        newLoopCount = Math.max((clip.offset || 0) / patternBeats + gridSnap / patternBeats, newLoopCount);

        clip.loopCount = newLoopCount;

        // Update visual width
        var duration = getClipDurationBeats(clip);
        clipDragState.clipElement.style.width = (duration * timelinePixelsPerBeat - 2) + 'px';

        // Update label in header
        var label = pattern.name || ('Pattern ' + (clip.patternId + 1));
        if (newLoopCount > 1) {
            var displayLoops = Math.round(newLoopCount * 100) / 100;
            label += ' ×' + displayLoops;
        }
        var header = clipDragState.clipElement.querySelector('.clip-header');
        if (header) {
            header.textContent = label;
        }

        autoExtendTimeline();
    } else if (clipDragState.mode === 'expand') {
        // Change pattern steps (expand/contract pattern)
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        var patternLpb = pattern.lpb || state.lpb;

        // Calculate step change based on grid snap
        var gridSnap = state.timeline.gridSnap || 1;
        var stepChange = Math.round(deltaBeat / gridSnap) * (patternLpb * gridSnap);
        var newSteps = Math.max(patternLpb, clipDragState.startSteps + stepChange);

        // Update pattern steps
        pattern.steps = newSteps;

        // Ensure pattern data array is correct size
        while (pattern.data.length < newSteps) {
            pattern.data.push({ columns: [] });
        }

        // Update visual width
        var duration = getClipDurationBeats(clip);
        clipDragState.clipElement.style.width = (duration * timelinePixelsPerBeat - 2) + 'px';

        // Update note visualization canvas
        var canvas = clipDragState.clipElement.querySelector('.clip-note-viz');
        if (canvas) {
            canvas.width = Math.max(duration * timelinePixelsPerBeat - 2, 1);
            renderClipNotes(canvas, pattern, clip.loopCount);
        }

        // Update pattern steps input if visible
        var stepsInput = document.getElementById('pattern-steps');
        if (stepsInput && state.selectedClip && state.selectedClip.clipId === clip.id) {
            stepsInput.value = newSteps;
        }

        autoExtendTimeline();
    }
}

function handleTimelineMouseUp(e) {
    if (clipDragState.active) {
        clipDragState.active = false;
        clipDragState.mode = null;
        clipDragState.clipElement = null;
        document.body.style.cursor = '';
        renderTimeline();  // Re-render to ensure proper state
    }
}

// ============================================
// SEQUENCE SIDEBAR (Removed - DAW uses clips only)
// ============================================

function renderSequenceSidebar() {
    // No-op - DAW layout uses clips on timeline, not sequence sidebar
}

// Handle double-click on timeline to add/edit clips
function handleTimelineDblClick(e) {
    var target = e.target;

    // Double-click on clip opens pattern in step sequencer
    if (target.classList.contains('timeline-clip')) {
        var clipId = parseFloat(target.getAttribute('data-clip-id'));
        var trackId = parseInt(target.getAttribute('data-track-id'));
        openClipInEditor(trackId, clipId);
        return;
    }

    // Double-click on empty track row to create new clip with NEW pattern
    var row = target.closest('.timeline-track-row');
    if (row) {
        var trackId = parseInt(row.getAttribute('data-track-id'));
        var rect = row.getBoundingClientRect();
        var x = e.clientX - rect.left;
        var beat = Math.floor(x / timelinePixelsPerBeat);

        // Always create a new pattern for each new clip
        var patternId = state.patterns.length;
        state.patterns.push(createTrackerPattern(16, state.lpb, trackId));

        // Add clip at this position
        var clip = addClipToTrack(trackId, patternId, beat, 1);
        if (clip) {
            renderTimeline();
            selectClip(trackId, clip.id);  // Select the new clip for editing
            consoleLog('Added pattern ' + (patternId + 1) + ' to track ' + (trackId + 1) + ' at beat ' + beat);
        }
    }
}

function openClipInEditor(trackId, clipId) {
    var track = state.tracks[trackId];
    if (!track) return;

    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipId) {
            var patternIdx = track.clips[i].patternId;
            // Set the selected clip (DAW-style)
            state.selectedClip = { trackId: trackId, clipId: clipId };
            state.focusedTrack = trackId;
            state.selectedTrack = trackId;
            renderTrackerGrid(true);
            renderTrackList();
            consoleLog('Editing pattern ' + (patternIdx + 1) + ' from track ' + (trackId + 1));
            break;
        }
    }
}

// ============================================
// PATTERN MANAGEMENT (DAW-style - patterns exist as clips)
// ============================================

// Clone the currently selected clip's pattern and create a new clip
function clonePattern() {
    var currentPattern = getCurrentPattern();
    if (!currentPattern) {
        consoleLog('No pattern selected to clone');
        return;
    }
    var cloned = JSON.parse(JSON.stringify(currentPattern));
    cloned.id = state.patterns.length;
    cloned.name = 'Pattern ' + (state.patterns.length + 1);
    state.patterns.push(cloned);
    consoleLog('Cloned pattern to ' + (state.patterns.length));
}

// Delete the currently selected clip
function deleteSelectedClip() {
    if (!state.selectedClip || state.selectedClip.trackId === null || state.selectedClip.clipId === null) {
        consoleLog('No clip selected');
        return;
    }
    removeClipFromTrack(state.selectedClip.trackId, state.selectedClip.clipId);
    state.selectedClip = { trackId: null, clipId: null };
    currentGridPatternIndex = -1;
    renderTimeline();
    renderTrackerGrid();
    consoleLog('Deleted clip');
}

function applyStepCount() {
    // Redirect to applyPatternSteps which uses pattern-steps element
    applyPatternSteps();
}

function applyPatternSteps() {
    var stepsEl = document.getElementById('pattern-steps');
    var lpbEl = document.getElementById('pattern-lpb');
    if (!stepsEl) return;

    var newSteps = parseInt(stepsEl.value) || 16;
    var newLpb = lpbEl ? parseInt(lpbEl.value) || state.lpb : state.lpb;

    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    if (!pattern) return;

    var oldSteps = pattern.steps;

    // Update LPB
    pattern.lpb = newLpb;

    // Update steps if changed
    if (newSteps !== oldSteps) {
        pattern.steps = newSteps;

        // Handle single-track pattern (new format)
        if (!Array.isArray(pattern.data[0])) {
            if (newSteps > oldSteps) {
                for (var step = oldSteps; step < newSteps; step++) {
                    pattern.data[step] = { note: '', amp: '', params: [] };
                }
            } else {
                pattern.data.length = newSteps;
            }
        }
    }

    invalidatePatternCache(patternIndex);
    renderTimeline();
    renderTrackerGrid(true);
    consoleLog('Pattern: ' + newSteps + ' steps, LPB=' + newLpb);
}

function markPatternDirty(patternIndex) {
    if (patternGridCache[patternIndex]) {
        patternGridCache[patternIndex]._dirty = true;
    }
}

function invalidatePatternCache(patternIndex) {
    if (patternIndex !== undefined) {
        if (patternGridCache[patternIndex]) {
            patternGridCache[patternIndex].remove();
            delete patternGridCache[patternIndex];
        }
    } else {
        for (var key in patternGridCache) {
            if (patternGridCache[key] && patternGridCache[key].remove) {
                patternGridCache[key].remove();
            }
        }
        patternGridCache = {};
    }
    currentGridPatternIndex = -1;
}

function prerenderAllPatterns() {
    var grid = domCache.grid;

    for (var i = 0; i < state.patterns.length; i++) {
        if (!patternGridCache[i]) {
            var container = buildPatternGridContainer(i);
            container.style.display = 'none';
            grid.appendChild(container);
            patternGridCache[i] = container;
        }
    }
}

// ============================================
// TRACKER GRID RENDERING
// ============================================

function buildPatternGridContainer(patternIndex) {
    var pattern = state.patterns[patternIndex];
    var container = document.createElement('div');
    container.className = 'pattern-grid-container';
    container.setAttribute('data-pattern-index', patternIndex);

    // Single track view (DAW-style)
    var track = document.createElement('div');
    track.className = 'track single-track';
    track.setAttribute('data-track', pattern.trackId || 0);

    // Control bar above columns (instrument selector + centered +/- buttons)
    var controlBar = document.createElement('div');
    controlBar.className = 'pattern-control-bar';

    // Instrument selector
    var instrSelect = document.createElement('div');
    instrSelect.className = 'pattern-instr-select';
    instrSelect.innerHTML = '<label>Instr: <select class="instr-dropdown" data-pattern="' + patternIndex + '">';
    var selectHtml = '';
    for (var i = 1; i <= 128; i++) {
        var selected = (pattern.instrument === i) ? ' selected' : '';
        selectHtml += '<option value="' + i + '"' + selected + '>' + i + '</option>';
    }
    instrSelect.innerHTML = '<label>Instr: <select class="instr-dropdown" data-pattern="' + patternIndex + '">' + selectHtml + '</select></label>';
    controlBar.appendChild(instrSelect);

    // Centered column controls
    var colControls = document.createElement('div');
    colControls.className = 'pattern-col-controls';
    colControls.innerHTML =
        '<button class="btn-note-col-minus" data-pattern="' + patternIndex + '" title="Remove note column">- Note</button>' +
        '<button class="btn-note-col-plus" data-pattern="' + patternIndex + '" title="Add note column">+ Note</button>';
    controlBar.appendChild(colControls);

    track.appendChild(controlBar);

    // Track rows container
    var rows = document.createElement('div');
    rows.className = 'track-rows';

    // Column labels row
    var labelsRow = document.createElement('div');
    labelsRow.className = 'column-labels';

    // Row number header
    var labelRowNum = document.createElement('div');
    labelRowNum.className = 'row-number';
    labelsRow.appendChild(labelRowNum);

    // Build labels for each note column
    var numNoteCols = pattern.noteColumns || 1;
    for (var nc = 0; nc < numNoteCols; nc++) {
        var noteColLabels = document.createElement('div');
        noteColLabels.className = 'note-column-group';
        noteColLabels.setAttribute('data-note-col', nc);

        // Note and velocity labels
        noteColLabels.innerHTML = '<div class="cell note-label">Note</div>' +
                                   '<div class="cell amp-label">Vel</div>';

        // FX column labels for this note column (p6, p7, p8, etc.)
        var fxCount = getFxCount(pattern, nc);
        for (var fx = 0; fx < fxCount; fx++) {
            var fxLabel = document.createElement('div');
            fxLabel.className = 'cell fx-label';
            fxLabel.textContent = 'p' + (6 + fx);
            noteColLabels.appendChild(fxLabel);
        }

        // Per-note-column FX +/- buttons
        var fxBtns = document.createElement('div');
        fxBtns.className = 'fx-col-controls';
        fxBtns.innerHTML =
            '<button class="btn-fx-minus" data-pattern="' + patternIndex + '" data-note-col="' + nc + '" title="Remove p-field">-p</button>' +
            '<button class="btn-fx-plus" data-pattern="' + patternIndex + '" data-note-col="' + nc + '" title="Add p-field">+p</button>';
        noteColLabels.appendChild(fxBtns);

        labelsRow.appendChild(noteColLabels);
    }

    rows.appendChild(labelsRow);

    // Ensure pattern data has proper structure
    for (var step = 0; step < pattern.steps; step++) {
        if (!pattern.data[step]) {
            pattern.data[step] = { columns: [] };
        }
        if (!pattern.data[step].columns) {
            pattern.data[step].columns = [];
        }
        // Ensure we have enough columns
        while (pattern.data[step].columns.length < numNoteCols) {
            pattern.data[step].columns.push({ note: '', amp: '', fx: [] });
        }
        // Ensure each column has enough FX
        for (var nc = 0; nc < numNoteCols; nc++) {
            var col = pattern.data[step].columns[nc];
            if (!col.fx) col.fx = [];
            var expectedFx = getFxCount(pattern, nc);
            while (col.fx.length < expectedFx) {
                col.fx.push('');
            }
        }
    }

    // Data rows
    for (var step = 0; step < pattern.steps; step++) {
        var row = createDataRowSingle(step, pattern);
        rows.appendChild(row);
    }

    track.appendChild(rows);
    container.appendChild(track);

    return container;
}

// Create data row for single-track pattern with multiple note columns
function createDataRowSingle(step, pattern) {
    var row = document.createElement('div');
    row.className = 'track-row';
    row.setAttribute('data-step', step);

    // Row number
    var rowNum = document.createElement('div');
    rowNum.className = 'row-number';
    rowNum.textContent = step.toString().padStart(3, '0');
    row.appendChild(rowNum);

    var stepData = pattern.data[step] || { columns: [{ note: '', amp: '', fx: [] }] };
    var numNoteCols = pattern.noteColumns || 1;

    // Render each note column
    for (var nc = 0; nc < numNoteCols; nc++) {
        var colData = stepData.columns[nc] || { note: '', amp: '', fx: [] };

        var noteColEl = document.createElement('div');
        noteColEl.className = 'note-column-group';
        noteColEl.setAttribute('data-note-col', nc);

        // Note cell
        var noteCell = document.createElement('div');
        noteCell.className = 'cell note';
        noteCell.setAttribute('data-step', step);
        noteCell.setAttribute('data-note-col', nc);
        noteCell.setAttribute('data-type', 'note');
        noteCell.textContent = colData.note || '---';
        if (colData.note === NOTE_OFF) {
            noteCell.classList.add('note-off');
        }
        noteColEl.appendChild(noteCell);

        // Amp cell
        var ampCell = document.createElement('div');
        ampCell.className = 'cell amp';
        ampCell.setAttribute('data-step', step);
        ampCell.setAttribute('data-note-col', nc);
        ampCell.setAttribute('data-type', 'amp');
        ampCell.textContent = colData.amp || '--';
        noteColEl.appendChild(ampCell);

        // FX cells for this note column
        var fxCount = getFxCount(pattern, nc);
        for (var fx = 0; fx < fxCount; fx++) {
            var fxCell = document.createElement('div');
            fxCell.className = 'cell fx';
            fxCell.setAttribute('data-step', step);
            fxCell.setAttribute('data-note-col', nc);
            fxCell.setAttribute('data-col', fx);
            fxCell.setAttribute('data-type', 'fx');

            var fxVal = colData.fx[fx];
            if (fxVal && fxVal !== '' && fxVal !== '--' && fxVal !== '----') {
                var numVal = parseInt(fxVal, 16);
                if (!isNaN(numVal)) {
                    fxCell.textContent = numVal.toString(16).toUpperCase().padStart(4, '0');
                } else {
                    fxCell.textContent = fxVal.toUpperCase();
                }
            } else {
                fxCell.textContent = '----';
            }
            noteColEl.appendChild(fxCell);
        }

        row.appendChild(noteColEl);
    }

    return row;
}

function renderTrackerGrid(forceRebuild) {
    var grid = domCache.grid;
    if (!grid) {
        grid = document.getElementById('tracker-grid');
        domCache.grid = grid;
    }
    if (!grid) return;

    var patternIndex = getCurrentPatternIndex();

    // Handle no pattern selected (show empty state)
    if (patternIndex === -1) {
        // Hide all pattern containers
        for (var key in patternGridCache) {
            if (patternGridCache[key]) {
                patternGridCache[key].style.display = 'none';
            }
        }
        currentGridPatternIndex = -1;
        // Update title to show no pattern selected
        var titleEl = document.getElementById('pattern-editor-title');
        if (titleEl) titleEl.textContent = 'No pattern selected - double-click timeline to create';
        return;
    }

    if (!forceRebuild && currentGridPatternIndex === patternIndex) {
        return;
    }

    if (forceRebuild && patternGridCache[patternIndex]) {
        patternGridCache[patternIndex].remove();
        delete patternGridCache[patternIndex];
    }

    // Hide all pattern containers
    for (var key in patternGridCache) {
        if (patternGridCache[key]) {
            patternGridCache[key].style.display = 'none';
        }
    }

    // Create container if not exists
    if (!patternGridCache[patternIndex]) {
        var container = buildPatternGridContainer(patternIndex);
        grid.appendChild(container);
        patternGridCache[patternIndex] = container;
    }

    patternGridCache[patternIndex].style.display = 'contents';
    currentGridPatternIndex = patternIndex;

    // Attach event handlers once
    if (!grid._eventsAttached) {
        attachGridEvents(grid);
        grid._eventsAttached = true;
    }

    // Clear selection when switching patterns
    clearSelection();

    // Update note column count display
    updateNoteColDisplay();

    // Update pattern header (steps, LPB)
    var pattern = state.patterns[patternIndex];
    if (pattern) {
        var stepsInput = document.getElementById('pattern-steps');
        var lpbInput = document.getElementById('pattern-lpb');
        var titleEl = document.getElementById('pattern-editor-title');

        if (stepsInput) stepsInput.value = pattern.steps || 16;
        if (lpbInput) lpbInput.value = pattern.lpb || state.lpb;
        if (titleEl) titleEl.textContent = 'Pattern ' + (patternIndex + 1) + ': ' + (pattern.name || 'Untitled');
    }
}

// ============================================
// EVENT HANDLING
// ============================================

function attachGridEvents(grid) {
    // Mouse events for selection
    grid.addEventListener('mousedown', onGridMouseDown);

    // Right-click context menu
    grid.addEventListener('contextmenu', onGridContextMenu);

    // Click for buttons
    grid.addEventListener('click', onGridClick);

    // Change for dropdowns (instrument selector)
    grid.addEventListener('change', onInstrDropdownChange);

    // Double click for editing
    grid.addEventListener('dblclick', onGridDblClick);

    // Global keyboard
    document.addEventListener('keydown', onDocumentKeyDown);
    document.addEventListener('keyup', onDocumentKeyUp);
}

function onGridContextMenu(e) {
    e.preventDefault();

    var cell = findCell(e.target);
    if (cell) {
        // If clicking on a cell not in selection, select it first
        var info = getCellInfo(cell);
        if (info) {
            var isInSelection = false;
            for (var i = 0; i < selectedCells.length; i++) {
                if (selectedCells[i] === cell) {
                    isInSelection = true;
                    break;
                }
            }
            if (!isInSelection) {
                selectCell(cell);
            }
        }
    }

    showContextMenu(e.clientX, e.clientY);
}

function onGridMouseDown(e) {
    var cell = findCell(e.target);
    if (!cell) return;

    // Only left button
    if (e.button !== 0) return;

    e.preventDefault();

    var info = getCellInfo(cell);
    if (!info) return;

    // Start selection
    dragState.active = true;
    dragState.startX = e.clientX;
    dragState.startY = e.clientY;

    var absCol = toAbsoluteCol(info.noteCol, info.type, info.col);

    selection.active = true;
    selection.startNoteCol = info.noteCol;
    selection.startStep = info.step;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.startAbsCol = absCol;
    selection.endNoteCol = info.noteCol;
    selection.endStep = info.step;
    selection.endCol = info.col;
    selection.endType = info.type;
    selection.endAbsCol = absCol;

    state.focusedNoteCol = info.noteCol;
    state.focusedStep = info.step;
    state.focusedColumn = info.col;
    state.focusedType = info.type;

    // Clear hex input buffer when selection changes
    fxInputBuffer = '';
    if (fxInputTimeout) {
        clearTimeout(fxInputTimeout);
        fxInputTimeout = null;
    }

    // Update visual
    highlightSelection();

    // Add drag listeners
    document.addEventListener('mousemove', onDocumentMouseMove);
    document.addEventListener('mouseup', onDocumentMouseUp);

    document.body.style.userSelect = 'none';
}

function onDocumentMouseMove(e) {
    if (!dragState.active) return;

    e.preventDefault();

    var element = document.elementFromPoint(e.clientX, e.clientY);
    if (!element) return;

    var cell = findCell(element);
    if (!cell) return;

    var info = getCellInfo(cell);
    if (!info) return;

    var absCol = toAbsoluteCol(info.noteCol, info.type, info.col);

    // Track if anything changed
    var changed = false;

    // Update noteCol, step, and column for rectangular selection
    if (selection.endNoteCol !== info.noteCol || selection.endStep !== info.step || selection.endAbsCol !== absCol) {
        selection.endNoteCol = info.noteCol;
        selection.endStep = info.step;
        selection.endCol = info.col;
        selection.endType = info.type;
        selection.endAbsCol = absCol;
        changed = true;
    }

    if (changed) {
        highlightSelection();
    }
}

function onDocumentMouseUp(e) {
    dragState.active = false;
    document.body.style.userSelect = '';

    document.removeEventListener('mousemove', onDocumentMouseMove);
    document.removeEventListener('mouseup', onDocumentMouseUp);
}

function onGridClick(e) {
    var target = e.target;

    if (target.classList.contains('btn-mute')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        state.tracks[trackIdx].muted = !state.tracks[trackIdx].muted;
        target.classList.toggle('active', state.tracks[trackIdx].muted);
        updateTrackAudibilityVisuals();
    } else if (target.classList.contains('btn-solo')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        state.tracks[trackIdx].soloed = !state.tracks[trackIdx].soloed;
        target.classList.toggle('active', state.tracks[trackIdx].soloed);
        updateTrackAudibilityVisuals();
    } else if (target.classList.contains('btn-fx-plus')) {
        // Add FX column to a specific note column
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        var noteColIdx = parseInt(target.getAttribute('data-note-col'));
        var pattern = state.patterns[patternIdx];
        if (pattern) {
            var currentFx = getFxCount(pattern, noteColIdx);
            if (currentFx < 8) {
                addFxColumn(patternIdx, noteColIdx);
                invalidatePatternCache();
                renderTrackerGrid(true);
                consoleLog('Added FX column to note column ' + (noteColIdx + 1));
            }
        }
    } else if (target.classList.contains('btn-fx-minus')) {
        // Remove FX column from a specific note column
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        var noteColIdx = parseInt(target.getAttribute('data-note-col'));
        var pattern = state.patterns[patternIdx];
        if (pattern) {
            var currentFx = getFxCount(pattern, noteColIdx);
            if (currentFx > 0) {
                removeFxColumn(patternIdx, noteColIdx);
                invalidatePatternCache();
                renderTrackerGrid(true);
                consoleLog('Removed FX column from note column ' + (noteColIdx + 1));
            }
        }
    } else if (target.classList.contains('btn-note-col-plus')) {
        // Add note column to pattern
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        addNoteColumn(patternIdx);
        invalidatePatternCache();
        renderTrackerGrid(true);
        consoleLog('Added note column');
    } else if (target.classList.contains('btn-note-col-minus')) {
        // Remove note column from pattern
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        removeNoteColumn(patternIdx);
        invalidatePatternCache();
        renderTrackerGrid(true);
        consoleLog('Removed note column');
    } else if (target.classList.contains('btn-fx-all-plus')) {
        // Add FX column to ALL note columns
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        var pattern = state.patterns[patternIdx];
        if (pattern) {
            var numNoteCols = pattern.noteColumns || 1;
            for (var nc = 0; nc < numNoteCols; nc++) {
                if (getFxCount(pattern, nc) < 8) {
                    addFxColumn(patternIdx, nc);
                }
            }
            invalidatePatternCache();
            renderTrackerGrid(true);
            consoleLog('Added p-field to all note columns');
        }
    } else if (target.classList.contains('btn-fx-all-minus')) {
        // Remove FX column from ALL note columns
        var patternIdx = parseInt(target.getAttribute('data-pattern'));
        var pattern = state.patterns[patternIdx];
        if (pattern) {
            var numNoteCols = pattern.noteColumns || 1;
            for (var nc = 0; nc < numNoteCols; nc++) {
                if (getFxCount(pattern, nc) > 0) {
                    removeFxColumn(patternIdx, nc);
                }
            }
            invalidatePatternCache();
            renderTrackerGrid(true);
            consoleLog('Removed p-field from all note columns');
        }
    }
}

// Handle instrument dropdown change
function onInstrDropdownChange(e) {
    if (!e.target.classList.contains('instr-dropdown')) return;
    var patternIdx = parseInt(e.target.getAttribute('data-pattern'));
    var instrNum = parseInt(e.target.value);
    if (state.patterns[patternIdx]) {
        state.patterns[patternIdx].instrument = instrNum;
        consoleLog('Pattern using instrument ' + instrNum + ' (keyboard preview active)');
    }
}

function onGridDblClick(e) {
    var cell = findCell(e.target);
    if (cell) {
        startEditing(cell);
    }
}

function onDocumentKeyDown(e) {
    // Skip if in textarea or other input (except our edit input)
    if (e.target.tagName === 'TEXTAREA') return;
    if (e.target.tagName === 'INPUT' && e.target !== editInput) return;

    // If editing, let the edit input handle it
    if (editingCell && e.target === editInput) return;

    // Code editor shortcuts
    if (e.target.id === 'code-editor' || e.target.id === 'opcodes-editor') {
        if (e.altKey && e.code === 'Space') {
            e.preventDefault();
            compileInstruments();
        }
        return;
    }

    // Live keyboard preview - handle note-on FIRST before any other processing
    // This ensures preview happens even if we also record to grid
    // Only preview when focused on a note column (not amp/fx columns)
    var keyLower = e.key.toLowerCase();
    if (keyboardMap.hasOwnProperty(keyLower) && !e.repeat && !e.ctrlKey && !e.altKey) {
        var currentType = state.focusedType || 'note';
        if (currentType === 'note') {
            // Determine which track/column to use for the preview
            var previewTrack = state.focusedTrack >= 0 ? state.focusedTrack : 0;
            var previewCol = state.focusedColumn >= 0 ? state.focusedColumn : 0;

            // Play the note preview
            playNotePreview(keyLower, previewTrack, previewCol);
        }
    }

    // Backtick - toggle recording
    if (e.key === '`' || e.code === 'Backquote') {
        e.preventDefault();
        toggleRecording();
        return;
    }

    // Space - play/stop
    if (e.code === 'Space') {
        e.preventDefault();
        if (state.isPlaying) {
            stopPlayback();
        } else {
            startPlayback();
        }
        return;
    }

    // L - toggle loop region
    if (e.key === 'l' || e.key === 'L') {
        e.preventDefault();
        toggleLoopRegion();
        updateLoopButton();
        return;
    }

    // N - toggle snap to measure
    if (e.key === 'n' || e.key === 'N') {
        e.preventDefault();
        toggleSnapToMeasure();
        updateSnapButton();
        return;
    }

    // Ctrl+S - save
    if (e.ctrlKey && e.key === 's') {
        e.preventDefault();
        saveSong();
        return;
    }

    // Ctrl+O - load
    if (e.ctrlKey && e.key === 'o') {
        e.preventDefault();
        document.getElementById('file-input').click();
        return;
    }

    // Octave up/down
    if (e.key === '=' || e.key === '+') {
        e.preventDefault();
        if (state.baseOctave < 8) {
            state.baseOctave++;
            updateOctaveDisplay();
            consoleLog('Octave: ' + state.baseOctave);
        }
        return;
    }

    if (e.key === '-') {
        e.preventDefault();
        if (state.baseOctave > 0) {
            state.baseOctave--;
            updateOctaveDisplay();
            consoleLog('Octave: ' + state.baseOctave);
        }
        return;
    }

    // Arrow navigation - always works (will create selection if needed)
    if (e.key === 'ArrowDown') {
        e.preventDefault();
        navigateSelection(0, 1);
        return;
    }
    if (e.key === 'ArrowUp') {
        e.preventDefault();
        navigateSelection(0, -1);
        return;
    }
    if (e.key === 'ArrowRight') {
        e.preventDefault();
        navigateSelection(1, 0);
        return;
    }
    if (e.key === 'ArrowLeft') {
        e.preventDefault();
        navigateSelection(-1, 0);
        return;
    }

    // Selection-based shortcuts
    if (selection.active && selectedCells.length > 0) {
        // Ctrl+C - copy
        if (e.ctrlKey && e.key === 'c') {
            e.preventDefault();
            copySelection();
            return;
        }

        // Ctrl+X - cut
        if (e.ctrlKey && e.key === 'x') {
            e.preventDefault();
            cutSelection();
            return;
        }

        // Ctrl+V - paste
        if (e.ctrlKey && e.key === 'v') {
            e.preventDefault();
            pasteAtSelection();
            return;
        }

        // Delete/Backspace - clear
        if (e.key === 'Delete' || e.key === 'Backspace') {
            e.preventDefault();
            clearSelectionData();
            return;
        }

        // Tab - note off
        if (e.key === 'Tab' && selection.startType === 'note') {
            e.preventDefault();
            enterNoteInSelection(NOTE_OFF);
            return;
        }

        // Enter - start editing
        if (e.key === 'Enter') {
            e.preventDefault();
            if (selectedCells.length > 0) {
                startEditing(selectedCells[0]);
            }
            return;
        }

        // Piano keys for note entry - only record to grid if recording is enabled
        var key = e.key.toLowerCase();
        if (keyboardMap.hasOwnProperty(key) && selection.startType === 'note') {
            e.preventDefault();
            // Only enter note into grid if recording, otherwise just preview (handled at top of function)
            if (state.isRecording) {
                var semitone = keyboardMap[key];
                var noteName = semitoneToNoteName(semitone, state.baseOctave);
                enterNoteInSelectionNoPreview(noteName);
            }
            return;
        }

        // Hex input for FX columns (0-9, A-F)
        if (selection.startType === 'fx') {
            var hexKey = e.key.toUpperCase();
            if (/^[0-9A-F]$/.test(hexKey)) {
                e.preventDefault();
                enterHexInFxSelection(hexKey);
                return;
            }
        }

        // Hex input for amp/velocity column (0-9, A-F)
        if (selection.startType === 'amp') {
            var hexKey = e.key.toUpperCase();
            if (/^[0-9A-F]$/.test(hexKey)) {
                e.preventDefault();
                enterHexInAmpSelection(hexKey);
                return;
            }
        }
    }

    // Recording mode piano keys
    if (state.isRecording) {
        var key = e.key.toLowerCase();
        if (keyboardMap.hasOwnProperty(key)) {
            e.preventDefault();
            var semitone = keyboardMap[key];
            var noteName = semitoneToNoteName(semitone, state.baseOctave);
            recordNote(noteName);
            // Note: preview is handled at the top of this function
        }
    }
}

function onDocumentKeyUp(e) {
    // Skip if in textarea or input
    if (e.target.tagName === 'TEXTAREA') return;
    if (e.target.tagName === 'INPUT' && e.target !== editInput) return;

    // Stop note preview on key release
    var key = e.key.toLowerCase();
    if (keyboardMap.hasOwnProperty(key)) {
        stopNotePreview(key);
    }
}

// ============================================
// CELL HELPERS
// ============================================

function findCell(element) {
    if (!element) return null;
    if (element.classList && element.classList.contains('cell') && element.hasAttribute('data-step')) {
        return element;
    }
    if (element.closest) {
        var cell = element.closest('.cell');
        if (cell && cell.hasAttribute('data-step')) {
            return cell;
        }
    }
    return null;
}

function getCellInfo(cell) {
    if (!cell) return null;

    var step = parseInt(cell.getAttribute('data-step'));
    var noteCol = parseInt(cell.getAttribute('data-note-col'));
    var col = parseInt(cell.getAttribute('data-col'));  // FX column index within note column
    var type = cell.getAttribute('data-type');

    if (isNaN(step) || !type) return null;
    if (isNaN(noteCol)) noteCol = 0;
    if (isNaN(col)) col = 0;

    return { step: step, noteCol: noteCol, col: col, type: type };
}

function findCellElement(step, noteCol, col, type) {
    var container = patternGridCache[currentGridPatternIndex];
    if (!container) return null;

    if (type === 'fx') {
        return container.querySelector(
            '.cell[data-step="' + step + '"][data-note-col="' + noteCol + '"][data-col="' + col + '"][data-type="' + type + '"]'
        );
    } else {
        return container.querySelector(
            '.cell[data-step="' + step + '"][data-note-col="' + noteCol + '"][data-type="' + type + '"]'
        );
    }
}

// ============================================
// SELECTION
// ============================================

function clearSelection() {
    for (var i = 0; i < selectedCells.length; i++) {
        selectedCells[i].classList.remove('selected');
    }
    selectedCells = [];
    selection.active = false;
}

// Convert (noteCol, type, fxCol) to absolute column index
// Layout: [noteCol0: note, amp, fx0, fx1...] [noteCol1: note, amp, fx0, fx1...] ...
function toAbsoluteCol(noteCol, type, fxCol) {
    var pattern = getCurrentPattern();
    if (!pattern) return 0;

    var absCol = 0;
    // Add columns from previous note columns
    for (var nc = 0; nc < noteCol; nc++) {
        absCol += 2 + getFxCount(pattern, nc);  // note + amp + fx columns
    }
    // Add column within current note column
    if (type === 'note') {
        return absCol;
    } else if (type === 'amp') {
        return absCol + 1;
    } else if (type === 'fx') {
        return absCol + 2 + fxCol;
    }
    return absCol;
}

// Convert absolute column index to (noteCol, type, fxCol)
function fromAbsoluteCol(absCol) {
    var pattern = getCurrentPattern();
    if (!pattern) return { noteCol: 0, type: 'note', col: 0 };

    var numNoteCols = pattern.noteColumns || 1;
    var colOffset = 0;

    for (var nc = 0; nc < numNoteCols; nc++) {
        var fxCount = getFxCount(pattern, nc);
        var noteColWidth = 2 + fxCount;  // note + amp + fx columns

        if (absCol < colOffset + noteColWidth) {
            var localCol = absCol - colOffset;
            if (localCol === 0) {
                return { noteCol: nc, type: 'note', col: 0 };
            } else if (localCol === 1) {
                return { noteCol: nc, type: 'amp', col: 0 };
            } else {
                return { noteCol: nc, type: 'fx', col: localCol - 2 };
            }
        }
        colOffset += noteColWidth;
    }

    // Default to last column
    return { noteCol: numNoteCols - 1, type: 'note', col: 0 };
}

// Get total number of columns in current pattern
function getTotalColumns() {
    var pattern = getCurrentPattern();
    if (!pattern) return 2;

    var total = 0;
    var numNoteCols = pattern.noteColumns || 1;
    for (var nc = 0; nc < numNoteCols; nc++) {
        total += 2 + getFxCount(pattern, nc);  // note + amp + fx columns
    }
    return total;
}

function highlightSelection() {
    // Clear old highlights
    for (var i = 0; i < selectedCells.length; i++) {
        selectedCells[i].classList.remove('selected');
    }
    selectedCells = [];

    if (!selection.active) return;

    var container = patternGridCache[currentGridPatternIndex];
    if (!container) return;

    var minStep = Math.min(selection.startStep, selection.endStep);
    var maxStep = Math.max(selection.startStep, selection.endStep);
    var minAbsCol = Math.min(selection.startAbsCol, selection.endAbsCol);
    var maxAbsCol = Math.max(selection.startAbsCol, selection.endAbsCol);
    var totalCols = getTotalColumns();

    // Simple rectangular selection
    for (var step = minStep; step <= maxStep; step++) {
        for (var absCol = minAbsCol; absCol <= maxAbsCol && absCol < totalCols; absCol++) {
            var colInfo = fromAbsoluteCol(absCol);
            var cell = findCellElement(step, colInfo.noteCol, colInfo.col, colInfo.type);
            if (cell) {
                cell.classList.add('selected');
                selectedCells.push(cell);
            }
        }
    }
}

function navigateSelection(colDelta, stepDelta) {
    var pattern = getCurrentPattern();
    if (!pattern) return;

    // If no active selection, create one at current focused position or (0,0,0)
    if (!selection.active || selection.startAbsCol < 0) {
        var noteCol = state.focusedNoteCol >= 0 ? state.focusedNoteCol : 0;
        var step = state.focusedStep >= 0 ? state.focusedStep : 0;
        var type = state.focusedType || 'note';
        var col = state.focusedColumn >= 0 ? state.focusedColumn : 0;
        var absCol = toAbsoluteCol(noteCol, type, col);

        selection.active = true;
        selection.startStep = step;
        selection.startAbsCol = absCol;
        selection.startNoteCol = noteCol;
        selection.startType = type;
        selection.startCol = col;
        selection.endStep = step;
        selection.endAbsCol = absCol;
        selection.endNoteCol = noteCol;
        selection.endType = type;
        selection.endCol = col;
    }

    var absCol = selection.startAbsCol + colDelta;
    var step = selection.startStep + stepDelta;

    // Get total columns for current pattern
    var totalCols = getTotalColumns();

    // Clamp column to valid range
    if (absCol < 0) absCol = 0;
    if (absCol >= totalCols) absCol = totalCols - 1;

    // Wrap step within pattern bounds
    if (step < 0) step = 0;
    if (step >= pattern.steps) step = pattern.steps - 1;

    // Update selection
    selection.startStep = step;
    selection.startAbsCol = absCol;
    selection.endStep = step;
    selection.endAbsCol = absCol;

    // Update type/col for compatibility
    var colInfo = fromAbsoluteCol(absCol);
    selection.startNoteCol = colInfo.noteCol;
    selection.startType = colInfo.type;
    selection.startCol = colInfo.col;
    selection.endNoteCol = colInfo.noteCol;
    selection.endType = colInfo.type;
    selection.endCol = colInfo.col;

    state.focusedNoteCol = colInfo.noteCol;
    state.focusedStep = step;
    state.focusedColumn = colInfo.col;
    state.focusedType = colInfo.type;

    highlightSelection();

    // Scroll into view
    if (selectedCells.length > 0) {
        selectedCells[0].scrollIntoView({ block: 'nearest', behavior: 'auto' });
    }
}

function selectCell(cell) {
    var info = getCellInfo(cell);
    if (!info) return;

    var absCol = toAbsoluteCol(info.noteCol, info.type, info.col);

    selection.active = true;
    selection.startStep = info.step;
    selection.startNoteCol = info.noteCol;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.startAbsCol = absCol;
    selection.endStep = info.step;
    selection.endNoteCol = info.noteCol;
    selection.endCol = info.col;
    selection.endType = info.type;
    selection.endAbsCol = absCol;

    state.focusedNoteCol = info.noteCol;
    state.focusedStep = info.step;
    state.focusedColumn = info.col;
    state.focusedType = info.type;

    highlightSelection();
}

// ============================================
// EDITING
// ============================================

function createEditInput() {
    if (editInput) return editInput;

    editInput = document.createElement('input');
    editInput.type = 'text';
    editInput.className = 'cell-edit-input';
    editInput.addEventListener('keydown', onEditInputKeyDown);
    editInput.addEventListener('blur', finishEditing);
    document.body.appendChild(editInput);

    return editInput;
}

function startEditing(cell) {
    if (!cell || editingCell === cell) return;
    finishEditing();

    var info = getCellInfo(cell);
    if (!info) return;

    editingCell = cell;
    var input = createEditInput();
    var rect = cell.getBoundingClientRect();

    input.style.position = 'fixed';
    input.style.left = rect.left + 'px';
    input.style.top = rect.top + 'px';
    input.style.width = rect.width + 'px';
    input.style.height = rect.height + 'px';
    input.style.display = 'block';

    var value = cell.textContent;
    input.value = (value === '---' || value === '--') ? '' : value;
    input.focus();
    input.select();
}

function finishEditing() {
    if (!editingCell || !editInput) return;

    var cell = editingCell;
    var info = getCellInfo(cell);

    if (info) {
        var value = editInput.value.trim().toUpperCase();

        // For FX cells, validate and format as hex
        if (info.type === 'fx' && value !== '') {
            // Allow hex input (with or without 0x prefix)
            var cleanValue = value.replace(/^0X/, '');
            var numVal = parseInt(cleanValue, 16);
            if (!isNaN(numVal)) {
                // Clamp to 0-FFFF range
                numVal = Math.min(Math.max(numVal, 0), 0xFFFF);
                value = numVal.toString(16).toUpperCase().padStart(4, '0');
            }
        }

        setCellValue(info.step, info.noteCol, info.col, info.type, value);
        updateCellDisplay(cell, info.type, value);
    }

    editInput.style.display = 'none';
    editingCell = null;
}

function onEditInputKeyDown(e) {
    if (e.key === 'Enter') {
        e.preventDefault();
        var cell = editingCell;
        finishEditing();
        if (cell && state.editStep > 0) {
            var info = getCellInfo(cell);
            if (info) {
                // Move down by edit step
                var nextCell = findCellElement(info.step + state.editStep, info.noteCol, info.col, info.type);
                if (nextCell) selectCell(nextCell);
            }
        }
    } else if (e.key === 'Escape') {
        editInput.style.display = 'none';
        editingCell = null;
    } else if (e.key === 'Tab') {
        e.preventDefault();
        if (editingCell) {
            var info = getCellInfo(editingCell);
            if (info && info.type === 'note') {
                editInput.value = NOTE_OFF;
            }
        }
    }
}

function setCellValue(step, noteCol, fxCol, type, value) {
    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    var stepData = pattern.data[step];
    if (!stepData || !stepData.columns) return;

    // Ensure column exists
    while (stepData.columns.length <= noteCol) {
        stepData.columns.push({ note: '', amp: '', fx: [] });
    }
    var colData = stepData.columns[noteCol];

    if (type === 'note') {
        colData.note = value;
    } else if (type === 'amp') {
        colData.amp = value;
    } else if (type === 'fx') {
        if (!colData.fx) colData.fx = [];
        while (colData.fx.length <= fxCol) {
            colData.fx.push('');
        }
        colData.fx[fxCol] = value;
    }

    markPatternDirty(patternIndex);
}

function updateCellDisplay(cell, type, value) {
    if (type === 'note') {
        cell.textContent = value || '---';
        if (value === NOTE_OFF) {
            cell.classList.add('note-off');
        } else {
            cell.classList.remove('note-off');
        }
    } else if (type === 'amp') {
        cell.textContent = value || '--';
    } else if (type === 'fx' || type === 'param') {
        // Display param/FX values as hex (0000-FFFF)
        if (!value || value === '' || value === '--' || value === '----') {
            cell.textContent = '----';
        } else {
            // If it's a number, convert to hex
            var numVal = parseInt(value, 16);
            if (!isNaN(numVal)) {
                cell.textContent = numVal.toString(16).toUpperCase().padStart(4, '0');
            } else {
                cell.textContent = value.toUpperCase();
            }
        }
    }
}

function enterNoteInSelection(noteName) {
    enterNoteInSelectionNoPreview(noteName);
    // Preview is now handled by keydown/keyup for proper note-on/note-off
}

function enterNoteInSelectionNoPreview(noteName) {
    if (selectedCells.length === 0) return;

    var cell = selectedCells[0];
    var info = getCellInfo(cell);
    if (!info || info.type !== 'note') return;

    setCellValue(info.step, info.noteCol, 0, 'note', noteName);
    updateCellDisplay(cell, 'note', noteName);

    // Move down by edit step (skip if editStep is 0)
    if (state.editStep > 0) {
        navigateSelection(0, state.editStep);
    }
}

// Play a note preview (called on keydown)
function playNotePreview(key, track, col) {
    if (!state.csoundReady) return;

    var semitone = keyboardMap[key];
    if (semitone === undefined) return;

    var noteName = semitoneToNoteName(semitone, state.baseOctave);
    var freq = parseNote(noteName);
    if (!freq) return;

    // Get instrument from current pattern if available, otherwise use track+1
    var baseInstr = track + 1;
    var pattern = getCurrentPattern();
    if (pattern && pattern.instrument) {
        baseInstr = pattern.instrument;
    }

    // Use fractional instrument number with semitone for unique instances (allows chords)
    // Format: instrNum.semitone (e.g., 1.00, 1.01, 1.12 for different keys on track 1)
    var instrNum = baseInstr + '.' + semitone.toString().padStart(2, '0');

    // Turn off any existing note for this key first using instrument 998 (note killer)
    if (pressedKeys[key]) {
        var oldInstrNum = pressedKeys[key].instrNum;
        csound.inputMessage('i 998 0 0.01 ' + oldInstrNum).catch(function() {});
    }

    // Track this pressed key
    pressedKeys[key] = {
        instrNum: instrNum,
        freq: freq,
        track: track,
        col: col,
        noteName: noteName
    };

    // Play the note with indefinite duration (-1 means held until turned off)
    var msg = 'i ' + instrNum + ' 0 -1 ' + freq.toFixed(4) + ' 0.7';
    csound.inputMessage(msg).catch(function(err) {
        consoleLog('Note on error: ' + err);
    });
}

// Stop a note preview (called on keyup)
function stopNotePreview(key) {
    if (!state.csoundReady) return;

    var keyInfo = pressedKeys[key];
    if (!keyInfo) return;

    // Turn off the note using instrument 998 (note killer)
    var offMsg = 'i 998 0 0.01 ' + keyInfo.instrNum;
    csound.inputMessage(offMsg).catch(function() {});

    // Remove from pressed keys
    delete pressedKeys[key];
}

// Play a chord preview (for chord buttons)
var chordPreviewNotes = [];
function playChordPreview(notes, track) {
    if (!state.csoundReady) return;

    // Stop any previous chord preview first
    stopChordPreview();

    // Use pattern instrument if available, otherwise track+1
    var instrBase = track + 1;
    var pattern = getCurrentPattern();
    if (pattern && pattern.instrument) {
        instrBase = pattern.instrument;
    }
    instrBase = String(instrBase);
    var promises = [];

    for (var i = 0; i < notes.length; i++) {
        var freq = parseNote(notes[i]);
        if (!freq) continue;

        // Use fractional instrument number: instrNum.noteIndex
        var instrNum = instrBase + '.' + (80 + i).toString().padStart(2, '0');
        chordPreviewNotes.push(instrNum);

        // Play with short duration (0.5 seconds)
        var msg = 'i ' + instrNum + ' 0 0.5 ' + freq.toFixed(4) + ' 0.7';
        promises.push(csound.inputMessage(msg));
    }

    // Send all notes simultaneously
    Promise.all(promises).catch(function(err) {
        console.error('Chord preview error:', err);
    });
}

function stopChordPreview() {
    if (!state.csoundReady) return;

    var promises = [];
    for (var i = 0; i < chordPreviewNotes.length; i++) {
        // Use instrument 998 (note killer) for reliable note-off
        var offMsg = 'i 998 0 0.01 ' + chordPreviewNotes[i];
        promises.push(csound.inputMessage(offMsg));
    }
    chordPreviewNotes = [];

    if (promises.length > 0) {
        Promise.all(promises).catch(function() {});
    }
}

// Track hex input buffer for FX columns
var fxInputBuffer = '';
var fxInputTimeout = null;

// Track hex input buffer for amp/velocity column
var ampInputBuffer = '';
var ampInputTimeout = null;

function enterHexInFxSelection(hexDigit) {
    if (selectedCells.length === 0) return;

    var cell = selectedCells[0];
    var info = getCellInfo(cell);
    if (!info || info.type !== 'fx') return;

    // Clear timeout and add to buffer
    if (fxInputTimeout) clearTimeout(fxInputTimeout);

    // Append digit to buffer (max 4 hex digits = FFFF)
    fxInputBuffer += hexDigit;
    if (fxInputBuffer.length > 4) {
        fxInputBuffer = fxInputBuffer.slice(-4);
    }

    // Parse and clamp value
    var value = parseInt(fxInputBuffer, 16);
    if (isNaN(value)) value = 0;
    if (value > 0xFFFF) value = 0xFFFF;

    // Format as hex with leading zeros (4 digits for 16-bit)
    var hexValue = value.toString(16).toUpperCase().padStart(4, '0');

    setCellValue(info.step, info.noteCol, info.col, 'fx', hexValue);
    updateCellDisplay(cell, 'fx', hexValue);

    // Reset buffer after a short delay (for continuous typing)
    fxInputTimeout = setTimeout(function() {
        fxInputBuffer = '';
        // Move down by edit step after input is complete (skip if editStep is 0)
        if (state.editStep > 0) {
            navigateSelection(0, state.editStep);
        }
    }, 500);
}

function enterHexInAmpSelection(hexDigit) {
    if (selectedCells.length === 0) return;

    var cell = selectedCells[0];
    var info = getCellInfo(cell);
    if (!info || info.type !== 'amp') return;

    // Clear timeout and add to buffer
    if (ampInputTimeout) clearTimeout(ampInputTimeout);

    // Append digit to buffer (max 2 hex digits = FF)
    ampInputBuffer += hexDigit;
    if (ampInputBuffer.length > 2) {
        ampInputBuffer = ampInputBuffer.slice(-2);
    }

    // Parse and clamp value
    var value = parseInt(ampInputBuffer, 16);
    if (isNaN(value)) value = 0;
    if (value > 0xFF) value = 0xFF;

    // Format as hex with leading zeros (2 digits for 8-bit)
    var hexValue = value.toString(16).toUpperCase().padStart(2, '0');

    setCellValue(info.step, info.noteCol, 0, 'amp', hexValue);
    updateCellDisplay(cell, 'amp', hexValue);

    // Reset buffer after a short delay (for continuous typing)
    ampInputTimeout = setTimeout(function() {
        ampInputBuffer = '';
        // Move down by edit step after input is complete (skip if editStep is 0)
        if (state.editStep > 0) {
            navigateSelection(0, state.editStep);
        }
    }, 500);
}

// ============================================
// CONTEXT MENU
// ============================================

var contextMenu = null;

function initContextMenu() {
    contextMenu = document.getElementById('context-menu');
    if (!contextMenu) return;

    // Hide menu on click outside
    document.addEventListener('click', function(e) {
        if (!contextMenu.contains(e.target)) {
            hideContextMenu();
        }
    });

    // Handle menu item clicks
    contextMenu.addEventListener('click', function(e) {
        var item = e.target.closest('.context-menu-item');
        if (!item || item.classList.contains('disabled')) return;

        var action = item.getAttribute('data-action');
        hideContextMenu();

        switch (action) {
            case 'interpolate':
                interpolateFxSelection();
                break;
            case 'clear':
                clearSelectionData();
                break;
            case 'copy':
                copySelection();
                break;
            case 'cut':
                cutSelection();
                break;
            case 'paste':
                pasteAtSelection();
                break;
        }
    });
}

function showContextMenu(x, y) {
    if (!contextMenu) return;

    // Update menu item states
    var interpolateItem = contextMenu.querySelector('[data-action="interpolate"]');
    var hasFxSelection = checkFxSelection();

    if (interpolateItem) {
        if (hasFxSelection) {
            interpolateItem.classList.remove('disabled');
        } else {
            interpolateItem.classList.add('disabled');
        }
    }

    // Position menu
    contextMenu.style.left = x + 'px';
    contextMenu.style.top = y + 'px';
    contextMenu.classList.add('visible');

    // Ensure menu stays within viewport
    var rect = contextMenu.getBoundingClientRect();
    if (rect.right > window.innerWidth) {
        contextMenu.style.left = (x - rect.width) + 'px';
    }
    if (rect.bottom > window.innerHeight) {
        contextMenu.style.top = (y - rect.height) + 'px';
    }
}

function hideContextMenu() {
    if (contextMenu) {
        contextMenu.classList.remove('visible');
    }
}

function checkFxSelection() {
    // Check if selection contains FX cells
    for (var i = 0; i < selectedCells.length; i++) {
        var info = getCellInfo(selectedCells[i]);
        if (info && info.type === 'fx') {
            return true;
        }
    }
    return false;
}

function interpolateFxSelection() {
    if (selectedCells.length < 2) {
        consoleLog('Need at least 2 cells selected for interpolation');
        return;
    }

    var pattern = getCurrentPattern();
    var patternIndex = getCurrentPatternIndex();

    if (!pattern || !pattern.data) {
        consoleLog('No pattern selected');
        return;
    }

    // Get all selected FX cells sorted by step
    var fxCells = [];
    for (var i = 0; i < selectedCells.length; i++) {
        var info = getCellInfo(selectedCells[i]);
        if (info && info.type === 'fx') {
            // Get FX value from the new pattern structure: pattern.data[step].columns[noteCol].fx[col]
            var stepData = pattern.data[info.step];
            if (!stepData || !stepData.columns || !stepData.columns[info.noteCol]) {
                continue;
            }
            var colData = stepData.columns[info.noteCol];
            var fxStr = colData.fx && colData.fx[info.col] ? colData.fx[info.col] : '';
            var value = null;
            if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                value = parseInt(fxStr, 16);
                if (isNaN(value)) value = null;
            }
            fxCells.push({
                cell: selectedCells[i],
                info: info,
                value: value,
                step: info.step
            });
        }
    }

    if (fxCells.length < 2) {
        consoleLog('Need at least 2 FX cells selected for interpolation');
        return;
    }

    // Sort by step
    fxCells.sort(function(a, b) { return a.step - b.step; });

    // Find first and last cells with values
    var firstWithValue = null;
    var lastWithValue = null;

    for (var i = 0; i < fxCells.length; i++) {
        if (fxCells[i].value !== null) {
            if (firstWithValue === null) {
                firstWithValue = i;
            }
            lastWithValue = i;
        }
    }

    if (firstWithValue === null || lastWithValue === null || firstWithValue === lastWithValue) {
        consoleLog('Need at least 2 cells with values for interpolation');
        return;
    }

    // Interpolate between first and last value
    var startValue = fxCells[firstWithValue].value;
    var endValue = fxCells[lastWithValue].value;
    var startStep = fxCells[firstWithValue].step;
    var endStep = fxCells[lastWithValue].step;
    var stepRange = endStep - startStep;

    if (stepRange === 0) {
        consoleLog('Cells must be on different steps');
        return;
    }

    // Fill in interpolated values for cells without data
    for (var i = firstWithValue; i <= lastWithValue; i++) {
        var cell = fxCells[i];
        if (cell.value === null) {
            // Calculate interpolated value
            var progress = (cell.step - startStep) / stepRange;
            var interpolatedValue = Math.round(startValue + (endValue - startValue) * progress);

            // Clamp to 0-65535 (hex 0000-FFFF)
            interpolatedValue = Math.max(0, Math.min(65535, interpolatedValue));

            // Set the value in the new pattern structure
            var hexValue = interpolatedValue.toString(16).toUpperCase().padStart(4, '0');
            var stepData = pattern.data[cell.info.step];
            if (stepData && stepData.columns && stepData.columns[cell.info.noteCol]) {
                var colData = stepData.columns[cell.info.noteCol];
                // Ensure fx array exists and is large enough
                if (!colData.fx) colData.fx = [];
                while (colData.fx.length <= cell.info.col) {
                    colData.fx.push('');
                }
                colData.fx[cell.info.col] = hexValue;
                updateCellDisplay(cell.cell, 'fx', hexValue);
            }
        }
    }

    markPatternDirty(patternIndex);
    consoleLog('Interpolated FX: ' + startValue.toString(16).toUpperCase() + ' -> ' + endValue.toString(16).toUpperCase());
}

// ============================================
// CHORDS
// ============================================

var chordTypes = [
    { name: 'Maj', intervals: [0, 4, 7], className: 'major' },
    { name: 'min', intervals: [0, 3, 7], className: 'minor' },
    { name: '7', intervals: [0, 4, 7, 10], className: '' },
    { name: 'Maj7', intervals: [0, 4, 7, 11], className: 'major' },
    { name: 'min7', intervals: [0, 3, 7, 10], className: 'minor' },
    { name: 'dim', intervals: [0, 3, 6], className: '' },
    { name: 'aug', intervals: [0, 4, 8], className: '' },
    { name: 'sus2', intervals: [0, 2, 7], className: '' },
    { name: 'sus4', intervals: [0, 5, 7], className: '' },
    { name: '9', intervals: [0, 4, 7, 10, 14], className: '' },
    { name: 'add9', intervals: [0, 4, 7, 14], className: '' },
    { name: '6', intervals: [0, 4, 7, 9], className: '' },
    { name: 'min6', intervals: [0, 3, 7, 9], className: 'minor' }
];

var rootNotes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];

function initChords() {
    var grid = document.getElementById('chord-grid');
    if (!grid) return;

    grid.innerHTML = '';

    // Create a row for each root note
    for (var r = 0; r < rootNotes.length; r++) {
        var root = rootNotes[r];
        var row = document.createElement('div');
        row.className = 'chord-row';

        var rootLabel = document.createElement('div');
        rootLabel.className = 'chord-root';
        rootLabel.textContent = root;
        row.appendChild(rootLabel);

        var buttons = document.createElement('div');
        buttons.className = 'chord-buttons';

        for (var c = 0; c < chordTypes.length; c++) {
            var chord = chordTypes[c];
            var btn = document.createElement('button');
            btn.className = 'chord-btn';
            if (chord.className) {
                btn.classList.add(chord.className);
            }
            btn.textContent = chord.name;
            btn.setAttribute('data-root', r);
            btn.setAttribute('data-chord', c);
            btn.addEventListener('click', onChordClick);
            buttons.appendChild(btn);
        }

        row.appendChild(buttons);
        grid.appendChild(row);
    }
}

function onChordClick(e) {
    var rootIndex = parseInt(e.target.getAttribute('data-root'));
    var chordIndex = parseInt(e.target.getAttribute('data-chord'));

    var chord = chordTypes[chordIndex];
    var octave = parseInt(document.getElementById('chord-octave').value) || 3;

    // Get the current step from selection or focused step
    var targetStep = state.focusedStep >= 0 ? state.focusedStep : 0;

    // Get the track for preview from the current pattern's track
    var previewTrack = state.selectedClip ? state.selectedClip.trackId : 0;

    // Calculate the notes for this chord
    var chordNotes = [];
    for (var i = 0; i < chord.intervals.length; i++) {
        var midiNote = rootIndex + (octave * 12) + chord.intervals[i];
        var noteOctave = Math.floor(midiNote / 12);
        var noteIndex = midiNote % 12;
        var noteName = noteNames[noteIndex] + '-' + noteOctave;
        chordNotes.push(noteName);
    }

    // Always preview the chord
    playChordPreview(chordNotes, previewTrack);

    // Only insert into pattern if recording is enabled
    if (state.isRecording) {
        insertChordNotes(targetStep, chordNotes);
    }
}

function insertChordNotes(step, notes) {
    var pattern = getCurrentPattern();
    var patternIndex = getCurrentPatternIndex();

    if (!pattern) {
        consoleLog('No pattern selected for chord insert');
        return;
    }

    var currentNoteCols = pattern.noteColumns || 1;
    var neededColumns = notes.length;
    var needsRebuild = false;

    // Add note columns if needed to fit the chord
    if (neededColumns > currentNoteCols) {
        while (pattern.noteColumns < neededColumns) {
            addNoteColumn(patternIndex);
        }
        needsRebuild = true;
    }

    // Ensure step data exists
    if (!pattern.data[step]) {
        pattern.data[step] = { columns: [] };
    }
    if (!pattern.data[step].columns) {
        pattern.data[step].columns = [];
    }
    while (pattern.data[step].columns.length < neededColumns) {
        pattern.data[step].columns.push({ note: '', amp: '', fx: [] });
    }

    // Insert the chord notes into each note column
    var stepData = pattern.data[step];
    for (var i = 0; i < notes.length; i++) {
        stepData.columns[i].note = notes[i];
        // Don't overwrite existing amp values
        if (!stepData.columns[i].amp) {
            stepData.columns[i].amp = 'FF';
        }
    }

    markPatternDirty(patternIndex);

    if (needsRebuild) {
        invalidatePatternCache();
        renderTrackerGrid(true);
    } else {
        // Update display cells directly
        for (var i = 0; i < notes.length; i++) {
            var noteCell = findCellElement(step, i, 0, 'note');
            var ampCell = findCellElement(step, i, 0, 'amp');
            if (noteCell) updateCellDisplay(noteCell, 'note', stepData.columns[i].note);
            if (ampCell) updateCellDisplay(ampCell, 'amp', stepData.columns[i].amp);
        }
    }

    // Move down by edit step
    if (state.editStep > 0) {
        navigateSelection(0, state.editStep);
    }

    consoleLog('Inserted chord at step ' + step + ': ' + notes.join(', '));
}

// ============================================
// CLIPBOARD
// ============================================

function clearSelectionData() {
    if (selectedCells.length === 0) return;

    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();

    for (var i = 0; i < selectedCells.length; i++) {
        var cell = selectedCells[i];
        var info = getCellInfo(cell);
        if (!info) continue;

        var stepData = pattern.data[info.step];
        if (!stepData || !stepData.columns) continue;

        var colData = stepData.columns[info.noteCol];
        if (!colData) continue;

        if (info.type === 'note') {
            colData.note = '';
            updateCellDisplay(cell, 'note', '');
        } else if (info.type === 'amp') {
            colData.amp = '';
            updateCellDisplay(cell, 'amp', '');
        } else if (info.type === 'fx') {
            if (colData.fx) {
                colData.fx[info.col] = '';
            }
            updateCellDisplay(cell, 'fx', '');
        }
    }

    markPatternDirty(patternIndex);
    consoleLog('Cleared ' + selectedCells.length + ' cell(s)');
}

function copySelection() {
    if (selectedCells.length === 0) return;

    var pattern = getCurrentPattern();

    var minStep = Math.min(selection.startStep, selection.endStep);
    var maxStep = Math.max(selection.startStep, selection.endStep);
    var minNoteCol = Math.min(selection.startNoteCol || 0, selection.endNoteCol || 0);
    var maxNoteCol = Math.max(selection.startNoteCol || 0, selection.endNoteCol || 0);

    // Copy column data for selected steps
    var data = [];

    for (var step = minStep; step <= maxStep; step++) {
        var stepData = pattern.data[step];
        if (!stepData || !stepData.columns) continue;

        var row = [];
        for (var nc = minNoteCol; nc <= maxNoteCol; nc++) {
            var colData = stepData.columns[nc] || { note: '', amp: '', fx: [] };
            row.push({
                note: colData.note,
                amp: colData.amp,
                fx: colData.fx ? colData.fx.slice() : []
            });
        }
        data.push(row);
    }

    clipboard = {
        type: 'columns',
        data: data,
        isRange: true,
        width: maxNoteCol - minNoteCol + 1,
        height: maxStep - minStep + 1
    };

    consoleLog('Copied ' + clipboard.height + ' steps x ' + clipboard.width + ' columns');
}

function cutSelection() {
    copySelection();
    clearSelectionData();
}

function pasteAtSelection() {
    if (!clipboard.data || selectedCells.length === 0) {
        consoleLog('Nothing to paste');
        return;
    }

    var startCell = selectedCells[0];
    var startInfo = getCellInfo(startCell);
    if (!startInfo) return;

    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();

    // Handle 'columns' type clipboard (new single-track format)
    if (clipboard.type === 'columns' && clipboard.isRange) {
        var count = 0;
        var needsRebuild = false;

        // First pass: ensure pattern has enough note columns
        var targetMaxCol = startInfo.noteCol + clipboard.width - 1;
        if (targetMaxCol >= (pattern.noteColumns || 1)) {
            while ((pattern.noteColumns || 1) <= targetMaxCol) {
                addNoteColumn(patternIndex);
            }
            needsRebuild = true;
        }

        if (needsRebuild) {
            invalidatePatternCache();
        }

        // Second pass: paste the data
        for (var rowIdx = 0; rowIdx < clipboard.height; rowIdx++) {
            var targetStep = startInfo.step + rowIdx;
            if (targetStep >= pattern.steps) break;

            var stepData = pattern.data[targetStep];
            if (!stepData || !stepData.columns) continue;

            for (var colIdx = 0; colIdx < clipboard.width; colIdx++) {
                var targetNoteCol = startInfo.noteCol + colIdx;
                if (targetNoteCol >= stepData.columns.length) continue;

                var cellData = clipboard.data[rowIdx][colIdx];
                var colData = stepData.columns[targetNoteCol];

                colData.note = cellData.note;
                colData.amp = cellData.amp;
                if (cellData.fx) {
                    colData.fx = cellData.fx.slice();
                }

                count++;
            }
        }

        renderTrackerGrid(true);
        consoleLog('Pasted ' + count + ' cells');
        markPatternDirty(patternIndex);
        return;
    }

    // Single cell paste
    if (!clipboard.isRange) {
        var stepData = pattern.data[startInfo.step];
        if (!stepData || !stepData.columns) return;

        var colData = stepData.columns[startInfo.noteCol];
        if (!colData) return;

        if (clipboard.type === 'note') {
            colData.note = clipboard.data.note;
            colData.amp = clipboard.data.amp;
        } else if (clipboard.type === 'fx') {
            if (!colData.fx) colData.fx = [];
            colData.fx[startInfo.col] = clipboard.data;
        }

        renderTrackerGrid(true);
        consoleLog('Pasted');
        markPatternDirty(patternIndex);
    }
}

// ============================================
// NOTE HELPERS
// ============================================

function parseNote(noteStr) {
    if (!noteStr || noteStr === '---' || noteStr === '' || noteStr === NOTE_OFF) return null;

    var freq = parseFloat(noteStr);
    if (!isNaN(freq) && freq > 0) return freq;

    var match = noteStr.match(/^([A-Ga-g])([#b]?)-?(\d+)$/);
    if (!match) return null;

    var noteMap = { 'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11 };
    var noteName = match[1].toUpperCase();
    var modifier = match[2];
    var octave = parseInt(match[3]);

    var semitone = noteMap[noteName];
    if (modifier === '#') semitone++;
    else if (modifier === 'b') semitone--;

    var midiNote = (octave + 1) * 12 + semitone;
    return 440 * Math.pow(2, (midiNote - 69) / 12);
}

function parseAmplitude(ampStr) {
    if (!ampStr || ampStr === '--' || ampStr === '') return 0.5;
    // Amp column is hex (00-FF): 00=silent, FF=full volume (1.0)
    var val = parseInt(ampStr, 16);
    if (isNaN(val)) return 0.5;
    return val / 255;  // 0xFF (255) = 1.0 (full volume)
}

function semitoneToNoteName(semitone, octave) {
    var noteIdx = semitone % 12;
    var noteOctave = octave + Math.floor(semitone / 12);
    return noteNames[noteIdx] + '-' + noteOctave;
}

// ============================================
// RECORDING
// ============================================

function toggleRecording() {
    state.isRecording = !state.isRecording;

    var btn = document.getElementById('btn-record');
    if (state.isRecording) {
        btn.classList.add('recording');
        consoleLog('Recording ON (Oct: ' + state.baseOctave + ')');
        setStatus('RECORDING - Octave: ' + state.baseOctave);
    } else {
        btn.classList.remove('recording');
        consoleLog('Recording OFF');
        setStatus('Recording stopped');
    }
}

function recordNote(noteName) {
    if (!state.isRecording) return;

    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    var noteCol = state.focusedNoteCol || 0;

    // Ensure step data exists
    var stepData = pattern.data[state.focusedStep];
    if (!stepData || !stepData.columns) return;

    // Ensure note column exists
    while (stepData.columns.length <= noteCol) {
        stepData.columns.push({ note: '', amp: '', fx: [] });
    }

    var colData = stepData.columns[noteCol];
    colData.note = noteName;
    if (!colData.amp) {
        colData.amp = 'FF';  // Default velocity (full volume)
    }

    markPatternDirty(patternIndex);

    // Update display
    var noteCell = findCellElement(state.focusedStep, noteCol, 0, 'note');
    var ampCell = findCellElement(state.focusedStep, noteCol, 0, 'amp');
    if (noteCell) updateCellDisplay(noteCell, 'note', noteName);
    if (ampCell && ampCell.textContent === '--') updateCellDisplay(ampCell, 'amp', 'FF');

    // Move down by edit step (skip if editStep is 0)
    if (state.editStep > 0) {
        state.focusedStep = Math.min(state.focusedStep + state.editStep, pattern.steps - 1);

        var nextCell = findCellElement(state.focusedStep, noteCol, 0, 'note');
        if (nextCell) {
            selectCell(nextCell);
            nextCell.scrollIntoView({ block: 'nearest', behavior: 'auto' });
        }
    }
}

// ============================================
// PLAYBACK
// ============================================

function isTrackAudible(trackIdx) {
    if (trackIdx < 0 || trackIdx >= state.tracks.length) return false;

    // Check if any track is soloed
    var anySolo = false;
    for (var i = 0; i < state.tracks.length; i++) {
        if (state.tracks[i].soloed) {
            anySolo = true;
            break;
        }
    }

    if (anySolo) {
        return state.tracks[trackIdx].soloed;
    }
    return !state.tracks[trackIdx].muted;
}

function updateTrackAudibilityVisuals() {
    var tracks = document.querySelectorAll('.track[data-track]');
    for (var i = 0; i < tracks.length; i++) {
        var trackIdx = parseInt(tracks[i].getAttribute('data-track'));
        var audible = isTrackAudible(trackIdx);
        tracks[i].classList.toggle('silenced', !audible);
    }
}

function updateNoteColDisplay() {
    var pattern = getCurrentPattern();
    var display = document.getElementById('note-col-count');
    if (display && pattern) {
        display.textContent = pattern.noteColumns || 1;
    }
}

function updatePlayhead(step) {
    var prev = document.querySelectorAll('.track-row.playing');
    for (var i = 0; i < prev.length; i++) {
        prev[i].classList.remove('playing');
    }

    var rows = document.querySelectorAll('.track-row[data-step="' + step + '"]');
    for (var i = 0; i < rows.length; i++) {
        rows[i].classList.add('playing');
    }
}

// Legacy getCurrentVisualPosition removed - using clip-based visual updates

function visualUpdateLoop() {
    if (!state.isPlaying) {
        pendingVisualUpdate = null;
        return;
    }

    // Update timeline playhead position
    updateTimelinePlayhead();

    // If a clip is selected, show the current step in that pattern
    if (state.selectedClip && state.selectedClip.trackId !== null && state.selectedClip.clipId !== null) {
        var track = state.tracks[state.selectedClip.trackId];
        if (track) {
            for (var i = 0; i < track.clips.length; i++) {
                if (track.clips[i].id === state.selectedClip.clipId) {
                    var clip = track.clips[i];
                    // Check if current beat is within this clip
                    if (state.currentBeat >= clip.startBeat && state.currentBeat < getClipEndBeat(clip)) {
                        var stepInfo = beatToPatternStep(clip, state.currentBeat);
                        if (stepInfo.step !== lastPlayedStep) {
                            updatePlayhead(stepInfo.step);
                            lastPlayedStep = stepInfo.step;
                        }
                    }
                    break;
                }
            }
        }
    }

    pendingVisualUpdate = requestAnimationFrame(visualUpdateLoop);
}

// Legacy sequence-based functions removed - using clip-based playback only

// Schedule notes from clips at the current beat position
function scheduleClipsAtBeat(beat, scheduledTime) {
    if (!state.csoundReady || !state.isPlaying) return;

    var p2 = Math.max(0, scheduledTime - audioCtx.currentTime);

    // Find all clips active at this beat
    var activeClips = getClipsAtBeat(beat);

    for (var i = 0; i < activeClips.length; i++) {
        var trackId = activeClips[i].trackId;
        var clip = activeClips[i].clip;

        if (!isTrackAudible(trackId)) continue;

        var pattern = state.patterns[clip.patternId];
        if (!pattern) continue;

        var patternLpb = pattern.lpb || state.lpb;
        var stepInfo = beatToPatternStep(clip, beat);
        var step = stepInfo.step;
        var loopCount = stepInfo.loopCount;

        if (step < 0 || step >= pattern.steps) continue;

        // Check if we already played this step (prevent duplicates at different LPBs)
        var clipKey = trackId + '_' + clip.id;
        var lastInfo = clipLastStep[clipKey];
        if (lastInfo && lastInfo.step === step && lastInfo.loopCount === loopCount) {
            // Same step and loop - already triggered, skip
            continue;
        }
        // Update tracking
        clipLastStep[clipKey] = { step: step, loopCount: loopCount };

        // Get step data from pattern
        var stepData = pattern.data ? pattern.data[step] : null;
        if (!stepData || !stepData.columns) continue;

        var stepDuration = 60 / (state.bpm * patternLpb);
        // Use pattern's instrument setting (1-128), not track ID
        var instrNum = pattern.instrument || 1;

        // Process each note column
        for (var nc = 0; nc < stepData.columns.length; nc++) {
            var colData = stepData.columns[nc];
            if (!colData) continue;

            // Voice key is per-track per-noteCol (persists across clips on same track)
            var voiceKey = trackId + '_' + nc;

            // Handle NOTE_OFF - turn off the active voice in this column
            if (colData.note === NOTE_OFF) {
                if (activeVoices[voiceKey]) {
                    var voice = activeVoices[voiceKey];
                    // Use instrument 998 (note killer) with turnoff2 for reliable note-off
                    // p4 = fractional instrument number to turn off
                    var offMsg = 'i 998 ' + p2.toFixed(4) + ' 0.01 ' + voice.instrInstance;
                    try {
                        csound.inputMessage(offMsg);
                        logVoice('OFF', voiceKey, { instr: voice.instrInstance, note: voice.noteName, msg: offMsg });
                    } catch (err) {
                        logVoice('OFF-ERROR', voiceKey, { error: err.message || err });
                    }
                    delete activeVoices[voiceKey];
                } else {
                    logVoice('OFF-SKIP', voiceKey, { reason: 'no active voice' });
                }
                continue;
            }

            // Handle new note
            var freq = parseNote(colData.note);
            if (freq !== null) {
                // Check if there's already a voice in this column that needs to be turned off
                var hadOldVoice = false;
                if (activeVoices[voiceKey]) {
                    hadOldVoice = true;
                    var oldVoice = activeVoices[voiceKey];
                    // Use instrument 998 (note killer) with turnoff2 for reliable note-off
                    var offMsg = 'i 998 ' + p2.toFixed(4) + ' 0.01 ' + oldVoice.instrInstance;
                    try {
                        csound.inputMessage(offMsg);
                        logVoice('OFF-REPLACE', voiceKey, { oldInstr: oldVoice.instrInstance, oldNote: oldVoice.noteName, msg: offMsg });
                    } catch (err) {
                        logVoice('OFF-REPLACE-ERROR', voiceKey, { error: err.message || err });
                    }
                    // Explicitly delete old voice before creating new one
                    delete activeVoices[voiceKey];
                }

                // Allocate new unique fractional instance
                var instrInstance = instrNum + '.' + voiceCounter.toString().padStart(3, '0');
                voiceCounter++;
                if (voiceCounter > 999) voiceCounter = 1;

                var amp = parseAmplitude(colData.amp);
                // Use -1 duration for held notes (will be turned off by NOTE_OFF or new note)
                // Add offset (0.005s = 5ms) to ensure turn-off fully processes before note-on when replacing
                var noteOnP2 = hadOldVoice ? (p2 + 0.005).toFixed(4) : p2.toFixed(4);
                var pfields = [instrInstance, noteOnP2, -1, freq.toFixed(4), amp.toFixed(4)];

                // Add FX columns as p6, p7, etc.
                var fxCount = (colData.fx || []).length;
                for (var fx = 0; fx < fxCount; fx++) {
                    var fxStr = colData.fx[fx];
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                    }
                    pfields.push(fxVal);
                }

                var onMsg = 'i ' + pfields.join(' ');
                try {
                    csound.inputMessage(onMsg);
                    logVoice('ON', voiceKey, { instr: instrInstance, note: colData.note, freq: freq.toFixed(2), msg: onMsg });
                } catch (err) {
                    logVoice('ON-ERROR', voiceKey, { error: err.message || err });
                }

                // Track this voice for note-off and FX updates
                activeVoices[voiceKey] = {
                    instrInstance: instrInstance,
                    instrNum: instrNum,
                    freq: freq,
                    amp: amp,
                    fxCount: fxCount,
                    noteName: colData.note
                };
            }
            // No note or empty note - check for FX update on active voice
            else if ((!colData.note || colData.note === '') && activeVoices[voiceKey]) {
                // Check if there are any FX values to send
                var hasFx = false;
                var fxValues = [];
                var voice = activeVoices[voiceKey];
                var fxCount = Math.max((colData.fx || []).length, voice.fxCount || 0);

                for (var fx = 0; fx < fxCount; fx++) {
                    var fxStr = colData.fx && colData.fx[fx] ? colData.fx[fx] : '';
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                        hasFx = true;
                    }
                    fxValues.push(fxVal);
                }

                // Send FX update if there are any non-zero FX values
                if (hasFx) {
                    // p3 = -1 means update parameters for held note
                    var pfields = [voice.instrInstance, p2.toFixed(4), -1, voice.freq.toFixed(4), voice.amp.toFixed(4)];
                    for (var fx = 0; fx < fxValues.length; fx++) {
                        pfields.push(fxValues[fx]);
                    }
                    var fxMsg = 'i ' + pfields.join(' ');
                    try {
                        csound.inputMessage(fxMsg);
                        logVoice('FX-UPDATE', voiceKey, { instr: voice.instrInstance, note: voice.noteName, fx: fxValues.join(',') });
                    } catch (err) {
                        logVoice('FX-UPDATE-ERROR', voiceKey, { error: err.message || err });
                    }
                }
            }
        }
    }
}

// Get note duration in steps for a specific note column
function getNoteDurationStepsSingle(pattern, startStep, noteColIndex) {
    // Find the next note or note-off to determine duration
    for (var step = startStep + 1; step < pattern.steps; step++) {
        var stepData = pattern.data[step];
        if (stepData && stepData.columns && stepData.columns[noteColIndex]) {
            var colData = stepData.columns[noteColIndex];
            if (colData.note && colData.note !== '') {
                return step - startStep;
            }
        }
    }
    // No next note found, play until pattern end
    return -1;
}

// Get the maximum LPB from all patterns (for scheduling resolution)
function getMaxLpb() {
    var maxLpb = state.lpb;
    for (var i = 0; i < state.patterns.length; i++) {
        var patternLpb = state.patterns[i].lpb || state.lpb;
        if (patternLpb > maxLpb) maxLpb = patternLpb;
    }
    return maxLpb;
}

// Lookahead scheduler - uses Web Audio clock for sample-accurate timing
// Schedules notes ahead of time to prevent timing jitter from main thread
function scheduler() {
    if (!state.isPlaying || !audioCtx) return;

    // Use highest LPB from all patterns for finest resolution
    var schedulerLpb = getMaxLpb() || state.lpb;
    var stepDuration = 60 / (state.bpm * schedulerLpb);

    // Schedule all steps that fall within our lookahead window
    while (nextStepTime < audioCtx.currentTime + scheduleAheadTime) {
        // DAW-style clip-based playback - each pattern uses its own LPB internally
        scheduleClipsAtBeat(state.currentBeat, nextStepTime);
        state.currentBeat += 1 / schedulerLpb;  // Advance by finest step unit

        // Check loop region or wrap at timeline end
        if (state.timeline.loopEnabled) {
            // Loop within the loop region
            if (state.currentBeat >= state.timeline.loopEnd) {
                // Turn off all held notes before looping
                turnOffAllActiveVoices(nextStepTime - audioCtx.currentTime);
                state.currentBeat = state.timeline.loopStart;
                clipLastStep = {};  // Reset clip tracking for loop
                activeVoices = {};  // Reset active voices for loop
                voiceCounter = 1;
            }
        } else {
            // Wrap around at timeline end (or arrangement end)
            var arrangementEnd = getMaxClipEndBeat();
            var wrapPoint = arrangementEnd > 0 ? snapToMeasureEnd(arrangementEnd) : state.timeline.totalBeats;
            if (state.currentBeat >= wrapPoint) {
                // Turn off all held notes before wrapping
                turnOffAllActiveVoices(nextStepTime - audioCtx.currentTime);
                state.currentBeat = 0;
                clipLastStep = {};  // Reset clip tracking
                activeVoices = {};  // Reset active voices
                voiceCounter = 1;
            }
        }
        nextStepTime += stepDuration;
    }

    // Schedule next check
    schedulerTimerId = setTimeout(scheduler, lookahead);
}

function startPlayback() {
    if (!state.csoundReady || state.isPlaying) return;

    // Check for AudioContext
    if (!audioCtx) {
        consoleLog('Warning: AudioContext not available, cannot play');
        return;
    }

    state.isPlaying = true;
    // Start from loop start if loop is enabled, otherwise from beginning
    state.currentBeat = state.timeline.loopEnabled ? state.timeline.loopStart : 0;
    clipLastStep = {};  // Reset clip step tracking
    activeVoices = {};  // Reset active voices
    voiceCounter = 1;  // Reset voice counter
    logVoice('PLAYBACK-START', 'all', { beat: state.currentBeat, voiceCounter: voiceCounter });

    // Show timeline playhead
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) playhead.style.display = 'block';

    prerenderAllPatterns();

    // Initialize precise timing using Web Audio clock
    playbackStartTime = audioCtx.currentTime;
    nextStepTime = audioCtx.currentTime;
    // Start lookahead scheduler (runs every 25ms, schedules 100ms ahead)
    scheduler();

    // Visual updates are decoupled from audio - use requestAnimationFrame
    pendingVisualUpdate = requestAnimationFrame(visualUpdateLoop);

    document.getElementById('btn-play').disabled = true;
    document.getElementById('btn-stop').disabled = false;
    consoleLog('Playing');
    setStatus('Playing...');
}

// Panic: kill ALL notes on ALL voices of ALL instruments using turnoff2
// Triggers instr 999 which uses turnoff2 with mode 0 (all instances)
function killAllNotes() {
    if (!state.csoundReady) return;
    try {
        csound.inputMessage('i 999 0 0.1');
    } catch (err) {}
}

function stopPlayback() {
    // If already stopped, second click kills all notes (panic)
    if (!state.isPlaying) {
        killAllNotes();
        consoleLog('All notes off');
        return;
    }

    state.isPlaying = false;

    // Stop lookahead scheduler
    if (schedulerTimerId) {
        clearTimeout(schedulerTimerId);
        schedulerTimerId = null;
    }

    // Also clear fallback interval if used
    if (state.playInterval) {
        clearInterval(state.playInterval);
        state.playInterval = null;
    }

    if (pendingVisualUpdate) {
        cancelAnimationFrame(pendingVisualUpdate);
        pendingVisualUpdate = null;
    }

    // Turn off all tracked active voices first
    turnOffAllActiveVoices(0);

    // Then use panic to kill any remaining notes
    killAllNotes();

    // Clear active voices tracking
    activeVoices = {};
    voiceCounter = 1;

    var rows = document.querySelectorAll('.track-row.playing');
    for (var i = 0; i < rows.length; i++) {
        rows[i].classList.remove('playing');
    }

    // Hide timeline playhead
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) playhead.style.display = 'none';

    document.getElementById('btn-play').disabled = false;
    // Keep stop button enabled for "panic" functionality (second click kills all notes)
    consoleLog('Stopped');
    setStatus('Stopped');
}

// ============================================
// SAVE/LOAD
// ============================================

// Convert ArrayBuffer to base64 string for JSON serialization
function arrayBufferToBase64(buffer) {
    var bytes = new Uint8Array(buffer);
    var binary = '';
    var chunkSize = 8192;
    for (var i = 0; i < bytes.length; i += chunkSize) {
        var chunk = bytes.subarray(i, Math.min(i + chunkSize, bytes.length));
        binary += String.fromCharCode.apply(null, chunk);
    }
    return btoa(binary);
}

// Convert base64 string back to ArrayBuffer
function base64ToArrayBuffer(base64) {
    var binary = atob(base64);
    var bytes = new Uint8Array(binary.length);
    for (var i = 0; i < binary.length; i++) {
        bytes[i] = binary.charCodeAt(i);
    }
    return bytes.buffer;
}

function saveSong() {
    saveCurrentInstrument();
    saveOpcodes();

    // Serialize ftable pool with base64-encoded audio data
    var serializedFtables = state.ftablePool.map(function(item) {
        // Find the matching sample in state.samples for the raw data
        var sample = state.samples.find(function(s) { return s.tableNum === item.tableNum; });
        return {
            tableNum: item.tableNum,
            name: item.name,
            libraryId: item.libraryId,
            rawDataB64: sample && sample.rawData ? arrayBufferToBase64(sample.rawData) : null,
            fileName: sample ? sample.fileName : null
        };
    });

    var songData = {
        version: 6,  // v6: includes sample data in save file
        bpm: state.bpm,
        lpb: state.lpb,
        timeSignature: state.timeSignature,
        quantize: state.quantize,
        patterns: state.patterns.map(function(p) {
            return {
                id: p.id,
                name: p.name,
                type: p.type,
                trackId: p.trackId,
                instrument: p.instrument || 1,
                steps: p.steps,
                lpb: p.lpb,
                noteColumns: p.noteColumns,
                data: p.data
            };
        }),
        tracks: state.tracks.map(function(t) {
            return {
                id: t.id,
                visible: t.visible,
                muted: t.muted,
                soloed: t.soloed,
                volume: t.volume,
                pan: t.pan,
                name: t.name,
                clips: t.clips
            };
        }),
        instruments: state.instruments,
        opcodes: state.opcodes,
        timeline: state.timeline,
        ftablePool: serializedFtables,
        usedFtables: state.usedFtables,
        nextFtableNum: state.nextFtableNum
    };

    var json = JSON.stringify(songData);
    var blob = new Blob([json], { type: 'application/octet-stream' });
    var url = URL.createObjectURL(blob);

    var a = document.createElement('a');
    a.href = url;
    a.download = 'song.cst';
    a.click();

    URL.revokeObjectURL(url);

    var sizeKB = (json.length / 1024).toFixed(1);
    consoleLog('Song saved (v6 format, ' + sizeKB + 'KB, ' + serializedFtables.length + ' ftables)');
}

function loadSong(file) {
    var reader = new FileReader();
    reader.onload = function(e) {
        try {
            var songData = JSON.parse(e.target.result);
            var version = songData.version || 1;

            state.bpm = songData.bpm || 120;
            state.lpb = songData.lpb || 4;
            state.timeSignature = songData.timeSignature || { num: 4, den: 4 };
            state.quantize = songData.quantize || '1/16';
            state.patterns = songData.patterns || [];
            state.instruments = songData.instruments || defaultInstruments.slice();
            state.opcodes = songData.opcodes || '';
            state.currentInstrument = 0;
            state.selectedClip = { trackId: null, clipId: null };

            // Handle track/clip migration based on version
            if (version < 5) {
                // Migrate from sequence-based to clip-based
                var sequence = songData.sequence || [0];
                var oldTracks = songData.tracks || [];
                state.tracks = [];

                // Create at least one track
                addTrack();

                // If there are old tracks with clips, use them
                for (var i = 0; i < oldTracks.length; i++) {
                    if (oldTracks[i] && oldTracks[i].clips && oldTracks[i].clips.length > 0) {
                        if (i >= state.tracks.length) addTrack();
                        var t = state.tracks[i];
                        t.muted = oldTracks[i].muted || false;
                        t.soloed = oldTracks[i].soloed || false;
                        t.volume = oldTracks[i].volume !== undefined ? oldTracks[i].volume : 1.0;
                        t.pan = oldTracks[i].pan || 0;
                        t.name = oldTracks[i].name || ('Track ' + (i + 1));
                        t.clips = oldTracks[i].clips || [];
                    }
                }

                // If no clips exist, migrate sequence to clips on track 0
                var hasClips = false;
                for (var t = 0; t < state.tracks.length; t++) {
                    if (state.tracks[t].clips.length > 0) hasClips = true;
                }
                if (!hasClips && sequence.length > 0 && state.patterns.length > 0) {
                    var beat = 0;
                    for (var s = 0; s < sequence.length; s++) {
                        var patternId = sequence[s];
                        if (patternId < state.patterns.length) {
                            var pattern = state.patterns[patternId];
                            var patternBeats = pattern.steps / (pattern.lpb || state.lpb);
                            addClipToTrack(0, patternId, beat, 1);
                            beat += patternBeats;
                        }
                    }
                }

                // Ensure patterns have instrument field
                for (var p = 0; p < state.patterns.length; p++) {
                    if (!state.patterns[p].instrument) {
                        state.patterns[p].instrument = 1;
                    }
                }
                state.timeline = songData.timeline || { zoom: 1, scrollX: 0, totalBeats: 4000 };
                consoleLog('Migrated from v' + version + ' format');
            } else {
                // v5 format - pure DAW with clips only
                var loadedTracks = songData.tracks || [];
                state.tracks = [];
                for (var i = 0; i < loadedTracks.length; i++) {
                    addTrack();
                    var t = state.tracks[i];
                    t.muted = loadedTracks[i].muted || false;
                    t.soloed = loadedTracks[i].soloed || false;
                    t.volume = loadedTracks[i].volume !== undefined ? loadedTracks[i].volume : 1.0;
                    t.pan = loadedTracks[i].pan || 0;
                    t.name = loadedTracks[i].name || ('Track ' + (i + 1));
                    t.clips = loadedTracks[i].clips || [];
                }
                if (state.tracks.length === 0) addTrack();
                state.timeline = songData.timeline || { zoom: 1, scrollX: 0, totalBeats: 4000 };
            }

            // Ensure instruments array has 128 entries
            while (state.instruments.length < 128) {
                state.instruments.push('instr ' + (state.instruments.length + 1) + '\nendin');
            }

            // Restore ftable pool from save data (v6+)
            state.ftablePool = [];
            state.usedFtables = songData.usedFtables || {};
            state.nextFtableNum = songData.nextFtableNum || 100;
            state.samples = [];

            if (songData.ftablePool && songData.ftablePool.length > 0) {
                songData.ftablePool.forEach(function(item) {
                    state.ftablePool.push({
                        tableNum: item.tableNum,
                        name: item.name,
                        libraryId: item.libraryId
                    });

                    // Restore sample data for Csound
                    if (item.rawDataB64) {
                        var rawData = base64ToArrayBuffer(item.rawDataB64);
                        state.samples.push({
                            tableNum: item.tableNum,
                            fileName: item.fileName || ('sample_ft' + item.tableNum + '.wav'),
                            rawData: rawData,
                            audioBuffer: null
                        });
                    }
                });
                consoleLog('Restored ' + state.ftablePool.length + ' ftables');

                // Reload ftables into Csound after it's ready
                if (state.csoundReady) {
                    loadRestoredFtablesIntoCsound();
                }
            }

            document.getElementById('bpm').value = state.bpm;

            initInstrumentTabs();
            document.getElementById('opcodes-editor').value = state.opcodes;

            invalidatePatternCache();
            prerenderAllPatterns();

            renderTrackerGrid(true);
            renderTrackList();
            renderTimeline();
            renderTimelineRuler();
            renderSampleLibrary();
            renderFtablePool();

            if (state.csoundReady) {
                compileAllInstruments();  // Full recompile after loading new song
            }

            consoleLog('Song loaded (v' + version + ' format)');
            setStatus('Song loaded');
        } catch (err) {
            consoleLog('Load error: ' + err.message);
        }
    };
    reader.readAsText(file);
}

// Load a demo file by number (1.cst, 2.cst, etc.)
async function loadDemo(demoNum) {
    try {
        consoleLog('Loading demo ' + demoNum + '...');
        setStatus('Loading demo ' + demoNum + '...');

        var response = await fetch(demoNum + '.cst');
        if (!response.ok) {
            throw new Error('Demo file not found: ' + demoNum + '.cst');
        }

        var text = await response.text();
        var songData = JSON.parse(text);
        var version = songData.version || 1;

        state.bpm = songData.bpm || 120;
        state.lpb = songData.lpb || 4;
        state.timeSignature = songData.timeSignature || { num: 4, den: 4 };
        state.quantize = songData.quantize || '1/16';
        state.patterns = songData.patterns || [];
        state.instruments = songData.instruments || defaultInstruments.slice();
        state.opcodes = songData.opcodes || '';
        state.currentInstrument = 0;
        state.selectedClip = { trackId: null, clipId: null };

        // Handle track/clip migration based on version
        if (version < 5) {
            // Migrate from sequence-based to clip-based
            var sequence = songData.sequence || [0];
            var oldTracks = songData.tracks || [];
            state.tracks = [];
            addTrack();

            // If there are old tracks with clips, use them
            for (var i = 0; i < oldTracks.length; i++) {
                if (oldTracks[i] && oldTracks[i].clips && oldTracks[i].clips.length > 0) {
                    if (i >= state.tracks.length) addTrack();
                    var t = state.tracks[i];
                    t.muted = oldTracks[i].muted || false;
                    t.soloed = oldTracks[i].soloed || false;
                    t.volume = oldTracks[i].volume !== undefined ? oldTracks[i].volume : 1.0;
                    t.pan = oldTracks[i].pan || 0;
                    t.name = oldTracks[i].name || ('Track ' + (i + 1));
                    t.clips = oldTracks[i].clips || [];
                }
            }

            // If no clips exist, migrate sequence to clips on track 0
            var hasClips = false;
            for (var t = 0; t < state.tracks.length; t++) {
                if (state.tracks[t].clips.length > 0) hasClips = true;
            }
            if (!hasClips && sequence.length > 0 && state.patterns.length > 0) {
                var beat = 0;
                for (var s = 0; s < sequence.length; s++) {
                    var patternId = sequence[s];
                    if (patternId < state.patterns.length) {
                        var pattern = state.patterns[patternId];
                        var patternBeats = pattern.steps / (pattern.lpb || state.lpb);
                        addClipToTrack(0, patternId, beat, 1);
                        beat += patternBeats;
                    }
                }
            }

            // Ensure patterns have instrument field
            for (var p = 0; p < state.patterns.length; p++) {
                if (!state.patterns[p].instrument) {
                    state.patterns[p].instrument = 1;
                }
            }
            state.timeline = songData.timeline || { zoom: 1, scrollX: 0, totalBeats: 4000 };
        } else {
            // v5 format - pure DAW
            var loadedTracks = songData.tracks || [];
            state.tracks = [];
            for (var i = 0; i < loadedTracks.length; i++) {
                addTrack();
                var t = state.tracks[i];
                t.muted = loadedTracks[i].muted || false;
                t.soloed = loadedTracks[i].soloed || false;
                t.volume = loadedTracks[i].volume !== undefined ? loadedTracks[i].volume : 1.0;
                t.pan = loadedTracks[i].pan || 0;
                t.name = loadedTracks[i].name || ('Track ' + (i + 1));
                t.clips = loadedTracks[i].clips || [];
            }
            if (state.tracks.length === 0) addTrack();
            state.timeline = songData.timeline || { zoom: 1, scrollX: 0, totalBeats: 4000 };
        }

        // Ensure instruments array has 128 entries
        while (state.instruments.length < 128) {
            state.instruments.push('instr ' + (state.instruments.length + 1) + '\nendin');
        }

        // Restore ftable pool from save data (v6+)
        state.ftablePool = [];
        state.usedFtables = songData.usedFtables || {};
        state.nextFtableNum = songData.nextFtableNum || 100;
        state.samples = [];

        if (songData.ftablePool && songData.ftablePool.length > 0) {
            songData.ftablePool.forEach(function(item) {
                state.ftablePool.push({
                    tableNum: item.tableNum,
                    name: item.name,
                    libraryId: item.libraryId
                });
                if (item.rawDataB64) {
                    state.samples.push({
                        tableNum: item.tableNum,
                        fileName: item.fileName || ('sample_ft' + item.tableNum + '.wav'),
                        rawData: base64ToArrayBuffer(item.rawDataB64),
                        audioBuffer: null
                    });
                }
            });

            if (state.csoundReady) {
                loadRestoredFtablesIntoCsound();
            }
        }

        document.getElementById('bpm').value = state.bpm;

        initInstrumentTabs();
        document.getElementById('opcodes-editor').value = state.opcodes;

        invalidatePatternCache();
        prerenderAllPatterns();

        renderTrackerGrid(true);
        renderTrackList();
        renderTimeline();
        renderTimelineRuler();
        renderSampleLibrary();
        renderFtablePool();

        if (state.csoundReady) {
            compileAllInstruments();  // Full recompile after loading demo
        }

        consoleLog('Demo ' + demoNum + ' loaded (v' + version + ')');
        setStatus('Demo ' + demoNum + ' loaded');
    } catch (err) {
        consoleLog('Demo load error: ' + err.message);
        setStatus('Error loading demo');
    }
}

// ============================================
// EXPORT CSD
// ============================================

function exportCSD() {
    saveCurrentInstrument();
    saveOpcodes();

    // Collect ftable sample files for inclusion
    var sampleFiles = [];  // { fileName, rawData }
    var ftableStatements = [];

    // Build f-statements for ftables and collect audio files
    var sorted = state.ftablePool.slice().sort(function(a, b) { return a.tableNum - b.tableNum; });
    for (var fi = 0; fi < sorted.length; fi++) {
        var ftItem = sorted[fi];
        var sample = state.samples.find(function(s) { return s.tableNum === ftItem.tableNum; });
        if (sample && sample.rawData) {
            // Clean filename for filesystem use (strip leading slash from WASM path)
            var cleanName = (ftItem.name || sample.fileName || 'sample_' + ftItem.tableNum + '.wav')
                .replace(/^\//, '').replace(/[^a-zA-Z0-9._-]/g, '_');
            // Ensure .wav extension
            if (!/\.\w+$/.test(cleanName)) cleanName += '.wav';

            sampleFiles.push({
                fileName: cleanName,
                rawData: sample.rawData
            });

            // f tableNum 0 0 1 "samples/filename" 0 0 0
            ftableStatements.push('f ' + ftItem.tableNum + ' 0 0 1 "samples/' + cleanName + '" 0 0 0');
        }
    }

    var csd = '<CsoundSynthesizer>\n<CsOptions>\n-odac -d\n</CsOptions>\n<CsInstruments>\n';
    csd += 'sr = 44100\nksmps = 32\nnchnls = 2\n0dbfs = 1\n\n';
    csd += 'gisine ftgen 1, 0, 16384, 10, 1\n\n';

    if (state.opcodes && state.opcodes.trim()) {
        csd += '; User Defined Opcodes\n' + state.opcodes + '\n\n';
    }

    csd += state.instruments.join('\n\n');
    csd += '\n</CsInstruments>\n<CsScore>\n';

    // Add ftable load statements at the top of the score
    if (ftableStatements.length > 0) {
        csd += '; Load sample ftables\n';
        csd += ftableStatements.join('\n') + '\n\n';
    }

    var events = [];
    var csdVoiceCounter = 1;
    var csdActiveVoices = {};

    var allClipEvents = [];

    for (var trackIdx = 0; trackIdx < state.tracks.length; trackIdx++) {
        var track = state.tracks[trackIdx];
        if (track.muted) continue;

        for (var clipIdx = 0; clipIdx < track.clips.length; clipIdx++) {
            var clip = track.clips[clipIdx];
            var pattern = state.patterns[clip.patternId];
            if (!pattern) continue;

            var patternLpb = pattern.lpb || state.lpb;
            var stepDuration = 60 / (state.bpm * patternLpb);
            var patternBeats = pattern.steps / patternLpb;
            var instrNum = pattern.instrument || 1;

            for (var loop = 0; loop < clip.loopCount; loop++) {
                var loopStartBeat = clip.startBeat + (loop * patternBeats);
                var loopStartTime = loopStartBeat * (60 / state.bpm);

                for (var step = 0; step < pattern.steps; step++) {
                    var stepTime = loopStartTime + (step * stepDuration);
                    var stepData = pattern.data[step];
                    if (!stepData || !stepData.columns) continue;

                    for (var nc = 0; nc < stepData.columns.length; nc++) {
                        var colData = stepData.columns[nc];
                        if (!colData) continue;

                        allClipEvents.push({
                            time: stepTime,
                            trackIdx: trackIdx,
                            noteCol: nc,
                            instrNum: instrNum,
                            colData: colData,
                            stepDuration: stepDuration
                        });
                    }
                }
            }
        }
    }

    allClipEvents.sort(function(a, b) { return a.time - b.time; });

    for (var i = 0; i < allClipEvents.length; i++) {
        var evt = allClipEvents[i];
        var voiceKey = evt.trackIdx + '_' + evt.noteCol;
        var colData = evt.colData;
        var stepTime = evt.time;
        var instrNum = evt.instrNum;

        if (colData.note === NOTE_OFF) {
            if (csdActiveVoices[voiceKey]) {
                var voice = csdActiveVoices[voiceKey];
                var duration = stepTime - voice.start;
                var pfields = [voice.instr, voice.start.toFixed(4), duration.toFixed(4), voice.freq.toFixed(4), voice.amp.toFixed(4)];
                for (var fx = 0; fx < voice.fxValues.length; fx++) {
                    pfields.push(voice.fxValues[fx]);
                }
                events.push('i ' + pfields.join(' '));
                delete csdActiveVoices[voiceKey];
            }
            continue;
        }

        var freq = parseNote(colData.note);
        if (freq !== null) {
            if (csdActiveVoices[voiceKey]) {
                var prevVoice = csdActiveVoices[voiceKey];
                var prevDuration = stepTime - prevVoice.start;
                var pfields = [prevVoice.instr, prevVoice.start.toFixed(4), prevDuration.toFixed(4), prevVoice.freq.toFixed(4), prevVoice.amp.toFixed(4)];
                for (var fx = 0; fx < prevVoice.fxValues.length; fx++) {
                    pfields.push(prevVoice.fxValues[fx]);
                }
                events.push('i ' + pfields.join(' '));
            }

            var instrInstance = instrNum + '.' + csdVoiceCounter.toString().padStart(3, '0');
            csdVoiceCounter++;
            if (csdVoiceCounter > 999) csdVoiceCounter = 1;

            var amp = parseAmplitude(colData.amp);
            var fxValues = [];
            for (var fx = 0; fx < (colData.fx || []).length; fx++) {
                var fxStr = colData.fx[fx];
                var fxVal = 0;
                if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                    fxVal = parseInt(fxStr, 16);
                    if (isNaN(fxVal)) fxVal = 0;
                }
                fxValues.push(fxVal);
            }

            csdActiveVoices[voiceKey] = {
                start: stepTime,
                instr: instrInstance,
                freq: freq,
                amp: amp,
                fxValues: fxValues,
                fxCount: fxValues.length
            };
        }
        else if ((!colData.note || colData.note === '') && csdActiveVoices[voiceKey]) {
            var hasFx = false;
            var fxValues = [];
            var voice = csdActiveVoices[voiceKey];
            var fxCount = Math.max((colData.fx || []).length, voice.fxCount || 0);

            for (var fx = 0; fx < fxCount; fx++) {
                var fxStr = colData.fx && colData.fx[fx] ? colData.fx[fx] : '';
                var fxVal = 0;
                if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                    fxVal = parseInt(fxStr, 16);
                    if (isNaN(fxVal)) fxVal = 0;
                    hasFx = true;
                }
                fxValues.push(fxVal);
            }

            if (hasFx) {
                var pfields = [voice.instr, stepTime.toFixed(4), -1, voice.freq.toFixed(4), voice.amp.toFixed(4)];
                for (var fx = 0; fx < fxValues.length; fx++) {
                    pfields.push(fxValues[fx]);
                }
                events.push('i ' + pfields.join(' '));
            }
        }
    }

    // Finalize all remaining voices
    var totalDuration = state.timeline.totalBeats * (60 / state.bpm);
    for (var voiceKey in csdActiveVoices) {
        var voice = csdActiveVoices[voiceKey];
        var duration = totalDuration - voice.start;
        var defaultStepDuration = 60 / (state.bpm * state.lpb);
        if (duration < defaultStepDuration) duration = defaultStepDuration;

        var pfields = [voice.instr, voice.start.toFixed(4), duration.toFixed(4), voice.freq.toFixed(4), voice.amp.toFixed(4)];
        for (var fx = 0; fx < voice.fxValues.length; fx++) {
            pfields.push(voice.fxValues[fx]);
        }
        events.push('i ' + pfields.join(' '));
    }

    events.sort(function(a, b) {
        var timeA = parseFloat(a.split(' ')[2]);
        var timeB = parseFloat(b.split(' ')[2]);
        return timeA - timeB;
    });

    csd += events.join('\n');
    csd += '\ne\n</CsScore>\n</CsoundSynthesizer>\n';

    // If there are ftable samples, export as ZIP with samples/ folder
    if (sampleFiles.length > 0) {
        var zipFiles = [];
        // Add the CSD file
        var csdBytes = new TextEncoder().encode(csd);
        zipFiles.push({ name: 'composition.csd', data: new Uint8Array(csdBytes) });

        // Add each sample file into samples/ subfolder
        for (var si = 0; si < sampleFiles.length; si++) {
            zipFiles.push({
                name: 'samples/' + sampleFiles[si].fileName,
                data: new Uint8Array(sampleFiles[si].rawData)
            });
        }

        var zipBlob = buildZip(zipFiles);
        var url = URL.createObjectURL(zipBlob);
        var a = document.createElement('a');
        a.href = url;
        a.download = 'composition.zip';
        a.click();
        URL.revokeObjectURL(url);

        var totalSize = (zipBlob.size / 1024).toFixed(1);
        consoleLog('CSD exported as ZIP (' + events.length + ' events, ' + sampleFiles.length + ' samples, ' + totalSize + 'KB)');
    } else {
        // No samples - just export plain CSD
        var blob = new Blob([csd], { type: 'text/plain' });
        var url = URL.createObjectURL(blob);
        var a = document.createElement('a');
        a.href = url;
        a.download = 'composition.csd';
        a.click();
        URL.revokeObjectURL(url);
        consoleLog('CSD exported (' + events.length + ' events)');
    }
}

// Build a ZIP file from an array of { name: string, data: Uint8Array }
// Uses store-only (no compression) which is fine for audio data
function buildZip(files) {
    var localHeaders = [];
    var centralHeaders = [];
    var offset = 0;

    for (var i = 0; i < files.length; i++) {
        var file = files[i];
        var nameBytes = new TextEncoder().encode(file.name);
        var data = file.data;
        var crc = crc32(data);

        // Local file header (30 bytes + name + data)
        var localHeader = new Uint8Array(30 + nameBytes.length);
        var lv = new DataView(localHeader.buffer);
        lv.setUint32(0, 0x04034b50, true);   // Local file header signature
        lv.setUint16(4, 20, true);            // Version needed to extract (2.0)
        lv.setUint16(6, 0, true);             // General purpose bit flag
        lv.setUint16(8, 0, true);             // Compression method: stored
        lv.setUint16(10, 0, true);            // Last mod time
        lv.setUint16(12, 0, true);            // Last mod date
        lv.setUint32(14, crc, true);          // CRC-32
        lv.setUint32(18, data.length, true);  // Compressed size
        lv.setUint32(22, data.length, true);  // Uncompressed size
        lv.setUint16(26, nameBytes.length, true); // File name length
        lv.setUint16(28, 0, true);            // Extra field length
        localHeader.set(nameBytes, 30);

        localHeaders.push({ header: localHeader, data: data, offset: offset });

        // Central directory entry (46 bytes + name)
        var centralHeader = new Uint8Array(46 + nameBytes.length);
        var cv = new DataView(centralHeader.buffer);
        cv.setUint32(0, 0x02014b50, true);   // Central directory signature
        cv.setUint16(4, 20, true);            // Version made by
        cv.setUint16(6, 20, true);            // Version needed
        cv.setUint16(8, 0, true);             // General purpose bit flag
        cv.setUint16(10, 0, true);            // Compression method: stored
        cv.setUint16(12, 0, true);            // Last mod time
        cv.setUint16(14, 0, true);            // Last mod date
        cv.setUint32(16, crc, true);          // CRC-32
        cv.setUint32(20, data.length, true);  // Compressed size
        cv.setUint32(24, data.length, true);  // Uncompressed size
        cv.setUint16(28, nameBytes.length, true); // File name length
        cv.setUint16(30, 0, true);            // Extra field length
        cv.setUint16(32, 0, true);            // File comment length
        cv.setUint16(34, 0, true);            // Disk number start
        cv.setUint16(36, 0, true);            // Internal file attributes
        cv.setUint32(38, 0, true);            // External file attributes
        cv.setUint32(42, offset, true);       // Relative offset of local header
        centralHeader.set(nameBytes, 46);

        centralHeaders.push(centralHeader);

        offset += localHeader.length + data.length;
    }

    // Calculate total size
    var centralDirSize = 0;
    for (var i = 0; i < centralHeaders.length; i++) {
        centralDirSize += centralHeaders[i].length;
    }

    // End of central directory record (22 bytes)
    var eocd = new Uint8Array(22);
    var ev = new DataView(eocd.buffer);
    ev.setUint32(0, 0x06054b50, true);               // EOCD signature
    ev.setUint16(4, 0, true);                         // Disk number
    ev.setUint16(6, 0, true);                         // Disk with central dir
    ev.setUint16(8, files.length, true);              // Entries on this disk
    ev.setUint16(10, files.length, true);             // Total entries
    ev.setUint32(12, centralDirSize, true);           // Size of central directory
    ev.setUint32(16, offset, true);                   // Offset of central directory
    ev.setUint16(20, 0, true);                        // Comment length

    // Assemble the ZIP
    var totalSize = offset + centralDirSize + 22;
    var zipBuffer = new Uint8Array(totalSize);
    var pos = 0;

    // Write local file headers + data
    for (var i = 0; i < localHeaders.length; i++) {
        zipBuffer.set(localHeaders[i].header, pos);
        pos += localHeaders[i].header.length;
        zipBuffer.set(localHeaders[i].data, pos);
        pos += localHeaders[i].data.length;
    }

    // Write central directory
    for (var i = 0; i < centralHeaders.length; i++) {
        zipBuffer.set(centralHeaders[i], pos);
        pos += centralHeaders[i].length;
    }

    // Write EOCD
    zipBuffer.set(eocd, pos);

    return new Blob([zipBuffer], { type: 'application/zip' });
}

// CRC-32 lookup table and function for ZIP
var crc32Table = null;
function crc32(data) {
    if (!crc32Table) {
        crc32Table = new Uint32Array(256);
        for (var i = 0; i < 256; i++) {
            var c = i;
            for (var j = 0; j < 8; j++) {
                c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
            }
            crc32Table[i] = c;
        }
    }
    var crc = 0xFFFFFFFF;
    for (var i = 0; i < data.length; i++) {
        crc = crc32Table[(crc ^ data[i]) & 0xFF] ^ (crc >>> 8);
    }
    return (crc ^ 0xFFFFFFFF) >>> 0;
}

// ============================================
// INSTRUMENT EDITOR
// ============================================

function initMainTabs() {
    var mainTabs = document.querySelectorAll('.main-tab');
    mainTabs.forEach(function(tab) {
        tab.addEventListener('click', function() {
            var tabName = this.getAttribute('data-tab');

            mainTabs.forEach(function(t) { t.classList.remove('active'); });
            this.classList.add('active');

            document.querySelectorAll('.tab-content').forEach(function(content) {
                content.classList.add('hidden');
            });
            document.getElementById('tab-' + tabName).classList.remove('hidden');
        });
    });
}

var currentInstrumentPage = 0;  // 0-7 for instruments 1-128 (16 per page)
var INSTRUMENTS_PER_PAGE = 16;

function initInstrumentTabs() {
    currentInstrumentPage = 0;
    renderInstrumentTabs();
    document.getElementById('code-editor').value = state.instruments[0];
    state.currentInstrument = 0;
}

function renderInstrumentTabs() {
    var container = document.getElementById('instrument-tabs');
    container.innerHTML = '';

    var startIdx = currentInstrumentPage * INSTRUMENTS_PER_PAGE;
    var endIdx = Math.min(startIdx + INSTRUMENTS_PER_PAGE, 128);

    // Previous page button
    if (currentInstrumentPage > 0) {
        var prevBtn = document.createElement('button');
        prevBtn.className = 'instr-tab instr-more-btn';
        prevBtn.textContent = '<';
        prevBtn.title = 'Previous page';
        prevBtn.addEventListener('click', function() {
            currentInstrumentPage--;
            renderInstrumentTabs();
        });
        container.appendChild(prevBtn);
    }

    // Instrument tabs for current page
    for (var i = startIdx; i < endIdx; i++) {
        var tab = document.createElement('button');
        tab.className = 'instr-tab' + (i === state.currentInstrument ? ' active' : '');
        tab.setAttribute('data-instr', i);
        tab.textContent = (i + 1);
        tab.addEventListener('click', handleInstrumentTabClick);
        container.appendChild(tab);
    }

    // Next page button
    if (endIdx < 128) {
        var nextBtn = document.createElement('button');
        nextBtn.className = 'instr-tab instr-more-btn';
        nextBtn.textContent = '>';
        nextBtn.title = 'Next page (' + (startIdx + 17) + '-' + Math.min(startIdx + 32, 128) + ')';
        nextBtn.addEventListener('click', function() {
            currentInstrumentPage++;
            renderInstrumentTabs();
        });
        container.appendChild(nextBtn);
    }

    // Page indicator
    var pageInfo = document.createElement('span');
    pageInfo.className = 'instr-page-info';
    pageInfo.textContent = (currentInstrumentPage + 1) + '/8';
    container.appendChild(pageInfo);
}

function handleInstrumentTabClick(e) {
    var idx = parseInt(e.target.getAttribute('data-instr'));
    var previousInstrument = state.currentInstrument;

    saveCurrentInstrument();

    // Auto-compile if the previous instrument changed
    if (state.csoundReady && previousInstrument !== idx) {
        var currentCode = state.instruments[previousInstrument];
        var lastCode = lastCompiled.instruments[previousInstrument] || '';
        if (currentCode !== lastCode) {
            compileSingleInstrument(previousInstrument);
        }
    }

    document.querySelectorAll('.instr-tab').forEach(function(t) {
        t.classList.remove('active');
    });
    e.target.classList.add('active');

    state.currentInstrument = idx;
    document.getElementById('code-editor').value = state.instruments[idx];
}

function saveCurrentInstrument() {
    state.instruments[state.currentInstrument] = document.getElementById('code-editor').value;
}

function saveOpcodes() {
    state.opcodes = document.getElementById('opcodes-editor').value;
}

function initSampleLoader() {
    // Import button - imports to library (no ftable)
    var importBtn = document.getElementById('btn-import-sample');
    if (importBtn) {
        importBtn.addEventListener('click', function() {
            document.getElementById('sample-file-input').click();
        });
    }

    // Clear library button
    var clearBtn = document.getElementById('btn-clear-library');
    if (clearBtn) {
        clearBtn.addEventListener('click', function() {
            clearSampleLibrary();
        });
    }

    // Allow multiple file selection
    var fileInput = document.getElementById('sample-file-input');
    if (fileInput) {
        fileInput.setAttribute('multiple', 'true');
        fileInput.addEventListener('change', function(e) {
            if (e.target.files.length > 0) {
                importSamplesToLibrary(Array.from(e.target.files));
            }
        });
    }

    // Set up drag-and-drop for sample library
    var libraryList = document.getElementById('sample-library-list');
    if (libraryList) {
        setupDropTarget(libraryList, function(files) {
            importSamplesToLibrary(files);
        });
    }

    // Setup ftable pool as drop target
    setupFtablePoolDropZone();

    // Initial render
    renderSampleLibrary();
    renderFtablePool();
    updateNextFtableDisplay();
}

function setupDropTarget(target, callback) {
    target.addEventListener('dragover', function(e) {
        e.preventDefault();
        e.stopPropagation();
        target.classList.add('drag-over');
    });

    target.addEventListener('dragleave', function(e) {
        e.preventDefault();
        e.stopPropagation();
        target.classList.remove('drag-over');
    });

    target.addEventListener('drop', async function(e) {
        e.preventDefault();
        e.stopPropagation();
        target.classList.remove('drag-over');

        var files = [];

        // Check if we can use webkitGetAsEntry for folder support
        if (e.dataTransfer.items && e.dataTransfer.items[0] && e.dataTransfer.items[0].webkitGetAsEntry) {
            var entries = [];
            for (var i = 0; i < e.dataTransfer.items.length; i++) {
                var entry = e.dataTransfer.items[i].webkitGetAsEntry();
                if (entry) {
                    entries.push(entry);
                }
            }
            files = await getFilesFromEntries(entries);
        } else if (e.dataTransfer.items) {
            for (var i = 0; i < e.dataTransfer.items.length; i++) {
                if (e.dataTransfer.items[i].kind === 'file') {
                    var file = e.dataTransfer.items[i].getAsFile();
                    if (isAudioFile(file.name)) {
                        files.push(file);
                    }
                }
            }
        } else {
            for (var i = 0; i < e.dataTransfer.files.length; i++) {
                if (isAudioFile(e.dataTransfer.files[i].name)) {
                    files.push(e.dataTransfer.files[i]);
                }
            }
        }

        if (files.length > 0) {
            callback(files);
        } else {
            consoleLog('No audio files found in drop');
        }
    });
}

// Get next available ftable number (reuses deleted numbers)
function getNextFtableNum() {
    // First check for freed ftable numbers (gaps from deleted ftables)
    for (var i = 100; i < 1000; i++) {
        if (!state.usedFtables[i]) {
            return i;
        }
    }
    return state.nextFtableNum;
}

function updateNextFtableDisplay() {
    var display = document.getElementById('next-ftable-num');
    if (display) {
        display.textContent = getNextFtableNum();
    }
}

// Import samples to library (without loading to ftable)
async function importSamplesToLibrary(files) {
    files.sort(function(a, b) {
        return a.name.localeCompare(b.name);
    });

    consoleLog('Importing ' + files.length + ' sample(s) to library...');

    for (var i = 0; i < files.length; i++) {
        await importSingleSampleToLibrary(files[i]);
    }

    renderSampleLibrary();
    consoleLog('Imported ' + files.length + ' sample(s) to library');
}

async function importSingleSampleToLibrary(file) {
    return new Promise(function(resolve) {
        var reader = new FileReader();
        reader.onload = async function(e) {
            try {
                var arrayBuffer = e.target.result;
                var isWav = file.name.toLowerCase().endsWith('.wav');
                var wavInfo = null;
                var channelArrays = null;
                var audioBuffer = null;

                if (isWav) {
                    wavInfo = parseWavHeader(arrayBuffer);
                    if (wavInfo.isValid) {
                        channelArrays = extractWavSamples(arrayBuffer, wavInfo);
                    }
                }

                // Fallback to Web Audio API
                if (!channelArrays) {
                    var audioCtxForDecode = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
                    audioBuffer = await audioCtxForDecode.decodeAudioData(arrayBuffer.slice(0));
                    channelArrays = [];
                    for (var ch = 0; ch < audioBuffer.numberOfChannels; ch++) {
                        channelArrays.push(audioBuffer.getChannelData(ch));
                    }
                    wavInfo = {
                        isValid: true,
                        format: 'DECODED',
                        channels: audioBuffer.numberOfChannels,
                        sampleRate: audioBuffer.sampleRate,
                        bitsPerSample: 32,
                        numSamples: audioBuffer.length,
                        duration: audioBuffer.duration
                    };
                }

                // Create audioBuffer for display if needed
                if (!audioBuffer && channelArrays) {
                    var audioCtxForBuffer = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
                    audioBuffer = audioCtxForBuffer.createBuffer(
                        channelArrays.length,
                        channelArrays[0].length,
                        wavInfo.sampleRate
                    );
                    for (var ch = 0; ch < channelArrays.length; ch++) {
                        audioBuffer.getChannelData(ch).set(channelArrays[ch]);
                    }
                }

                // Generate unique ID for library item
                var libId = 'lib_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9);

                var libraryItem = {
                    id: libId,
                    name: file.name,
                    rawData: arrayBuffer,
                    audioBuffer: audioBuffer,
                    channelArrays: channelArrays,
                    format: wavInfo.format,
                    channels: wavInfo.channels,
                    sampleRate: wavInfo.sampleRate,
                    bitsPerSample: wavInfo.bitsPerSample,
                    numSamples: wavInfo.numSamples,
                    duration: wavInfo.duration
                };

                state.sampleLibrary.push(libraryItem);
                resolve();

            } catch (err) {
                consoleLog('Error importing ' + file.name + ': ' + err.message);
                resolve();
            }
        };
        reader.readAsArrayBuffer(file);
    });
}

// Load a sample from library to an ftable
// Reload restored ftables into Csound after loading a song
async function loadRestoredFtablesIntoCsound() {
    if (!state.csoundReady || !csound) return;

    for (var i = 0; i < state.samples.length; i++) {
        var sample = state.samples[i];
        if (!sample.rawData) continue;

        try {
            var fileName = sample.fileName || ('/' + sample.name);
            var fileData = new Uint8Array(sample.rawData);
            await csound.fs.writeFile(fileName, fileData);

            var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
            await csound.readScore(ftableScore);

            consoleLog('Restored ftable ' + sample.tableNum + ': ' + (sample.name || fileName));
        } catch (err) {
            consoleLog('Error restoring ftable ' + sample.tableNum + ': ' + err.message);
        }
    }
}

async function loadLibrarySampleToFtable(libraryId) {
    if (!state.csoundReady || !csound) {
        consoleLog('Error: Csound not ready');
        return;
    }

    var libItem = state.sampleLibrary.find(function(s) { return s.id === libraryId; });
    if (!libItem) {
        consoleLog('Error: Sample not found in library');
        return;
    }

    // Get next available ftable number
    var tableNum = getNextFtableNum();

    consoleLog('Loading ' + libItem.name + ' to ftable ' + tableNum + '...');

    try {
        // Write file to Csound filesystem
        var fileName = '/' + libItem.name.replace(/[^a-zA-Z0-9._-]/g, '_');
        var fileData = new Uint8Array(libItem.rawData);
        await csound.fs.writeFile(fileName, fileData);

        // Create ftable using GEN01
        var ftableScore = 'f ' + tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
        await csound.readScore(ftableScore);

        // Create ftable pool entry
        var ftableItem = {
            tableNum: tableNum,
            libraryId: libraryId,
            name: libItem.name,
            fileName: fileName,
            audioBuffer: libItem.audioBuffer,
            duration: libItem.duration,
            sampleRate: libItem.sampleRate,
            channels: libItem.channels
        };

        state.ftablePool.push(ftableItem);
        state.usedFtables[tableNum] = true;

        // Also add to legacy samples array for compatibility
        state.samples.push({
            name: libItem.name,
            tableNum: tableNum,
            fileName: fileName,
            audioBuffer: libItem.audioBuffer,
            rawData: libItem.rawData,
            channelArrays: libItem.channelArrays,
            audioArray: libItem.channelArrays ? new Float32Array(libItem.channelArrays[0]) : null,
            format: libItem.format,
            channels: libItem.channels,
            sampleRate: libItem.sampleRate,
            bitsPerSample: libItem.bitsPerSample,
            numSamples: libItem.numSamples,
            duration: libItem.duration,
            slices: []
        });

        renderFtablePool();
        renderSampleList();  // Legacy list
        updateNextFtableDisplay();

        consoleLog('Loaded ' + libItem.name + ' -> ftable ' + tableNum);

    } catch (err) {
        consoleLog('Error loading to ftable: ' + err.message);
    }
}

// Delete an ftable (frees the number for reuse)
function deleteFtable(tableNum) {
    // Remove from ftable pool
    state.ftablePool = state.ftablePool.filter(function(f) { return f.tableNum !== tableNum; });

    // Remove from legacy samples
    state.samples = state.samples.filter(function(s) { return s.tableNum !== tableNum; });

    // Mark ftable number as available
    delete state.usedFtables[tableNum];

    // Clear the ftable in Csound (set to empty)
    if (state.csoundReady && csound) {
        try {
            // Create an empty table to clear it
            csound.readScore('f ' + tableNum + ' 0 0 0');
        } catch (err) {}
    }

    renderFtablePool();
    renderSampleList();
    updateNextFtableDisplay();

    consoleLog('Deleted ftable ' + tableNum + ' (now available for reuse)');
}

// Remove a sample from the library
function removeFromLibrary(libraryId) {
    state.sampleLibrary = state.sampleLibrary.filter(function(s) { return s.id !== libraryId; });
    renderSampleLibrary();
    consoleLog('Removed sample from library');
}

// Clear entire sample library and free memory
function clearSampleLibrary() {
    if (state.sampleLibrary.length === 0) {
        consoleLog('Sample library is already empty');
        return;
    }
    var count = state.sampleLibrary.length;
    // Null out all references to large data so GC can reclaim memory
    state.sampleLibrary.forEach(function(item) {
        item.rawData = null;
        item.audioBuffer = null;
        item.channelArrays = null;
    });
    state.sampleLibrary = [];
    renderSampleLibrary();
    consoleLog('Cleared ' + count + ' samples from library (memory freed)');
}

// Render the sample library list
function renderSampleLibrary() {
    var list = document.getElementById('sample-library-list');
    if (!list) return;

    list.innerHTML = '';

    if (state.sampleLibrary.length === 0) {
        list.innerHTML = '<div class="sample-list-empty">Drop samples here or click Import</div>';
        return;
    }

    state.sampleLibrary.forEach(function(item) {
        var div = document.createElement('div');
        div.className = 'library-item';
        div.setAttribute('draggable', 'true');
        div.setAttribute('data-library-id', item.id);

        var duration = item.duration ? item.duration.toFixed(2) + 's' : '';
        var size = item.rawData ? (item.rawData.byteLength / 1024).toFixed(1) + 'KB' : '';

        div.innerHTML =
            '<span class="sample-name" title="' + item.name + '">' + item.name + '</span>' +
            '<span class="sample-size">' + duration + ' ' + size + '</span>' +
            '<button class="btn-play" data-id="' + item.id + '" title="Play">▶</button>' +
            '<button class="btn-load-ftable" data-id="' + item.id + '" title="Load to ftable">→ ft</button>' +
            '<button class="btn-remove" data-id="' + item.id + '" title="Remove from library">×</button>';

        // Drag start - store library item ID
        div.addEventListener('dragstart', function(e) {
            e.dataTransfer.setData('application/x-library-sample', item.id);
            e.dataTransfer.effectAllowed = 'copy';
            div.classList.add('dragging');
        });

        div.addEventListener('dragend', function() {
            div.classList.remove('dragging');
        });

        // Play button
        div.querySelector('.btn-play').addEventListener('click', function(e) {
            e.stopPropagation();
            var id = this.getAttribute('data-id');
            playLibrarySample(id);
        });

        // Load to ftable button
        div.querySelector('.btn-load-ftable').addEventListener('click', function(e) {
            e.stopPropagation();
            var id = this.getAttribute('data-id');
            loadLibrarySampleToFtable(id);
        });

        // Remove button
        div.querySelector('.btn-remove').addEventListener('click', function(e) {
            e.stopPropagation();
            var id = this.getAttribute('data-id');
            removeFromLibrary(id);
        });

        list.appendChild(div);
    });
}

// Setup ftable pool as drop target for library items
function setupFtablePoolDropZone() {
    var pool = document.getElementById('ftable-pool-list');
    if (!pool) return;

    pool.addEventListener('dragover', function(e) {
        if (e.dataTransfer.types.includes('application/x-library-sample')) {
            e.preventDefault();
            e.dataTransfer.dropEffect = 'copy';
            pool.classList.add('drag-over');
        }
    });

    pool.addEventListener('dragleave', function(e) {
        pool.classList.remove('drag-over');
    });

    pool.addEventListener('drop', function(e) {
        e.preventDefault();
        pool.classList.remove('drag-over');

        var libraryId = e.dataTransfer.getData('application/x-library-sample');
        if (libraryId) {
            loadLibrarySampleToFtable(libraryId);
        }
    });
}

// Render the ftable pool list
var ftableDragState = { dragging: null, overItem: null, position: null };

function renderFtablePool() {
    var list = document.getElementById('ftable-pool-list');
    if (!list) return;

    list.innerHTML = '';

    if (state.ftablePool.length === 0) {
        list.innerHTML = '<div class="sample-list-empty">No samples loaded to ftables</div>';
        return;
    }

    // Sort by table number
    var sorted = state.ftablePool.slice().sort(function(a, b) { return a.tableNum - b.tableNum; });

    sorted.forEach(function(item, index) {
        var div = document.createElement('div');
        div.className = 'ftable-item';
        div.setAttribute('draggable', 'true');
        div.setAttribute('data-ftable-index', index);
        div.setAttribute('data-ftable-num', item.tableNum);

        div.innerHTML =
            '<span class="ftable-num">ft' + item.tableNum + '</span>' +
            '<span class="sample-name" data-table="' + item.tableNum + '" title="Click to edit">' + item.name + '</span>' +
            '<button class="btn-play" data-table="' + item.tableNum + '" title="Play">▶</button>' +
            '<button class="btn-delete" data-table="' + item.tableNum + '" title="Delete (frees ftable)">×</button>';

        // Drag start
        div.addEventListener('dragstart', function(e) {
            ftableDragState.dragging = item.tableNum;
            e.dataTransfer.setData('application/x-ftable-reorder', item.tableNum.toString());
            e.dataTransfer.effectAllowed = 'move';
            div.classList.add('dragging');
        });

        div.addEventListener('dragend', function() {
            div.classList.remove('dragging');
            ftableDragState.dragging = null;
            // Clear all drag indicators
            var items = list.querySelectorAll('.ftable-item');
            items.forEach(function(el) {
                el.classList.remove('drag-above', 'drag-below');
            });
        });

        div.addEventListener('dragover', function(e) {
            // Only handle ftable reorder drags, not library-to-ftable drags
            if (ftableDragState.dragging === null) return;
            e.preventDefault();
            e.dataTransfer.dropEffect = 'move';

            // Determine if above or below midpoint
            var rect = div.getBoundingClientRect();
            var midY = rect.top + rect.height / 2;
            var above = e.clientY < midY;

            // Clear all indicators
            var items = list.querySelectorAll('.ftable-item');
            items.forEach(function(el) {
                el.classList.remove('drag-above', 'drag-below');
            });

            if (item.tableNum !== ftableDragState.dragging) {
                div.classList.add(above ? 'drag-above' : 'drag-below');
                ftableDragState.overItem = item.tableNum;
                ftableDragState.position = above ? 'above' : 'below';
            }
        });

        div.addEventListener('drop', function(e) {
            e.preventDefault();
            var srcTable = parseInt(e.dataTransfer.getData('application/x-ftable-reorder'));
            if (!srcTable || srcTable === item.tableNum) return;

            // Clear indicators
            var items = list.querySelectorAll('.ftable-item');
            items.forEach(function(el) {
                el.classList.remove('drag-above', 'drag-below');
            });

            reorderFtables(srcTable, item.tableNum, ftableDragState.position === 'above');
        });

        // Play button
        div.querySelector('.btn-play').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            playSampleFromBank(tbl);
        });

        // Sample name - click to load in editor
        div.querySelector('.sample-name').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            var sample = state.samples.find(function(s) { return s.tableNum === tbl; });
            if (sample) {
                loadSampleIntoEditor(sample);
            }
        });

        // Delete button
        div.querySelector('.btn-delete').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            deleteFtable(tbl);
        });

        list.appendChild(div);
    });
}

// Reorder ftables: move srcTable to be above or below targetTable
async function reorderFtables(srcTable, targetTable, insertAbove) {
    // Get current sorted order
    var sorted = state.ftablePool.slice().sort(function(a, b) { return a.tableNum - b.tableNum; });

    // Extract the source item
    var srcItem = null;
    var newOrder = [];
    for (var i = 0; i < sorted.length; i++) {
        if (sorted[i].tableNum === srcTable) {
            srcItem = sorted[i];
        } else {
            newOrder.push(sorted[i]);
        }
    }
    if (!srcItem) return;

    // Find target position and insert
    var insertIdx = -1;
    for (var i = 0; i < newOrder.length; i++) {
        if (newOrder[i].tableNum === targetTable) {
            insertIdx = insertAbove ? i : i + 1;
            break;
        }
    }
    if (insertIdx === -1) insertIdx = newOrder.length;
    newOrder.splice(insertIdx, 0, srcItem);

    // Collect the table numbers in their original sorted order
    var tableNums = sorted.map(function(item) { return item.tableNum; });

    // Build a mapping: each item in newOrder gets the table number at that position
    var remapPlan = []; // { item, oldTable, newTable }
    for (var i = 0; i < newOrder.length; i++) {
        var oldTable = newOrder[i].tableNum;
        var newTable = tableNums[i];
        if (oldTable !== newTable) {
            remapPlan.push({ item: newOrder[i], oldTable: oldTable, newTable: newTable });
        } else {
            // No change needed
            newOrder[i].tableNum = newTable;
        }
    }

    if (remapPlan.length === 0) return; // Nothing to change

    // Reassign ftable numbers in Csound
    // Strategy: use a temporary high table number to avoid collisions
    // For each remap, copy old -> temp, then temp -> new
    if (state.csoundReady && csound) {
        try {
            var tempBase = 9000;
            // Step 1: Copy all affected tables to temp numbers
            for (var i = 0; i < remapPlan.length; i++) {
                var plan = remapPlan[i];
                var tempTable = tempBase + i;
                // Find the sample's raw data in state.samples
                var sample = state.samples.find(function(s) { return s.tableNum === plan.oldTable; });
                if (sample && sample.fileName) {
                    // Re-create ftable at temp number from file
                    await csound.readScore('f ' + tempTable + ' 0 0 1 "' + sample.fileName + '" 0 0 0');
                }
                // Store temp assignment
                plan.tempTable = tempTable;
            }

            // Step 2: Clear old table numbers
            for (var i = 0; i < remapPlan.length; i++) {
                await csound.readScore('f ' + remapPlan[i].oldTable + ' 0 0 0');
            }

            // Step 3: Copy from temp to new table number
            for (var i = 0; i < remapPlan.length; i++) {
                var plan = remapPlan[i];
                var sample = state.samples.find(function(s) { return s.tableNum === plan.oldTable; });
                if (sample && sample.fileName) {
                    await csound.readScore('f ' + plan.newTable + ' 0 0 1 "' + sample.fileName + '" 0 0 0');
                }
                // Clear temp
                await csound.readScore('f ' + plan.tempTable + ' 0 0 0');
            }
        } catch (err) {
            consoleLog('Error reassigning ftables in Csound: ' + err.message);
        }
    }

    // Update state: ftablePool, samples, usedFtables
    state.usedFtables = {};
    for (var i = 0; i < remapPlan.length; i++) {
        var plan = remapPlan[i];
        // Update ftablePool entry
        plan.item.tableNum = plan.newTable;
        // Update corresponding sample in state.samples
        var sample = state.samples.find(function(s) { return s.tableNum === plan.oldTable; });
        if (sample) {
            sample.tableNum = plan.newTable;
        }
    }
    // Rebuild usedFtables
    state.ftablePool.forEach(function(item) {
        state.usedFtables[item.tableNum] = true;
    });

    renderFtablePool();
    updateNextFtableDisplay();

    consoleLog('Reordered ftables: ft' + srcTable + ' moved ' + (insertAbove ? 'above' : 'below') + ' ft' + targetTable);
}

function isAudioFile(filename) {
    var ext = filename.toLowerCase().split('.').pop();
    return ['wav', 'aif', 'aiff', 'mp3', 'ogg', 'flac'].indexOf(ext) !== -1;
}

async function getFilesFromEntries(entries) {
    var files = [];

    async function traverseEntry(entry) {
        if (entry.isFile) {
            return new Promise(function(resolve) {
                entry.file(function(file) {
                    if (isAudioFile(file.name)) {
                        files.push(file);
                    }
                    resolve();
                }, function() {
                    resolve(); // Ignore errors
                });
            });
        } else if (entry.isDirectory) {
            var reader = entry.createReader();
            return new Promise(function(resolve) {
                var readEntries = function() {
                    reader.readEntries(async function(subEntries) {
                        if (subEntries.length === 0) {
                            resolve();
                        } else {
                            for (var i = 0; i < subEntries.length; i++) {
                                await traverseEntry(subEntries[i]);
                            }
                            // Continue reading (directories may have >100 entries)
                            readEntries();
                        }
                    }, function() {
                        resolve(); // Ignore errors
                    });
                };
                readEntries();
            });
        }
    }

    for (var i = 0; i < entries.length; i++) {
        await traverseEntry(entries[i]);
    }

    return files;
}

// Legacy function - now imports to library instead of directly to ftables
async function loadMultipleSampleFiles(files) {
    await importSamplesToLibrary(files);
}

// ============================================
// WAV FILE PARSING
// ============================================

function parseWavHeader(arrayBuffer) {
    var view = new DataView(arrayBuffer);
    var result = {
        isValid: false,
        error: null,
        format: null,
        channels: 0,
        sampleRate: 0,
        byteRate: 0,
        blockAlign: 0,
        bitsPerSample: 0,
        dataOffset: 0,
        dataSize: 0,
        numSamples: 0,
        duration: 0,
        // Extended format info
        validBitsPerSample: 0,
        channelMask: 0,
        subFormat: null
    };

    // Check minimum size
    if (arrayBuffer.byteLength < 44) {
        result.error = 'File too small to be a valid WAV';
        return result;
    }

    // Read RIFF header
    var riff = String.fromCharCode(view.getUint8(0), view.getUint8(1), view.getUint8(2), view.getUint8(3));
    if (riff !== 'RIFF') {
        result.error = 'Not a RIFF file (got: ' + riff + ')';
        return result;
    }

    var fileSize = view.getUint32(4, true); // Little-endian

    var wave = String.fromCharCode(view.getUint8(8), view.getUint8(9), view.getUint8(10), view.getUint8(11));
    if (wave !== 'WAVE') {
        result.error = 'Not a WAVE file (got: ' + wave + ')';
        return result;
    }

    // Parse chunks
    var offset = 12;
    var foundFmt = false;
    var foundData = false;

    while (offset < arrayBuffer.byteLength - 8) {
        var chunkId = String.fromCharCode(
            view.getUint8(offset),
            view.getUint8(offset + 1),
            view.getUint8(offset + 2),
            view.getUint8(offset + 3)
        );
        var chunkSize = view.getUint32(offset + 4, true);

        if (chunkId === 'fmt ') {
            // Format chunk
            foundFmt = true;
            var audioFormat = view.getUint16(offset + 8, true);
            result.channels = view.getUint16(offset + 10, true);
            result.sampleRate = view.getUint32(offset + 12, true);
            result.byteRate = view.getUint32(offset + 16, true);
            result.blockAlign = view.getUint16(offset + 20, true);
            result.bitsPerSample = view.getUint16(offset + 22, true);

            // Determine format type
            if (audioFormat === 1) {
                result.format = 'PCM';
            } else if (audioFormat === 3) {
                result.format = 'IEEE_FLOAT';
            } else if (audioFormat === 6) {
                result.format = 'A-LAW';
            } else if (audioFormat === 7) {
                result.format = 'MU-LAW';
            } else if (audioFormat === 0xFFFE) {
                result.format = 'EXTENSIBLE';
                // Parse extended format info if present
                if (chunkSize >= 40) {
                    var cbSize = view.getUint16(offset + 24, true);
                    if (cbSize >= 22) {
                        result.validBitsPerSample = view.getUint16(offset + 26, true);
                        result.channelMask = view.getUint32(offset + 28, true);
                        // SubFormat GUID - first two bytes indicate actual format
                        var subFormatCode = view.getUint16(offset + 32, true);
                        if (subFormatCode === 1) {
                            result.subFormat = 'PCM';
                        } else if (subFormatCode === 3) {
                            result.subFormat = 'IEEE_FLOAT';
                        } else {
                            result.subFormat = 'UNKNOWN_' + subFormatCode;
                        }
                    }
                }
            } else {
                result.format = 'UNKNOWN_' + audioFormat;
            }

        } else if (chunkId === 'data') {
            // Data chunk
            foundData = true;
            result.dataOffset = offset + 8;
            result.dataSize = chunkSize;

            // Calculate number of samples
            var bytesPerSample = result.bitsPerSample / 8;
            if (bytesPerSample > 0 && result.channels > 0) {
                result.numSamples = Math.floor(chunkSize / (bytesPerSample * result.channels));
                result.duration = result.numSamples / result.sampleRate;
            }
        }
        // Skip other chunks (LIST, fact, cue, etc.)

        // Move to next chunk (chunks are word-aligned)
        offset += 8 + chunkSize;
        if (chunkSize % 2 === 1) offset++; // Padding byte
    }

    if (!foundFmt) {
        result.error = 'No fmt chunk found';
        return result;
    }

    if (!foundData) {
        result.error = 'No data chunk found';
        return result;
    }

    result.isValid = true;
    return result;
}

function extractWavSamples(arrayBuffer, wavInfo) {
    if (!wavInfo.isValid) {
        return null;
    }

    var view = new DataView(arrayBuffer);
    var numSamples = wavInfo.numSamples;
    var channels = wavInfo.channels;
    var bitsPerSample = wavInfo.bitsPerSample;
    var dataOffset = wavInfo.dataOffset;
    var format = wavInfo.subFormat || wavInfo.format;

    // Output: interleaved Float32Array (or mono if single channel)
    // For Csound, we'll create separate channel arrays
    var channelArrays = [];
    for (var ch = 0; ch < channels; ch++) {
        channelArrays.push(new Float32Array(numSamples));
    }

    var sampleIndex = 0;
    var byteOffset = dataOffset;
    var bytesPerSample = bitsPerSample / 8;

    for (var i = 0; i < numSamples; i++) {
        for (var ch = 0; ch < channels; ch++) {
            var sample = 0;

            if (format === 'PCM') {
                if (bitsPerSample === 8) {
                    // 8-bit PCM is unsigned (0-255, center at 128)
                    sample = (view.getUint8(byteOffset) - 128) / 128;
                } else if (bitsPerSample === 16) {
                    // 16-bit PCM is signed
                    sample = view.getInt16(byteOffset, true) / 32768;
                } else if (bitsPerSample === 24) {
                    // 24-bit PCM - read 3 bytes and convert
                    var b0 = view.getUint8(byteOffset);
                    var b1 = view.getUint8(byteOffset + 1);
                    var b2 = view.getUint8(byteOffset + 2);
                    var val = (b2 << 16) | (b1 << 8) | b0;
                    // Sign extend
                    if (val & 0x800000) val |= 0xFF000000;
                    sample = val / 8388608; // 2^23
                } else if (bitsPerSample === 32) {
                    // 32-bit PCM
                    sample = view.getInt32(byteOffset, true) / 2147483648; // 2^31
                }
            } else if (format === 'IEEE_FLOAT') {
                if (bitsPerSample === 32) {
                    sample = view.getFloat32(byteOffset, true);
                } else if (bitsPerSample === 64) {
                    sample = view.getFloat64(byteOffset, true);
                }
            } else if (format === 'A-LAW') {
                sample = alawToLinear(view.getUint8(byteOffset));
            } else if (format === 'MU-LAW') {
                sample = mulawToLinear(view.getUint8(byteOffset));
            }

            channelArrays[ch][i] = sample;
            byteOffset += bytesPerSample;
        }
    }

    return channelArrays;
}

// A-law decompression
function alawToLinear(alaw) {
    alaw ^= 0x55;
    var sign = (alaw & 0x80) ? -1 : 1;
    var exponent = (alaw >> 4) & 0x07;
    var mantissa = alaw & 0x0F;
    var sample;
    if (exponent === 0) {
        sample = (mantissa * 2 + 1) * 2;
    } else {
        sample = ((mantissa * 2 + 33) << exponent) - 33;
    }
    return sign * sample / 32768;
}

// Mu-law decompression
function mulawToLinear(mulaw) {
    mulaw = ~mulaw;
    var sign = (mulaw & 0x80) ? -1 : 1;
    var exponent = (mulaw >> 4) & 0x07;
    var mantissa = mulaw & 0x0F;
    var sample = ((mantissa * 2 + 33) << exponent) - 33;
    return sign * sample / 32768;
}

async function loadSampleFile(file) {
    var tableNum = getNextFtableNum();
    await loadSampleFileToTable(file, tableNum);
}

async function loadSampleFileToTable(file, tableNum) {
    if (!state.csoundReady || !csound) {
        consoleLog('Error: Csound not ready');
        return;
    }

    var existing = state.samples.find(function(s) { return s.tableNum === tableNum; });
    if (existing) {
        state.samples = state.samples.filter(function(s) { return s.tableNum !== tableNum; });
        state.ftablePool = state.ftablePool.filter(function(f) { return f.tableNum !== tableNum; });
    }

    consoleLog('Loading sample: ' + file.name + '...');

    var reader = new FileReader();
    reader.onload = async function(e) {
        try {
            var arrayBuffer = e.target.result;
            var isWav = file.name.toLowerCase().endsWith('.wav');
            var wavInfo = null;
            var channelArrays = null;
            var audioBuffer = null;

            if (isWav) {
                // Parse WAV header for accurate metadata
                wavInfo = parseWavHeader(arrayBuffer);

                if (wavInfo.isValid) {
                    consoleLog('WAV Header: ' + wavInfo.format +
                        ', ' + wavInfo.channels + 'ch' +
                        ', ' + wavInfo.sampleRate + 'Hz' +
                        ', ' + wavInfo.bitsPerSample + 'bit' +
                        ', ' + wavInfo.numSamples + ' samples' +
                        ', ' + wavInfo.duration.toFixed(3) + 's');

                    // Extract samples directly from WAV
                    channelArrays = extractWavSamples(arrayBuffer, wavInfo);

                    if (!channelArrays) {
                        throw new Error('Failed to extract WAV samples');
                    }
                } else {
                    consoleLog('WAV parse error: ' + wavInfo.error + ', falling back to Web Audio API');
                }
            }

            // Fallback to Web Audio API for non-WAV files or parse failures
            if (!channelArrays) {
                var audioCtxForDecode = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
                audioBuffer = await audioCtxForDecode.decodeAudioData(arrayBuffer.slice(0));

                consoleLog('Decoded via Web Audio: ' + audioBuffer.numberOfChannels + 'ch, ' +
                    audioBuffer.sampleRate + 'Hz, ' + audioBuffer.length + ' samples');

                // Extract channel data
                channelArrays = [];
                for (var ch = 0; ch < audioBuffer.numberOfChannels; ch++) {
                    channelArrays.push(audioBuffer.getChannelData(ch));
                }

                // Create wavInfo from audioBuffer
                wavInfo = {
                    isValid: true,
                    format: 'DECODED',
                    channels: audioBuffer.numberOfChannels,
                    sampleRate: audioBuffer.sampleRate,
                    bitsPerSample: 32, // Web Audio uses float32
                    numSamples: audioBuffer.length,
                    duration: audioBuffer.duration
                };
            }

            // Use first channel for mono Csound table (or mix to mono if needed)
            var audioArray = new Float32Array(channelArrays[0].length);
            audioArray.set(channelArrays[0]);

            // Write the original file to Csound's virtual filesystem for GEN01
            var fileName = '/' + file.name.replace(/[^a-zA-Z0-9._-]/g, '_');
            var fileData = new Uint8Array(arrayBuffer);
            await csound.fs.writeFile(fileName, fileData);
            consoleLog('Wrote file to Csound fs: ' + fileName);

            // Create ftable using GEN01 (deferred load from file)
            // f tableNum 0 0 1 "filename" 0 0 0
            var ftableScore = 'f ' + tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
            await csound.readScore(ftableScore);
            consoleLog('Created ftable ' + tableNum + ' from ' + fileName);

            // Create audioBuffer for sample editor if we don't have one
            if (!audioBuffer) {
                // Create an AudioBuffer from our parsed data for the waveform display
                var audioCtxForBuffer = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
                audioBuffer = audioCtxForBuffer.createBuffer(
                    channelArrays.length,
                    channelArrays[0].length,
                    wavInfo.sampleRate
                );
                for (var ch = 0; ch < channelArrays.length; ch++) {
                    audioBuffer.getChannelData(ch).set(channelArrays[ch]);
                }
            }

            // Store sample with all metadata
            var sampleObj = {
                name: file.name,
                tableNum: tableNum,
                fileName: fileName,
                rawData: arrayBuffer,
                audioBuffer: audioBuffer,
                audioArray: audioArray,
                channelArrays: channelArrays,
                // WAV metadata
                format: wavInfo.format,
                channels: wavInfo.channels,
                sampleRate: wavInfo.sampleRate,
                bitsPerSample: wavInfo.bitsPerSample,
                numSamples: wavInfo.numSamples,
                duration: wavInfo.duration,
                // Extended info
                byteRate: wavInfo.byteRate,
                blockAlign: wavInfo.blockAlign,
                validBitsPerSample: wavInfo.validBitsPerSample,
                channelMask: wavInfo.channelMask,
                subFormat: wavInfo.subFormat,
                slices: []
            };

            state.samples.push(sampleObj);

            // Also register in new ftable tracking system
            state.usedFtables[tableNum] = true;
            state.ftablePool.push({
                tableNum: tableNum,
                libraryId: null,  // Directly loaded, not from library
                name: file.name,
                fileName: fileName,
                audioBuffer: audioBuffer,
                duration: wavInfo.duration,
                sampleRate: wavInfo.sampleRate,
                channels: wavInfo.channels
            });

            renderSampleList();
            renderFtablePool();
            updateNextFtableDisplay();

            consoleLog('Loaded: ' + file.name + ' -> ftable ' + tableNum);

            // Auto-load into sample editor if the Sample Editor tab is active
            var sampleView = document.getElementById('sample-editor-view');
            if (sampleView && !sampleView.classList.contains('hidden')) {
                loadSampleIntoEditor(sampleObj);
            }

        } catch (err) {
            consoleLog('Error loading sample: ' + err.message);
            console.error(err);
        }
    };

    reader.readAsArrayBuffer(file);
}

// Legacy function - kept for backwards compatibility
function renderSampleList() {
    var list = document.getElementById('sample-list');
    if (!list) return;  // Element no longer exists in new UI

    list.innerHTML = '';

    if (state.samples.length === 0) {
        list.innerHTML = '<div style="padding:10px;color:#666;font-size:0.8em;">No samples loaded</div>';
        return;
    }

    state.samples.forEach(function(sample) {
        var item = document.createElement('div');
        item.className = 'sample-item';
        item.innerHTML =
            '<button class="sample-play-btn" data-table="' + sample.tableNum + '" title="Play">&#9658;</button>' +
            '<span class="sample-name" data-table="' + sample.tableNum + '">' + sample.name + '</span>' +
            '<span class="sample-table">ft' + sample.tableNum + '</span>' +
            '<button class="sample-delete-btn" data-table="' + sample.tableNum + '" title="Delete">X</button>';

        // Play button - click to play sample
        item.querySelector('.sample-play-btn').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            playSampleFromBank(tbl);
        });

        // Delete button - now uses deleteFtable for proper cleanup
        item.querySelector('.sample-delete-btn').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            deleteFtable(tbl);
        });

        // Make clicking sample name load it in sample editor
        item.querySelector('.sample-name').addEventListener('click', function() {
            var tbl = parseInt(this.getAttribute('data-table'));
            var s = state.samples.find(function(sam) { return sam.tableNum === tbl; });
            if (s) loadSampleIntoEditor(s);
        });

        list.appendChild(item);
    });
}

// ============================================
// PIANO ROLL
// ============================================

var pianoRoll = {
    canvas: null,
    ctx: null,
    velocityCanvas: null,
    velocityCtx: null,
    keysContainer: null,
    pixelsPerBeat: 40,
    noteHeight: 16,
    octaves: 9,  // C-1 to C8
    lowestNote: 12,  // C0 (MIDI note 12)
    notes: [],  // Array of { pitch, startBeat, duration, velocity }
    selectedNotes: [],
    isDragging: false,
    dragMode: null,  // 'move', 'resize', 'draw'
    dragStartX: 0,
    dragStartY: 0,
    scrollX: 0,
    scrollY: 0
};

function initPianoRoll() {
    pianoRoll.canvas = document.getElementById('piano-roll-canvas');
    pianoRoll.velocityCanvas = document.getElementById('velocity-canvas');
    pianoRoll.keysContainer = document.getElementById('piano-keys');

    if (pianoRoll.canvas) {
        pianoRoll.ctx = pianoRoll.canvas.getContext('2d');
        pianoRoll.canvas.addEventListener('mousedown', handlePianoRollMouseDown);
        pianoRoll.canvas.addEventListener('mousemove', handlePianoRollMouseMove);
        pianoRoll.canvas.addEventListener('mouseup', handlePianoRollMouseUp);
        pianoRoll.canvas.addEventListener('dblclick', handlePianoRollDblClick);
        pianoRoll.canvas.addEventListener('contextmenu', handlePianoRollContextMenu);
    }

    if (pianoRoll.velocityCanvas) {
        pianoRoll.velocityCtx = pianoRoll.velocityCanvas.getContext('2d');
    }

    // Quantize selector
    var quantizeSelect = document.getElementById('piano-quantize');
    if (quantizeSelect) {
        quantizeSelect.addEventListener('change', function() {
            state.quantize = this.value;
        });
    }

    // Zoom buttons
    var btnZoomIn = document.getElementById('btn-piano-zoom-in');
    var btnZoomOut = document.getElementById('btn-piano-zoom-out');
    if (btnZoomIn) btnZoomIn.addEventListener('click', function() { zoomPianoRoll(1.25); });
    if (btnZoomOut) btnZoomOut.addEventListener('click', function() { zoomPianoRoll(0.8); });

    renderPianoKeys();
}

function renderPianoKeys() {
    if (!pianoRoll.keysContainer) return;
    pianoRoll.keysContainer.innerHTML = '';

    // Render from high to low (C8 to C0)
    var totalNotes = pianoRoll.octaves * 12;
    for (var i = totalNotes - 1; i >= 0; i--) {
        var noteNum = pianoRoll.lowestNote + i;
        var octave = Math.floor(noteNum / 12) - 1;
        var noteIdx = noteNum % 12;
        var isBlack = [1, 3, 6, 8, 10].indexOf(noteIdx) !== -1;

        var key = document.createElement('div');
        key.className = 'piano-key ' + (isBlack ? 'black' : 'white');
        key.setAttribute('data-note', noteNum);
        key.textContent = noteNames[noteIdx] + octave;
        key.addEventListener('mousedown', function(e) {
            var note = parseInt(this.getAttribute('data-note'));
            previewMidiNote(note, 100);
            this.classList.add('playing');
        });
        key.addEventListener('mouseup', function() {
            var note = parseInt(this.getAttribute('data-note'));
            stopMidiNote(note);
            this.classList.remove('playing');
        });
        key.addEventListener('mouseleave', function() {
            var note = parseInt(this.getAttribute('data-note'));
            stopMidiNote(note);
            this.classList.remove('playing');
        });

        pianoRoll.keysContainer.appendChild(key);
    }
}

function renderPianoRoll() {
    if (!pianoRoll.canvas || !pianoRoll.ctx) return;

    var pattern = getCurrentPattern();
    if (!pattern) return;

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;
    var totalNotes = pianoRoll.octaves * 12;

    // Size canvas
    var width = patternBeats * pianoRoll.pixelsPerBeat;
    var height = totalNotes * pianoRoll.noteHeight;
    pianoRoll.canvas.width = width;
    pianoRoll.canvas.height = height;

    var ctx = pianoRoll.ctx;

    // Clear
    ctx.fillStyle = '#1a1a2e';
    ctx.fillRect(0, 0, width, height);

    // Draw grid
    ctx.strokeStyle = '#0f3460';
    ctx.lineWidth = 1;

    // Horizontal lines (note rows)
    for (var i = 0; i <= totalNotes; i++) {
        var y = i * pianoRoll.noteHeight;
        var noteNum = pianoRoll.lowestNote + (totalNotes - i);
        var isBlack = [1, 3, 6, 8, 10].indexOf(noteNum % 12) !== -1;

        // Darker background for black keys
        if (isBlack) {
            ctx.fillStyle = '#12122a';
            ctx.fillRect(0, y, width, pianoRoll.noteHeight);
        }

        ctx.beginPath();
        ctx.moveTo(0, y);
        ctx.lineTo(width, y);
        ctx.stroke();
    }

    // Vertical lines (beat/step grid)
    var stepsPerBeat = patternLpb;
    for (var step = 0; step <= pattern.steps; step++) {
        var x = (step / patternLpb) * pianoRoll.pixelsPerBeat;
        ctx.strokeStyle = (step % stepsPerBeat === 0) ? '#16213e' : '#0f3460';
        ctx.beginPath();
        ctx.moveTo(x, 0);
        ctx.lineTo(x, height);
        ctx.stroke();
    }

    // Draw notes from piano roll data
    ctx.fillStyle = '#4ecca3';
    for (var i = 0; i < pianoRoll.notes.length; i++) {
        var note = pianoRoll.notes[i];
        drawPianoNote(ctx, note);
    }

    // Also draw notes from step sequencer data (if any)
    var trackIdx = state.selectedTrack;
    if (pattern.data && pattern.data[trackIdx]) {
        for (var step = 0; step < pattern.steps; step++) {
            var stepData = pattern.data[trackIdx][step];
            if (stepData && stepData.notes) {
                for (var nc = 0; nc < stepData.notes.length; nc++) {
                    var noteData = stepData.notes[nc];
                    if (noteData.note && noteData.note !== '' && noteData.note !== NOTE_OFF) {
                        var midiNote = noteNameToMidi(noteData.note);
                        if (midiNote >= pianoRoll.lowestNote) {
                            var noteObj = {
                                pitch: midiNote,
                                startBeat: step / patternLpb,
                                duration: 1 / patternLpb,
                                velocity: parseAmplitude(noteData.amp)
                            };
                            drawPianoNote(ctx, noteObj, '#6c63ff');
                        }
                    }
                }
            }
        }
    }

    renderVelocityLane();
}

function drawPianoNote(ctx, note, color) {
    var totalNotes = pianoRoll.octaves * 12;
    var y = (totalNotes - (note.pitch - pianoRoll.lowestNote) - 1) * pianoRoll.noteHeight;
    var x = note.startBeat * pianoRoll.pixelsPerBeat;
    var w = note.duration * pianoRoll.pixelsPerBeat;

    ctx.fillStyle = color || '#4ecca3';
    ctx.fillRect(x + 1, y + 1, w - 2, pianoRoll.noteHeight - 2);

    // Border
    ctx.strokeStyle = 'rgba(0,0,0,0.3)';
    ctx.strokeRect(x + 1, y + 1, w - 2, pianoRoll.noteHeight - 2);
}

function renderVelocityLane() {
    if (!pianoRoll.velocityCanvas || !pianoRoll.velocityCtx) return;

    var pattern = getCurrentPattern();
    if (!pattern) return;

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;

    var canvas = pianoRoll.velocityCanvas;
    var ctx = pianoRoll.velocityCtx;

    // Match width to piano roll
    canvas.width = patternBeats * pianoRoll.pixelsPerBeat;
    canvas.height = 60;

    ctx.fillStyle = '#12122a';
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    // Draw velocity bars
    for (var i = 0; i < pianoRoll.notes.length; i++) {
        var note = pianoRoll.notes[i];
        var x = note.startBeat * pianoRoll.pixelsPerBeat;
        var h = (note.velocity || 0.7) * 50;

        ctx.fillStyle = '#4ecca3';
        ctx.fillRect(x + 2, 60 - h, 6, h);
    }
}



function midiToNoteName(midiNote) {
    var octave = Math.floor(midiNote / 12) - 1;
    var noteIdx = midiNote % 12;
    return noteNames[noteIdx] + '-' + octave;
}

function handlePianoRollMouseDown(e) {
    var rect = pianoRoll.canvas.getBoundingClientRect();
    var x = e.clientX - rect.left;
    var y = e.clientY - rect.top;

    pianoRoll.isDragging = true;
    pianoRoll.dragStartX = x;
    pianoRoll.dragStartY = y;

    // Check if clicking on existing note
    var clickedNote = findNoteAt(x, y);
    if (clickedNote) {
        pianoRoll.selectedNotes = [clickedNote];
        pianoRoll.dragMode = 'move';
    } else {
        pianoRoll.dragMode = 'draw';
    }

    renderPianoRoll();
}

function handlePianoRollMouseMove(e) {
    if (!pianoRoll.isDragging) return;
    // Drag handling will be implemented for note movement
}

function handlePianoRollMouseUp(e) {
    if (!pianoRoll.isDragging) return;

    var rect = pianoRoll.canvas.getBoundingClientRect();
    var x = e.clientX - rect.left;
    var y = e.clientY - rect.top;

    if (pianoRoll.dragMode === 'draw') {
        var totalNotes = pianoRoll.octaves * 12;

        var beat = x / pianoRoll.pixelsPerBeat;
        var pitch = pianoRoll.lowestNote + totalNotes - Math.floor(y / pianoRoll.noteHeight) - 1;

        // Quantize
        var quantizedBeat = quantizeBeat(beat);
        var quantizedDuration = getQuantizeDuration();

        var newNote = {
            pitch: pitch,
            startBeat: quantizedBeat,
            duration: quantizedDuration,
            velocity: 0.8
        };

        // Add to piano roll notes array (for display)
        pianoRoll.notes.push(newNote);

        // Save to the current piano pattern if one is selected
        savePianoNotesToPattern();

        // Preview the note
        previewMidiNote(pitch, Math.floor(newNote.velocity * 127));
    }

    pianoRoll.isDragging = false;
    pianoRoll.dragMode = null;
    renderPianoRoll();
}

// Get the currently selected piano pattern (from selected clip)
function getCurrentPianoPattern() {
    var track = state.tracks[state.selectedTrack];
    if (!track || !track.clips) return null;

    // Find selected clip
    var selectedClipEl = document.querySelector('.timeline-clip.selected');
    if (!selectedClipEl) return null;

    var clipId = parseFloat(selectedClipEl.getAttribute('data-clip-id'));
    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipId) {
            var pattern = state.patterns[track.clips[i].patternId];
            if (pattern && pattern.type === 'piano') {
                return pattern;
            }
        }
    }
    return null;
}

// Save piano roll notes to the current pattern
function savePianoNotesToPattern() {
    var pattern = getCurrentPianoPattern();
    if (pattern) {
        pattern.notes = pianoRoll.notes.slice();  // Copy notes array
    }
}

function handlePianoRollDblClick(e) {
    var rect = pianoRoll.canvas.getBoundingClientRect();
    var x = e.clientX - rect.left;
    var y = e.clientY - rect.top;

    // Double-click on note to delete
    var note = findNoteAt(x, y);
    if (note) {
        var idx = pianoRoll.notes.indexOf(note);
        if (idx !== -1) {
            pianoRoll.notes.splice(idx, 1);
            savePianoNotesToPattern();
            renderPianoRoll();
        }
    }
}

function handlePianoRollContextMenu(e) {
    e.preventDefault();
    // Could show quantize menu here
}

function findNoteAt(x, y) {
    var totalNotes = pianoRoll.octaves * 12;
    var clickPitch = pianoRoll.lowestNote + totalNotes - Math.floor(y / pianoRoll.noteHeight) - 1;
    var clickBeat = x / pianoRoll.pixelsPerBeat;

    for (var i = 0; i < pianoRoll.notes.length; i++) {
        var note = pianoRoll.notes[i];
        if (note.pitch === clickPitch &&
            clickBeat >= note.startBeat &&
            clickBeat < note.startBeat + note.duration) {
            return note;
        }
    }
    return null;
}

function quantizeBeat(beat) {
    if (state.quantize === 'off') return beat;

    var grid = getQuantizeGrid();
    return Math.floor(beat / grid) * grid;
}

function getQuantizeGrid() {
    switch (state.quantize) {
        case '1/4': return 1;
        case '1/8': return 0.5;
        case '1/16': return 0.25;
        case '1/32': return 0.125;
        case '1/4T': return 1 / 1.5;
        case '1/8T': return 0.5 / 1.5;
        case '1/16T': return 0.25 / 1.5;
        default: return 0.25;
    }
}

function getQuantizeDuration() {
    return getQuantizeGrid();
}

function addNoteToPatterStep(pitch, beat, duration) {
    var pattern = getCurrentPattern();
    if (!pattern) return;

    var patternLpb = pattern.lpb || state.lpb;
    var step = Math.floor(beat * patternLpb);
    var noteCol = state.focusedNoteCol || 0;

    if (step >= 0 && step < pattern.steps) {
        var stepData = pattern.data[step];
        if (stepData && stepData.columns) {
            // Ensure note column exists
            while (stepData.columns.length <= noteCol) {
                stepData.columns.push({ note: '', amp: '', fx: [] });
            }
            var colData = stepData.columns[noteCol];
            colData.note = midiToNoteName(pitch);
            colData.amp = 'FF';
            invalidatePatternCache(getCurrentPatternIndex());
            renderTrackerGrid(true);
        }
    }
}

function zoomPianoRoll(factor) {
    pianoRoll.pixelsPerBeat = Math.max(10, Math.min(200, pianoRoll.pixelsPerBeat * factor));
    renderPianoRoll();
}

// Track active MIDI preview notes per track
var activeMidiPreviews = {};

function previewMidiNote(midiNote, velocity) {
    if (!state.csoundReady) return;

    var freq = 440 * Math.pow(2, (midiNote - 69) / 12);
    var amp = velocity / 127;
    var trackKey = state.selectedTrack;

    // Use unique fractional instance per MIDI note: trackNum.midiNote (e.g., 1.60 for middle C)
    var instrNum = (state.selectedTrack + 1) + '.' + midiNote.toString().padStart(3, '0');

    // Turn off any existing note on this MIDI key first
    if (activeMidiPreviews[trackKey + '_' + midiNote]) {
        var oldInstr = activeMidiPreviews[trackKey + '_' + midiNote];
        try {
            csound.inputMessage('i 998 0 0.01 ' + oldInstr);
        } catch (err) {}
    }

    try {
        csound.inputMessage('i ' + instrNum + ' 0 -1 ' + freq.toFixed(4) + ' ' + amp.toFixed(4));
        activeMidiPreviews[trackKey + '_' + midiNote] = instrNum;
    } catch (err) {}
}

function stopMidiNote(midiNote) {
    if (!state.csoundReady) return;

    var trackKey = state.selectedTrack;
    var noteKey = trackKey + '_' + midiNote;

    // Get the tracked instrument instance for this MIDI note
    if (activeMidiPreviews[noteKey]) {
        var instrNum = activeMidiPreviews[noteKey];
        try {
            // Use instrument 998 (note killer) for reliable note-off
            csound.inputMessage('i 998 0 0.01 ' + instrNum);
        } catch (err) {}
        delete activeMidiPreviews[noteKey];
    }
}

// ============================================
// MIDI INPUT
// ============================================

var midiAccess = null;
var activeMidiInput = null;
var midiNoteVelocities = {};  // Track note velocities for recording

function initMIDI() {
    if (!navigator.requestMIDIAccess) {
        consoleLog('Web MIDI API not supported');
        return;
    }

    navigator.requestMIDIAccess().then(function(access) {
        midiAccess = access;
        state.midi.enabled = true;
        updateMIDIDeviceList();

        // Listen for device changes
        access.onstatechange = function(e) {
            updateMIDIDeviceList();
        };

        consoleLog('MIDI access granted');
    }).catch(function(err) {
        consoleLog('MIDI access denied: ' + err.message);
    });

    // Setup MIDI input selector
    var select = document.getElementById('midi-input');
    if (select) {
        select.addEventListener('change', function() {
            selectMIDIInput(this.value);
        });
    }
}

function updateMIDIDeviceList() {
    var select = document.getElementById('midi-input');
    if (!select || !midiAccess) return;

    // Remember current selection
    var currentValue = select.value;

    // Clear and rebuild
    select.innerHTML = '<option value="">None</option>';

    midiAccess.inputs.forEach(function(input) {
        var option = document.createElement('option');
        option.value = input.id;
        option.textContent = input.name;
        select.appendChild(option);
    });

    // Restore selection if still available
    if (currentValue) {
        select.value = currentValue;
    }
}

function selectMIDIInput(inputId) {
    // Disconnect previous input
    if (activeMidiInput) {
        activeMidiInput.onmidimessage = null;
        activeMidiInput = null;
    }

    if (!inputId || !midiAccess) {
        state.midi.inputDevice = null;
        return;
    }

    var input = midiAccess.inputs.get(inputId);
    if (input) {
        activeMidiInput = input;
        input.onmidimessage = handleMIDIMessage;
        state.midi.inputDevice = inputId;
        consoleLog('MIDI input: ' + input.name);
    }
}

function handleMIDIMessage(msg) {
    var data = msg.data;
    var status = data[0];
    var command = status >> 4;
    var channel = status & 0x0f;

    switch (command) {
        case 9:  // Note On
            var note = data[1];
            var velocity = data[2];
            if (velocity > 0) {
                handleMIDINoteOn(note, velocity, channel);
            } else {
                handleMIDINoteOff(note, channel);
            }
            break;

        case 8:  // Note Off
            handleMIDINoteOff(data[1], channel);
            break;

        case 11:  // Control Change
            handleMIDICC(data[1], data[2], channel);
            break;

        case 14:  // Pitch Bend
            var bend = ((data[2] << 7) | data[1]) - 8192;
            handleMIDIPitchBend(bend, channel);
            break;
    }
}

function handleMIDINoteOn(note, velocity, channel) {
    midiNoteVelocities[note] = velocity;

    // Preview the note
    previewMidiNote(note, velocity);

    // Record if recording is enabled
    if (state.isRecording) {
        var noteName = midiToNoteName(note);
        var ampHex = Math.round(velocity / 127 * 127).toString(16).toUpperCase().padStart(2, '0');
        var noteCol = state.focusedNoteCol || 0;

        // Record to step sequencer
        var pattern = getCurrentPattern();
        var step = state.focusedStep;

        if (pattern && step < pattern.steps) {
            var stepData = pattern.data[step];
            if (stepData && stepData.columns) {
                // Ensure note column exists
                while (stepData.columns.length <= noteCol) {
                    stepData.columns.push({ note: '', amp: '', fx: [] });
                }
                var colData = stepData.columns[noteCol];
                colData.note = noteName;
                colData.amp = ampHex;

                invalidatePatternCache(getCurrentPatternIndex());
                renderTrackerGrid(true);

                // Move cursor by edit step
                if (state.editStep > 0) {
                    state.focusedStep = Math.min(state.focusedStep + state.editStep, pattern.steps - 1);
                }
            }
        }
    }

    // Visual feedback on piano keys
    var key = document.querySelector('.piano-key[data-note="' + note + '"]');
    if (key) key.classList.add('playing');
}

function handleMIDINoteOff(note, channel) {
    delete midiNoteVelocities[note];
    stopMidiNote(note);

    // Visual feedback
    var key = document.querySelector('.piano-key[data-note="' + note + '"]');
    if (key) key.classList.remove('playing');
}

function handleMIDICC(cc, value, channel) {
    // CC can be mapped to FX columns
    var mapping = state.midi.ccMappings[cc];
    if (mapping && state.isRecording) {
        var pattern = getCurrentPattern();
        var step = state.focusedStep;
        var noteCol = state.focusedNoteCol || 0;

        if (pattern && step < pattern.steps) {
            var stepData = pattern.data[step];
            if (stepData && stepData.columns) {
                // Ensure note column exists
                while (stepData.columns.length <= noteCol) {
                    stepData.columns.push({ note: '', amp: '', fx: [] });
                }
                var colData = stepData.columns[noteCol];
                var fxIdx = mapping.fxColumn || 0;
                if (!colData.fx) colData.fx = [];
                while (colData.fx.length <= fxIdx) {
                    colData.fx.push('');
                }
                colData.fx[fxIdx] = value.toString(16).toUpperCase().padStart(4, '0');

                invalidatePatternCache(getCurrentPatternIndex());
                renderTrackerGrid(true);
            }
        }
    }
}

function handleMIDIPitchBend(bend, channel) {
    // Pitch bend range: -8192 to +8191
    // Could be mapped to a parameter or used for live pitch adjustment
    // For now, just log it
    // consoleLog('Pitch bend: ' + bend);
}

// ============================================
// SAMPLE EDITOR
// ============================================

function initSampleEditor() {
    sampleEditor.canvas = document.getElementById('waveform-canvas');
    sampleEditor.ctx = sampleEditor.canvas ? sampleEditor.canvas.getContext('2d') : null;

    // Editor view tab switching
    var viewTabs = document.querySelectorAll('.editor-view-tab');
    viewTabs.forEach(function(tab) {
        tab.addEventListener('click', function() {
            var view = this.getAttribute('data-view');
            switchEditorView(view);
        });
    });

    // Sample editor controls
    var btnZoomIn = document.getElementById('btn-zoom-in');
    var btnZoomOut = document.getElementById('btn-zoom-out');
    var btnZoomFit = document.getElementById('btn-zoom-fit');
    var btnAddSlice = document.getElementById('btn-add-slice');
    var btnRemoveSlice = document.getElementById('btn-remove-slice');
    var btnAutoSlice = document.getElementById('btn-auto-slice');

    if (btnZoomIn) btnZoomIn.addEventListener('click', function() { zoomWaveform(1.5); });
    if (btnZoomOut) btnZoomOut.addEventListener('click', function() { zoomWaveform(0.67); });
    if (btnZoomFit) btnZoomFit.addEventListener('click', fitWaveformToView);
    if (btnAddSlice) btnAddSlice.addEventListener('click', addSliceAtSelection);
    if (btnRemoveSlice) btnRemoveSlice.addEventListener('click', removeSelectedSlice);
    if (btnAutoSlice) btnAutoSlice.addEventListener('click', autoSlice);

    // Insert slices to instrument button
    var btnInsertSlices = document.getElementById('btn-insert-slices');
    if (btnInsertSlices) btnInsertSlices.addEventListener('click', insertSlicesToInstrument);

    // Chop to sample bank button
    var btnToSampleBank = document.getElementById('btn-to-sample-bank');
    if (btnToSampleBank) btnToSampleBank.addEventListener('click', chopToSampleBank);

    // Play/Stop buttons
    var btnPlaySample = document.getElementById('btn-play-sample');
    var btnStopSample = document.getElementById('btn-stop-sample');
    if (btnPlaySample) btnPlaySample.addEventListener('click', playSampleInEditor);
    if (btnStopSample) btnStopSample.addEventListener('click', stopSamplePlayback);

    // Canvas interaction
    if (sampleEditor.canvas) {
        sampleEditor.canvas.addEventListener('mousedown', handleWaveformMouseDown);
        sampleEditor.canvas.addEventListener('mousemove', handleWaveformMouseMove);
        sampleEditor.canvas.addEventListener('mouseup', handleWaveformMouseUp);
        sampleEditor.canvas.addEventListener('wheel', handleWaveformWheel, { passive: false });

        // Handle canvas resize
        window.addEventListener('resize', function() {
            if (sampleEditor.audioBuffer) {
                resizeCanvas();
                renderWaveform();
            }
        });
    }

    // Scrollbar interaction
    var scrollbar = document.getElementById('waveform-scrollbar');
    if (scrollbar) {
        scrollbar.addEventListener('input', function() {
            if (sampleEditor.waveformData) {
                sampleEditor.scrollOffset = parseFloat(this.value);
                renderWaveform();
            }
        });
    }

    // Keyboard shortcuts for sample editor (Delete, Ctrl+Z)
    document.addEventListener('keydown', function(e) {
        // Only handle when sample editor view is visible
        var sampleView = document.getElementById('sample-editor-view');
        if (!sampleView || sampleView.classList.contains('hidden')) return;

        // Don't handle if focus is in a text input
        if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

        // Delete key - delete selection (or entire sample if no selection)
        if (e.key === 'Delete' && !e.ctrlKey && !e.altKey && !e.shiftKey) {
            if (sampleEditor.currentSample) {
                e.preventDefault();
                deleteSelection();
                return;
            }
        }

        // Ctrl+Z - undo
        if (e.ctrlKey && e.key === 'z' && !e.shiftKey && !e.altKey) {
            if (sampleEditor.currentSample) {
                e.preventDefault();
                sampleEditorUndo();
                return;
            }
        }
    });
}

function switchEditorView(view) {
    // Handle main view tabs (pattern vs sample)
    var tabs = document.querySelectorAll('.editor-view-tab');
    tabs.forEach(function(t) {
        var tabView = t.getAttribute('data-view');
        t.classList.toggle('active', tabView === view);
    });

    // Main views: pattern-editor-area vs sample-editor-view
    var sampleView = document.getElementById('sample-editor-view');
    var patternEditorArea = document.getElementById('pattern-editor-area');

    if (sampleView) sampleView.classList.toggle('hidden', view !== 'sample');
    if (patternEditorArea) patternEditorArea.classList.toggle('hidden', view === 'sample');

    // Resize and render waveform when switching to sample view
    if (view === 'sample' && sampleEditor.audioBuffer) {
        setTimeout(function() {
            resizeCanvas();
            renderWaveform();
        }, 50);
    }
}

async function loadSampleIntoEditor(sample) {
    if (!sample) {
        consoleLog('No sample provided');
        return;
    }

    // Check if we have decoded audio data
    if (!sample.audioBuffer && !sample.rawData) {
        consoleLog('Sample has no audio data');
        return;
    }

    sampleEditor.currentSample = sample;

    // Switch to sample editor view
    switchEditorView('sample');

    try {
        // Use pre-decoded audioBuffer if available, otherwise decode from rawData
        if (sample.audioBuffer) {
            sampleEditor.audioBuffer = sample.audioBuffer;
        } else if (sample.rawData) {
            var audioCtxTemp = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
            var arrayBuffer = sample.rawData.slice(0); // Clone the ArrayBuffer
            sampleEditor.audioBuffer = await audioCtxTemp.decodeAudioData(arrayBuffer);
            // Store for future use
            sample.audioBuffer = sampleEditor.audioBuffer;
            sample.audioArray = sampleEditor.audioBuffer.getChannelData(0);
        }

        // Load existing slices if any
        sampleEditor.slices = sample.slices ? sample.slices.slice() : [];
        sampleEditor.selectedSlice = -1;
        sampleEditor.selection = null;
        sampleEditor.zoom = 1;
        sampleEditor.scrollOffset = 0;
        sampleEditor.undoStack = []; // Clear undo stack for new sample

        // Update display
        updateSampleEditorInfo();
        resizeCanvas();
        computeWaveformData();
        renderWaveform();
        renderSliceList();
        updateSliceInitCode();

        consoleLog('Loaded ' + sample.name + ' into editor (' + sampleEditor.audioBuffer.length + ' samples)');
    } catch (err) {
        consoleLog('Error loading sample into editor: ' + err.message);
        console.error(err);
    }
}

function updateSampleEditorInfo() {
    var nameEl = document.getElementById('sample-editor-name');
    var infoEl = document.getElementById('sample-editor-info');

    if (sampleEditor.currentSample) {
        var sample = sampleEditor.currentSample;
        nameEl.textContent = sample.name + ' (ft' + sample.tableNum + ')';

        // Build detailed info string from WAV metadata
        var info = [];

        // Format type
        if (sample.format) {
            var formatStr = sample.format;
            if (sample.subFormat) formatStr += '/' + sample.subFormat;
            info.push(formatStr);
        }

        // Channels
        info.push(sample.channels + 'ch');

        // Sample rate
        info.push(sample.sampleRate + 'Hz');

        // Bit depth
        if (sample.bitsPerSample) {
            var bitStr = sample.bitsPerSample + 'bit';
            if (sample.validBitsPerSample && sample.validBitsPerSample !== sample.bitsPerSample) {
                bitStr += '(' + sample.validBitsPerSample + ')';
            }
            info.push(bitStr);
        }

        // Sample count
        info.push(sample.numSamples + ' samples');

        // Duration
        if (sample.duration) {
            info.push(sample.duration.toFixed(3) + 's');
        }

        infoEl.textContent = info.join(' | ');
    } else {
        nameEl.textContent = 'No sample loaded';
        infoEl.textContent = '';
    }
}

function resizeCanvas() {
    if (!sampleEditor.canvas) return;

    var container = sampleEditor.canvas.parentElement;
    var rect = container.getBoundingClientRect();

    sampleEditor.canvas.width = rect.width;
    sampleEditor.canvas.height = rect.height;
}

function computeWaveformData() {
    if (!sampleEditor.audioBuffer) {
        sampleEditor.waveformData = null;
        return;
    }

    var buf = sampleEditor.audioBuffer;
    var channelData = buf.getChannelData(0); // Use first channel
    var length = channelData.length;

    // Compute peaks at multiple resolutions for efficient rendering
    var blockSize = 256;
    var numBlocks = Math.ceil(length / blockSize);
    var peaks = new Float32Array(numBlocks * 2); // min and max per block

    for (var i = 0; i < numBlocks; i++) {
        var start = i * blockSize;
        var end = Math.min(start + blockSize, length);
        var min = 1, max = -1;

        for (var j = start; j < end; j++) {
            var val = channelData[j];
            if (val < min) min = val;
            if (val > max) max = val;
        }

        peaks[i * 2] = min;
        peaks[i * 2 + 1] = max;
    }

    sampleEditor.waveformData = {
        peaks: peaks,
        blockSize: blockSize,
        numBlocks: numBlocks,
        totalSamples: length
    };
}

function renderWaveform() {
    if (!sampleEditor.ctx || !sampleEditor.canvas) return;

    var ctx = sampleEditor.ctx;
    var canvas = sampleEditor.canvas;
    var width = canvas.width;
    var height = canvas.height;

    // Clear canvas
    ctx.fillStyle = '#0a0a14';
    ctx.fillRect(0, 0, width, height);

    if (!sampleEditor.audioBuffer || !sampleEditor.waveformData) {
        // Draw placeholder text
        ctx.fillStyle = '#333';
        ctx.font = '14px Courier New';
        ctx.textAlign = 'center';
        ctx.fillText('Select a sample from the browser to edit', width / 2, height / 2);
        return;
    }

    var data = sampleEditor.waveformData;
    var buf = sampleEditor.audioBuffer;
    var totalSamples = data.totalSamples;

    // Calculate visible range based on zoom and scroll
    var visibleSamples = totalSamples / sampleEditor.zoom;
    var startSample = sampleEditor.scrollOffset;
    var endSample = startSample + visibleSamples;

    // Clamp
    if (endSample > totalSamples) {
        endSample = totalSamples;
        startSample = Math.max(0, endSample - visibleSamples);
    }

    // Draw center line
    ctx.strokeStyle = '#1a1a2e';
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, height / 2);
    ctx.lineTo(width, height / 2);
    ctx.stroke();

    var samplesPerPixel = visibleSamples / width;
    var midY = height / 2;
    var amplitude = height / 2 - 10;

    // Get raw channel data for line drawing
    var channelData = buf.getChannelData(0);

    if (samplesPerPixel <= 1) {
        // Zoomed in: draw every sample as a point connected by lines
        var pixelsPerSample = 1 / samplesPerPixel;

        ctx.strokeStyle = '#4ecca3';
        ctx.lineWidth = 1.5;
        ctx.beginPath();

        var firstPoint = true;
        for (var i = Math.floor(startSample); i < Math.ceil(endSample) && i < channelData.length; i++) {
            var x = (i - startSample) * pixelsPerSample;
            var y = midY - channelData[i] * amplitude;

            if (firstPoint) {
                ctx.moveTo(x, y);
                firstPoint = false;
            } else {
                ctx.lineTo(x, y);
            }
        }
        ctx.stroke();

        // Draw sample points as circles when zoomed in very far
        if (samplesPerPixel < 0.3) {
            ctx.fillStyle = '#6fffca';
            for (var i = Math.floor(startSample); i < Math.ceil(endSample) && i < channelData.length; i++) {
                var x = (i - startSample) * pixelsPerSample;
                var y = midY - channelData[i] * amplitude;
                ctx.beginPath();
                ctx.arc(x, y, 3, 0, Math.PI * 2);
                ctx.fill();
            }
        }
    } else {
        // Zoomed out: draw min/max envelope as two lines with fill between
        var mins = [];
        var maxs = [];

        for (var x = 0; x < width; x++) {
            var sampleStart = Math.floor(startSample + x * samplesPerPixel);
            var sampleEnd = Math.floor(startSample + (x + 1) * samplesPerPixel);
            if (sampleEnd > channelData.length) sampleEnd = channelData.length;
            if (sampleStart < 0) sampleStart = 0;

            var min = 1, max = -1;
            for (var i = sampleStart; i < sampleEnd; i++) {
                var val = channelData[i];
                if (val < min) min = val;
                if (val > max) max = val;
            }

            // If no samples in range, use last known value
            if (min > max) {
                min = max = sampleStart < channelData.length ? channelData[sampleStart] : 0;
            }

            mins.push(min);
            maxs.push(max);
        }

        // Draw the min line (bottom edge)
        ctx.strokeStyle = '#4ecca3';
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(0, midY - mins[0] * amplitude);
        for (var x = 1; x < width; x++) {
            ctx.lineTo(x, midY - mins[x] * amplitude);
        }
        ctx.stroke();

        // Draw the max line (top edge)
        ctx.beginPath();
        ctx.moveTo(0, midY - maxs[0] * amplitude);
        for (var x = 1; x < width; x++) {
            ctx.lineTo(x, midY - maxs[x] * amplitude);
        }
        ctx.stroke();

        // Draw vertical lines connecting min to max at each pixel for filled look
        ctx.strokeStyle = 'rgba(78, 204, 163, 0.5)';
        ctx.lineWidth = 1;
        for (var x = 0; x < width; x++) {
            var y1 = midY - maxs[x] * amplitude;
            var y2 = midY - mins[x] * amplitude;
            if (Math.abs(y2 - y1) > 1) {
                ctx.beginPath();
                ctx.moveTo(x, y1);
                ctx.lineTo(x, y2);
                ctx.stroke();
            }
        }
    }

    // Draw selection
    if (sampleEditor.selection) {
        var selStartX = sampleToPixel(sampleEditor.selection.start);
        var selEndX = sampleToPixel(sampleEditor.selection.end);
        if (selStartX > selEndX) {
            var tmp = selStartX; selStartX = selEndX; selEndX = tmp;
        }
        ctx.fillStyle = 'rgba(78, 204, 163, 0.2)';
        ctx.fillRect(selStartX, 0, selEndX - selStartX, height);
        ctx.strokeStyle = '#4ecca3';
        ctx.lineWidth = 1;
        ctx.strokeRect(selStartX, 0, selEndX - selStartX, height);
    }

    // Draw slice markers
    ctx.lineWidth = 2;
    for (var i = 0; i < sampleEditor.slices.length; i++) {
        var slicePos = sampleEditor.slices[i];
        var x = sampleToPixel(slicePos);

        if (x >= 0 && x <= width) {
            ctx.strokeStyle = i === sampleEditor.selectedSlice ? '#4ecca3' : '#e94560';
            ctx.beginPath();
            ctx.moveTo(x, 0);
            ctx.lineTo(x, height);
            ctx.stroke();

            // Draw slice number
            ctx.fillStyle = i === sampleEditor.selectedSlice ? '#4ecca3' : '#e94560';
            ctx.font = 'bold 10px Courier New';
            ctx.textAlign = 'left';
            ctx.fillText((i + 1).toString(), x + 3, 12);
        }
    }

    // Update scrollbar
    updateWaveformScrollbar();
}

function sampleToPixel(samplePos) {
    if (!sampleEditor.canvas || !sampleEditor.waveformData) return 0;

    var totalSamples = sampleEditor.waveformData.totalSamples;
    var visibleSamples = totalSamples / sampleEditor.zoom;
    var startSample = sampleEditor.scrollOffset;

    return ((samplePos - startSample) / visibleSamples) * sampleEditor.canvas.width;
}

function pixelToSample(pixelX) {
    if (!sampleEditor.canvas || !sampleEditor.waveformData) return 0;

    var totalSamples = sampleEditor.waveformData.totalSamples;
    var visibleSamples = totalSamples / sampleEditor.zoom;
    var startSample = sampleEditor.scrollOffset;

    return Math.floor(startSample + (pixelX / sampleEditor.canvas.width) * visibleSamples);
}

function zoomWaveform(factor) {
    if (!sampleEditor.audioBuffer) return;

    var oldZoom = sampleEditor.zoom;
    sampleEditor.zoom = Math.max(1, Math.min(100, sampleEditor.zoom * factor));

    // Adjust scroll to keep center point
    var totalSamples = sampleEditor.waveformData.totalSamples;
    var oldVisibleSamples = totalSamples / oldZoom;
    var newVisibleSamples = totalSamples / sampleEditor.zoom;
    var centerSample = sampleEditor.scrollOffset + oldVisibleSamples / 2;

    sampleEditor.scrollOffset = Math.max(0, centerSample - newVisibleSamples / 2);

    renderWaveform();
}

function fitWaveformToView() {
    sampleEditor.zoom = 1;
    sampleEditor.scrollOffset = 0;
    renderWaveform();
}

function handleWaveformMouseDown(e) {
    if (!sampleEditor.audioBuffer) return;

    var rect = sampleEditor.canvas.getBoundingClientRect();
    var x = e.clientX - rect.left;
    var samplePos = pixelToSample(x);

    // Check if clicking on a slice marker
    var sliceHit = -1;
    for (var i = 0; i < sampleEditor.slices.length; i++) {
        var sliceX = sampleToPixel(sampleEditor.slices[i]);
        if (Math.abs(x - sliceX) < 8) {
            sliceHit = i;
            break;
        }
    }

    if (sliceHit >= 0) {
        // Start dragging slice
        sampleEditor.isDragging = true;
        sampleEditor.dragSliceIndex = sliceHit;
        sampleEditor.selectedSlice = sliceHit;
        renderSliceList();
    } else {
        // Start selection
        sampleEditor.selection = { start: samplePos, end: samplePos };
        sampleEditor.selectedSlice = -1;
        sampleEditor.isDragging = false;
    }

    renderWaveform();
}

function handleWaveformMouseMove(e) {
    if (!sampleEditor.audioBuffer) return;

    var rect = sampleEditor.canvas.getBoundingClientRect();
    var x = e.clientX - rect.left;
    var samplePos = pixelToSample(x);

    if (sampleEditor.isDragging && sampleEditor.dragSliceIndex >= 0) {
        // Dragging a slice marker
        samplePos = Math.max(0, Math.min(sampleEditor.waveformData.totalSamples - 1, samplePos));
        sampleEditor.slices[sampleEditor.dragSliceIndex] = samplePos;
        renderWaveform();
        updateSliceInitCode();
    } else if (sampleEditor.selection && e.buttons === 1) {
        // Extending selection
        sampleEditor.selection.end = samplePos;
        renderWaveform();
    } else {
        // Update cursor based on hover
        var nearSlice = false;
        for (var i = 0; i < sampleEditor.slices.length; i++) {
            var sliceX = sampleToPixel(sampleEditor.slices[i]);
            if (Math.abs(x - sliceX) < 8) {
                nearSlice = true;
                break;
            }
        }
        sampleEditor.canvas.style.cursor = nearSlice ? 'ew-resize' : 'crosshair';
    }
}

function handleWaveformMouseUp(e) {
    if (sampleEditor.isDragging) {
        sampleEditor.isDragging = false;
        // Sort slices after drag
        sampleEditor.slices.sort(function(a, b) { return a - b; });
        renderSliceList();
        saveSampleSlices();
    }
    renderWaveform();
}

function handleWaveformWheel(e) {
    if (!sampleEditor.audioBuffer) return;
    e.preventDefault();

    // Get mouse position for zoom centering
    var rect = sampleEditor.canvas.getBoundingClientRect();
    var mouseX = e.clientX - rect.left;
    var mouseSample = pixelToSample(mouseX);

    // Scroll up = zoom in, Scroll down = zoom out
    var factor = e.deltaY < 0 ? 1.3 : 0.77;
    sampleEditor.zoom = Math.max(1, Math.min(500, sampleEditor.zoom * factor));

    // Adjust scroll to keep mouse position stable
    var totalSamples = sampleEditor.waveformData.totalSamples;
    var newVisibleSamples = totalSamples / sampleEditor.zoom;
    var mouseRatio = mouseX / sampleEditor.canvas.width;

    sampleEditor.scrollOffset = Math.max(0,
        Math.min(totalSamples - newVisibleSamples, mouseSample - newVisibleSamples * mouseRatio));

    renderWaveform();
}

// Scrollbar update function
function updateWaveformScrollbar() {
    var scrollbar = document.getElementById('waveform-scrollbar');
    if (!scrollbar || !sampleEditor.waveformData) return;

    var totalSamples = sampleEditor.waveformData.totalSamples;
    var visibleSamples = totalSamples / sampleEditor.zoom;

    // Update scrollbar value and max
    scrollbar.max = Math.max(0, totalSamples - visibleSamples);
    scrollbar.value = sampleEditor.scrollOffset;
}

// Undo support for sample editor - stores audio data for full undo
function pushSampleEditorUndo() {
    // Clone the audio buffer data for undo
    var audioData = null;
    if (sampleEditor.audioBuffer) {
        audioData = [];
        for (var ch = 0; ch < sampleEditor.audioBuffer.numberOfChannels; ch++) {
            audioData.push(new Float32Array(sampleEditor.audioBuffer.getChannelData(ch)));
        }
    }

    var undoState = {
        slices: sampleEditor.slices.slice(),
        selectedSlice: sampleEditor.selectedSlice,
        audioData: audioData,
        sampleRate: sampleEditor.audioBuffer ? sampleEditor.audioBuffer.sampleRate : 44100,
        numberOfChannels: sampleEditor.audioBuffer ? sampleEditor.audioBuffer.numberOfChannels : 1
    };
    sampleEditor.undoStack.push(undoState);
    if (sampleEditor.undoStack.length > sampleEditor.maxUndo) {
        sampleEditor.undoStack.shift();
    }
}

function sampleEditorUndo() {
    if (sampleEditor.undoStack.length === 0) {
        consoleLog('Nothing to undo');
        return;
    }

    var undoState = sampleEditor.undoStack.pop();
    sampleEditor.slices = undoState.slices;
    sampleEditor.selectedSlice = undoState.selectedSlice;

    // Restore audio buffer if it was saved
    if (undoState.audioData && undoState.audioData.length > 0) {
        var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
        var length = undoState.audioData[0].length;
        var newBuffer = ctx.createBuffer(undoState.numberOfChannels, length, undoState.sampleRate);

        for (var ch = 0; ch < undoState.numberOfChannels; ch++) {
            newBuffer.getChannelData(ch).set(undoState.audioData[ch]);
        }

        sampleEditor.audioBuffer = newBuffer;

        // Update the current sample reference
        if (sampleEditor.currentSample) {
            sampleEditor.currentSample.audioBuffer = newBuffer;
            sampleEditor.currentSample.audioArray = newBuffer.getChannelData(0);
            sampleEditor.currentSample.numSamples = length;
            sampleEditor.currentSample.duration = length / undoState.sampleRate;
        }

        // Recompute waveform data
        computeWaveformData();
        updateSampleEditorInfo();
    }

    renderWaveform();
    renderSliceList();
    updateSliceInitCode();
    saveSampleSlices();
    consoleLog('Undo');
}

// Delete selected portion of the waveform (or entire sample if no selection)
async function deleteSelection() {
    if (!sampleEditor.audioBuffer) {
        consoleLog('No sample loaded');
        return;
    }

    // If no selection, delete the entire sample
    if (!sampleEditor.selection) {
        deleteCurrentSample();
        return;
    }

    var selStart = Math.min(sampleEditor.selection.start, sampleEditor.selection.end);
    var selEnd = Math.max(sampleEditor.selection.start, sampleEditor.selection.end);

    // Make sure selection is valid
    if (selStart < 0) selStart = 0;
    if (selEnd > sampleEditor.audioBuffer.length) selEnd = sampleEditor.audioBuffer.length;

    var deleteLength = selEnd - selStart;
    if (deleteLength <= 0) {
        consoleLog('No selection to delete');
        return;
    }

    // Push undo state before modification
    pushSampleEditorUndo();

    var oldBuffer = sampleEditor.audioBuffer;
    var newLength = oldBuffer.length - deleteLength;

    if (newLength <= 0) {
        consoleLog('Cannot delete entire sample - use Delete without selection');
        sampleEditor.undoStack.pop(); // Remove the undo state we just added
        return;
    }

    // Create new smaller AudioBuffer
    var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
    var newBuffer = ctx.createBuffer(
        oldBuffer.numberOfChannels,
        newLength,
        oldBuffer.sampleRate
    );

    // Copy audio data, excluding the selection
    for (var ch = 0; ch < oldBuffer.numberOfChannels; ch++) {
        var oldData = oldBuffer.getChannelData(ch);
        var newData = newBuffer.getChannelData(ch);

        // Copy samples before selection
        for (var i = 0; i < selStart; i++) {
            newData[i] = oldData[i];
        }

        // Copy samples after selection
        for (var i = selEnd; i < oldBuffer.length; i++) {
            newData[i - deleteLength] = oldData[i];
        }
    }

    // Update the audio buffer
    sampleEditor.audioBuffer = newBuffer;

    // Update slice markers - remove slices in deleted region, shift others
    var newSlices = [];
    for (var i = 0; i < sampleEditor.slices.length; i++) {
        var slicePos = sampleEditor.slices[i];
        if (slicePos < selStart) {
            // Slice is before deletion - keep as is
            newSlices.push(slicePos);
        } else if (slicePos >= selEnd) {
            // Slice is after deletion - shift back
            newSlices.push(slicePos - deleteLength);
        }
        // Slices within the deleted region are removed
    }
    sampleEditor.slices = newSlices;
    sampleEditor.selectedSlice = -1;

    // Clear selection
    sampleEditor.selection = null;

    // Clamp scroll offset
    var totalSamples = newLength;
    var visibleSamples = totalSamples / sampleEditor.zoom;
    if (sampleEditor.scrollOffset + visibleSamples > totalSamples) {
        sampleEditor.scrollOffset = Math.max(0, totalSamples - visibleSamples);
    }

    // Update the sample object
    if (sampleEditor.currentSample) {
        sampleEditor.currentSample.audioBuffer = newBuffer;
        sampleEditor.currentSample.audioArray = newBuffer.getChannelData(0);
        sampleEditor.currentSample.numSamples = newLength;
        sampleEditor.currentSample.duration = newLength / newBuffer.sampleRate;

        // Update Csound ftable with new audio data
        await updateSampleInCsound(sampleEditor.currentSample);
    }

    // Recompute waveform data and render
    computeWaveformData();
    updateSampleEditorInfo();
    renderWaveform();
    renderSliceList();
    updateSliceInitCode();
    saveSampleSlices();

    consoleLog('Deleted ' + deleteLength + ' samples (' + (deleteLength / newBuffer.sampleRate).toFixed(3) + 's)');
}

// Insert slice i-values into the current instrument and recompile
async function insertSlicesToInstrument() {
    if (!sampleEditor.currentSample) {
        consoleLog('No sample loaded');
        return;
    }

    if (sampleEditor.slices.length === 0) {
        consoleLog('No slices to insert');
        return;
    }

    // Generate slice init code
    var sliceCode = '; Slice markers for ' + sampleEditor.currentSample.name + '\n';
    sliceCode += 'itable = ' + sampleEditor.currentSample.tableNum + '\n';

    for (var i = 0; i < sampleEditor.slices.length; i++) {
        sliceCode += 'islice' + (i + 1) + ' = ' + sampleEditor.slices[i] + '\n';
    }

    // Also add slice count and total length
    sliceCode += 'inumslices = ' + sampleEditor.slices.length + '\n';
    if (sampleEditor.audioBuffer) {
        sliceCode += 'isamplelength = ' + sampleEditor.audioBuffer.length + '\n';
        sliceCode += 'isamplerate = ' + sampleEditor.audioBuffer.sampleRate + '\n';
    }

    // Get current instrument code
    saveCurrentInstrument();
    var instrCode = state.instruments[state.currentInstrument];

    // Find the "instr X" line and insert slice code after it
    var instrMatch = instrCode.match(/^(\s*instr\s+\d+\s*\n)/m);
    if (instrMatch) {
        var insertPos = instrMatch.index + instrMatch[0].length;

        // Check if there's already slice code (to replace it)
        var existingSliceMatch = instrCode.match(/; Slice markers for[\s\S]*?(?=\n[a-zA-Z]|\nendin)/);
        if (existingSliceMatch) {
            // Replace existing slice code
            instrCode = instrCode.replace(existingSliceMatch[0], sliceCode.trim());
        } else {
            // Insert new slice code after instr line
            instrCode = instrCode.slice(0, insertPos) + sliceCode + instrCode.slice(insertPos);
        }
    } else {
        // No instr line found, just prepend
        instrCode = sliceCode + instrCode;
    }

    // Update the instrument code
    state.instruments[state.currentInstrument] = instrCode;
    document.getElementById('code-editor').value = instrCode;

    // Switch to instruments tab and show the updated code
    var mainTabs = document.querySelectorAll('.main-tab');
    mainTabs.forEach(function(t) { t.classList.remove('active'); });
    document.querySelector('.main-tab[data-tab="instruments"]').classList.add('active');

    document.querySelectorAll('.tab-content').forEach(function(content) {
        content.classList.add('hidden');
    });
    document.getElementById('tab-instruments').classList.remove('hidden');

    // Make sure we're showing the correct instrument tab
    var instrTabs = document.querySelectorAll('.instr-tab');
    instrTabs.forEach(function(t) {
        t.classList.toggle('active', parseInt(t.getAttribute('data-instr')) === state.currentInstrument);
    });

    // Compile the updated instrument
    await compileInstruments();

    consoleLog('Inserted ' + sampleEditor.slices.length + ' slice values into instrument ' + (state.currentInstrument + 1));
}

// Chop sample at slice markers and add each slice to the sample bank
async function chopToSampleBank() {
    if (!sampleEditor.currentSample || !sampleEditor.audioBuffer) {
        consoleLog('No sample loaded');
        return;
    }

    if (sampleEditor.slices.length === 0) {
        consoleLog('No slice markers - add slices first');
        return;
    }

    var buf = sampleEditor.audioBuffer;
    var baseName = sampleEditor.currentSample.name.replace(/\.[^/.]+$/, ''); // Remove extension
    var baseTableNum = getNextFtableNum();

    // Create slice regions (from each slice to the next, plus start to first slice)
    var regions = [];

    // First region: start to first slice (if first slice isn't at 0)
    if (sampleEditor.slices[0] > 0) {
        regions.push({ start: 0, end: sampleEditor.slices[0] });
    }

    // Middle regions: between slices
    for (var i = 0; i < sampleEditor.slices.length; i++) {
        var start = sampleEditor.slices[i];
        var end = (i < sampleEditor.slices.length - 1) ? sampleEditor.slices[i + 1] : buf.length;
        if (end > start) {
            regions.push({ start: start, end: end });
        }
    }

    consoleLog('Creating ' + regions.length + ' samples from slices...');

    var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
    var createdCount = 0;

    for (var i = 0; i < regions.length; i++) {
        var region = regions[i];
        var sliceLength = region.end - region.start;

        if (sliceLength <= 0) continue;

        // Create new AudioBuffer for this slice
        var sliceBuffer = ctx.createBuffer(
            buf.numberOfChannels,
            sliceLength,
            buf.sampleRate
        );

        // Copy audio data
        for (var ch = 0; ch < buf.numberOfChannels; ch++) {
            var sourceData = buf.getChannelData(ch);
            var destData = sliceBuffer.getChannelData(ch);
            for (var j = 0; j < sliceLength; j++) {
                destData[j] = sourceData[region.start + j];
            }
        }

        // Create sample object
        var tableNum = baseTableNum + createdCount;
        var sliceName = baseName + '_slice' + (i + 1) + '.wav';
        var fileName = '/' + sliceName.replace(/[^a-zA-Z0-9._-]/g, '_');

        // Convert to WAV and upload to Csound
        var wavData = audioBufferToWav(sliceBuffer);

        try {
            await csound.fs.writeFile(fileName, new Uint8Array(wavData));
            var ftableScore = 'f ' + tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
            await csound.readScore(ftableScore);

            // Add to sample list
            var sampleObj = {
                name: sliceName,
                tableNum: tableNum,
                fileName: fileName,
                rawData: wavData,
                audioBuffer: sliceBuffer,
                audioArray: sliceBuffer.getChannelData(0),
                format: 'PCM',
                channels: sliceBuffer.numberOfChannels,
                sampleRate: sliceBuffer.sampleRate,
                bitsPerSample: 16,
                numSamples: sliceBuffer.length,
                duration: sliceBuffer.length / sliceBuffer.sampleRate,
                slices: []
            };

            state.samples.push(sampleObj);

            // Register in new ftable tracking system
            state.usedFtables[tableNum] = true;
            state.ftablePool.push({
                tableNum: tableNum,
                libraryId: null,
                name: sliceName,
                fileName: fileName,
                audioBuffer: sliceBuffer,
                duration: sliceBuffer.length / sliceBuffer.sampleRate,
                sampleRate: sliceBuffer.sampleRate,
                channels: sliceBuffer.numberOfChannels
            });

            createdCount++;
        } catch (err) {
            consoleLog('Error creating slice ' + (i + 1) + ': ' + err.message);
        }
    }

    renderSampleList();
    renderFtablePool();
    updateNextFtableDisplay();
    consoleLog('Created ' + createdCount + ' samples from slices (ft' + baseTableNum + '-' + (baseTableNum + createdCount - 1) + ')');
}

// Sample playback state
var samplePlaybackSource = null;
var samplePlaybackCtx = null;

// Play sample in editor (selection or whole sample)
function playSampleInEditor() {
    if (!sampleEditor.audioBuffer) {
        consoleLog('No sample loaded');
        return;
    }

    // Stop any current playback
    stopSamplePlayback();

    var buf = sampleEditor.audioBuffer;
    var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
    samplePlaybackCtx = ctx;

    // Determine play range
    var startSample = 0;
    var endSample = buf.length;

    if (sampleEditor.selection) {
        startSample = Math.min(sampleEditor.selection.start, sampleEditor.selection.end);
        endSample = Math.max(sampleEditor.selection.start, sampleEditor.selection.end);
        if (startSample < 0) startSample = 0;
        if (endSample > buf.length) endSample = buf.length;
    }

    var playLength = endSample - startSample;
    if (playLength <= 0) return;

    // Create a buffer for the portion to play
    var playBuffer;
    if (startSample === 0 && endSample === buf.length) {
        playBuffer = buf;
    } else {
        playBuffer = ctx.createBuffer(buf.numberOfChannels, playLength, buf.sampleRate);
        for (var ch = 0; ch < buf.numberOfChannels; ch++) {
            var sourceData = buf.getChannelData(ch);
            var destData = playBuffer.getChannelData(ch);
            for (var i = 0; i < playLength; i++) {
                destData[i] = sourceData[startSample + i];
            }
        }
    }

    // Create and play source
    samplePlaybackSource = ctx.createBufferSource();
    samplePlaybackSource.buffer = playBuffer;
    samplePlaybackSource.connect(ctx.destination);
    samplePlaybackSource.onended = function() {
        samplePlaybackSource = null;
    };
    samplePlaybackSource.start();

    var duration = playLength / buf.sampleRate;
    consoleLog('Playing ' + duration.toFixed(2) + 's');
}

// Stop sample playback
function stopSamplePlayback() {
    if (samplePlaybackSource) {
        try {
            samplePlaybackSource.stop();
        } catch (e) {}
        samplePlaybackSource = null;
    }
}

// Play a sample from the sample bank by table number
function playSampleFromBank(tableNum) {
    var sample = state.samples.find(function(s) { return s.tableNum === tableNum; });
    if (!sample) {
        consoleLog('Sample not found: ft' + tableNum);
        return;
    }

    // Stop any current playback
    stopSamplePlayback();

    var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
    samplePlaybackCtx = ctx;

    // Get or create audio buffer
    var buf = sample.audioBuffer;
    if (!buf && sample.rawData) {
        // Need to decode - do it async
        ctx.decodeAudioData(sample.rawData.slice(0)).then(function(decodedBuf) {
            sample.audioBuffer = decodedBuf;
            playSampleBuffer(decodedBuf, ctx);
        }).catch(function(err) {
            consoleLog('Error decoding sample: ' + err.message);
        });
        return;
    }

    if (buf) {
        playSampleBuffer(buf, ctx);
    }
}

// Play a sample from the library (by library ID)
function playLibrarySample(libraryId) {
    var item = state.sampleLibrary.find(function(s) { return s.id == libraryId; });
    if (!item || !item.rawData) {
        consoleLog('Library sample not found');
        return;
    }

    stopSamplePlayback();

    var ctx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
    samplePlaybackCtx = ctx;

    if (item.audioBuffer) {
        playSampleBuffer(item.audioBuffer, ctx);
    } else {
        ctx.decodeAudioData(item.rawData.slice(0)).then(function(decodedBuf) {
            item.audioBuffer = decodedBuf;
            playSampleBuffer(decodedBuf, ctx);
        }).catch(function(err) {
            consoleLog('Error decoding library sample: ' + err.message);
        });
    }
}

function playSampleBuffer(buf, ctx) {
    samplePlaybackSource = ctx.createBufferSource();
    samplePlaybackSource.buffer = buf;
    samplePlaybackSource.connect(ctx.destination);
    samplePlaybackSource.onended = function() {
        samplePlaybackSource = null;
    };
    samplePlaybackSource.start();
    consoleLog('Playing ' + (buf.length / buf.sampleRate).toFixed(2) + 's');
}

// Update the Csound ftable with modified audio data
async function updateSampleInCsound(sample) {
    if (!csound || !state.csoundReady || !sample) return;

    try {
        // Create WAV file from audio buffer
        var wavData = audioBufferToWav(sample.audioBuffer);

        // Write to Csound virtual filesystem
        await csound.fs.writeFile(sample.fileName, new Uint8Array(wavData));

        // Reload the ftable
        var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + sample.fileName + '" 0 0 0';
        await csound.readScore(ftableScore);

        consoleLog('Updated ftable ' + sample.tableNum);
    } catch (err) {
        consoleLog('Error updating Csound ftable: ' + err.message);
    }
}

// Convert AudioBuffer to WAV format (returns ArrayBuffer)
function audioBufferToWav(audioBuffer) {
    var numChannels = audioBuffer.numberOfChannels;
    var sampleRate = audioBuffer.sampleRate;
    var format = 1; // PCM
    var bitDepth = 16;

    var bytesPerSample = bitDepth / 8;
    var blockAlign = numChannels * bytesPerSample;

    var dataLength = audioBuffer.length * blockAlign;
    var buffer = new ArrayBuffer(44 + dataLength);
    var view = new DataView(buffer);

    // RIFF header
    writeString(view, 0, 'RIFF');
    view.setUint32(4, 36 + dataLength, true);
    writeString(view, 8, 'WAVE');

    // fmt chunk
    writeString(view, 12, 'fmt ');
    view.setUint32(16, 16, true); // chunk size
    view.setUint16(20, format, true);
    view.setUint16(22, numChannels, true);
    view.setUint32(24, sampleRate, true);
    view.setUint32(28, sampleRate * blockAlign, true); // byte rate
    view.setUint16(32, blockAlign, true);
    view.setUint16(34, bitDepth, true);

    // data chunk
    writeString(view, 36, 'data');
    view.setUint32(40, dataLength, true);

    // Interleave and write audio data
    var offset = 44;
    var channels = [];
    for (var ch = 0; ch < numChannels; ch++) {
        channels.push(audioBuffer.getChannelData(ch));
    }

    for (var i = 0; i < audioBuffer.length; i++) {
        for (var ch = 0; ch < numChannels; ch++) {
            var sample = Math.max(-1, Math.min(1, channels[ch][i]));
            var intSample = sample < 0 ? sample * 0x8000 : sample * 0x7FFF;
            view.setInt16(offset, intSample, true);
            offset += 2;
        }
    }

    return buffer;
}

function writeString(view, offset, string) {
    for (var i = 0; i < string.length; i++) {
        view.setUint8(offset + i, string.charCodeAt(i));
    }
}

// Delete current sample from editor and sample list (when no selection)
function deleteCurrentSample() {
    if (!sampleEditor.currentSample) {
        consoleLog('No sample loaded in editor');
        return;
    }

    var tableNum = sampleEditor.currentSample.tableNum;
    var sampleName = sampleEditor.currentSample.name;

    // Remove from state.samples
    state.samples = state.samples.filter(function(s) { return s.tableNum !== tableNum; });

    // Clear editor state
    sampleEditor.currentSample = null;
    sampleEditor.audioBuffer = null;
    sampleEditor.waveformData = null;
    sampleEditor.slices = [];
    sampleEditor.selectedSlice = -1;
    sampleEditor.undoStack = [];
    sampleEditor.zoom = 1;
    sampleEditor.scrollOffset = 0;
    sampleEditor.selection = null;

    // Update UI
    renderSampleList();
    updateSampleEditorInfo();
    renderWaveform();
    renderSliceList();
    updateSliceInitCode();

    consoleLog('Deleted sample: ' + sampleName);
}

function addSliceAtSelection() {
    if (!sampleEditor.audioBuffer) {
        consoleLog('No sample loaded');
        return;
    }

    // Push undo state before modification
    pushSampleEditorUndo();

    var pos;
    if (sampleEditor.selection) {
        pos = Math.min(sampleEditor.selection.start, sampleEditor.selection.end);
    } else {
        // Add at center of view
        var totalSamples = sampleEditor.waveformData.totalSamples;
        var visibleSamples = totalSamples / sampleEditor.zoom;
        pos = Math.floor(sampleEditor.scrollOffset + visibleSamples / 2);
    }

    // Don't add duplicate
    for (var i = 0; i < sampleEditor.slices.length; i++) {
        if (Math.abs(sampleEditor.slices[i] - pos) < 100) {
            consoleLog('Slice already exists near this position');
            return;
        }
    }

    sampleEditor.slices.push(pos);
    sampleEditor.slices.sort(function(a, b) { return a - b; });
    sampleEditor.selectedSlice = sampleEditor.slices.indexOf(pos);

    renderWaveform();
    renderSliceList();
    updateSliceInitCode();
    saveSampleSlices();
}

function removeSelectedSlice() {
    if (sampleEditor.selectedSlice < 0 || sampleEditor.selectedSlice >= sampleEditor.slices.length) {
        consoleLog('No slice selected');
        return;
    }

    // Push undo state before modification
    pushSampleEditorUndo();

    sampleEditor.slices.splice(sampleEditor.selectedSlice, 1);
    sampleEditor.selectedSlice = -1;

    renderWaveform();
    renderSliceList();
    updateSliceInitCode();
    saveSampleSlices();
}

function autoSlice() {
    if (!sampleEditor.audioBuffer) {
        consoleLog('No sample loaded');
        return;
    }

    // Push undo state before modification
    pushSampleEditorUndo();

    var sensitivity = parseInt(document.getElementById('slice-sensitivity').value) || 50;
    var threshold = 0.01 + (100 - sensitivity) * 0.005; // Lower sensitivity = higher threshold

    var buf = sampleEditor.audioBuffer;
    var channelData = buf.getChannelData(0);
    var length = channelData.length;

    // Detect transients using simple energy difference
    var blockSize = Math.floor(buf.sampleRate * 0.01); // 10ms blocks
    var numBlocks = Math.floor(length / blockSize);
    var energies = [];

    for (var i = 0; i < numBlocks; i++) {
        var start = i * blockSize;
        var end = Math.min(start + blockSize, length);
        var energy = 0;

        for (var j = start; j < end; j++) {
            energy += channelData[j] * channelData[j];
        }
        energies.push(energy / blockSize);
    }

    // Find transients (sudden energy increases)
    var newSlices = [];
    var minGap = Math.floor(buf.sampleRate * 0.05); // Minimum 50ms between slices

    for (var i = 1; i < numBlocks; i++) {
        var diff = energies[i] - energies[i - 1];
        if (diff > threshold && energies[i] > threshold * 0.5) {
            var pos = i * blockSize;
            if (newSlices.length === 0 || pos - newSlices[newSlices.length - 1] > minGap) {
                newSlices.push(pos);
            }
        }
    }

    sampleEditor.slices = newSlices;
    sampleEditor.selectedSlice = -1;

    renderWaveform();
    renderSliceList();
    updateSliceInitCode();
    saveSampleSlices();

    consoleLog('Auto-detected ' + newSlices.length + ' slices');
}

function renderSliceList() {
    var list = document.getElementById('slice-list');
    if (!list) return;

    list.innerHTML = '';

    if (sampleEditor.slices.length === 0) {
        list.innerHTML = '<span style="color:#666;font-size:0.75em;">No slices</span>';
        return;
    }

    sampleEditor.slices.forEach(function(pos, index) {
        var item = document.createElement('div');
        item.className = 'slice-item' + (index === sampleEditor.selectedSlice ? ' selected' : '');
        item.textContent = (index + 1) + ': ' + pos;
        item.setAttribute('data-slice-index', index);

        item.addEventListener('click', function() {
            sampleEditor.selectedSlice = index;
            renderSliceList();
            renderWaveform();

            // Scroll to slice
            if (sampleEditor.waveformData) {
                var totalSamples = sampleEditor.waveformData.totalSamples;
                var visibleSamples = totalSamples / sampleEditor.zoom;
                sampleEditor.scrollOffset = Math.max(0, pos - visibleSamples / 2);
                renderWaveform();
            }
        });

        list.appendChild(item);
    });
}

function updateSliceInitCode() {
    var codeEl = document.getElementById('slice-init-code');
    if (!codeEl) return;

    if (sampleEditor.slices.length === 0) {
        codeEl.textContent = '; No slices defined';
        return;
    }

    var code = '';
    sampleEditor.slices.forEach(function(pos, index) {
        code += 'islice' + (index + 1) + ' = ' + pos;
        if (index < sampleEditor.slices.length - 1) code += '  ';
    });

    codeEl.textContent = code;
}

function saveSampleSlices() {
    if (!sampleEditor.currentSample) return;

    // Save slices back to the sample object
    sampleEditor.currentSample.slices = sampleEditor.slices.slice();

    // Update the ftable in Csound if needed (for runtime editing)
    // The actual audio data editing would be done here before reloading
}

async function updateSampleFtable() {
    if (!sampleEditor.currentSample || !sampleEditor.audioBuffer || !state.csoundReady) return;

    var sample = sampleEditor.currentSample;

    // To update the ftable, we need to write a new WAV file and reload
    // For now, just reload from the existing file
    try {
        if (sample.fileName) {
            var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + sample.fileName + '" 0 0 0';
            await csound.readScore(ftableScore);
            consoleLog('Reloaded ftable ' + sample.tableNum);
        }
    } catch (err) {
        consoleLog('Error updating ftable: ' + err.message);
    }
}

// Compile a single instrument by index (0-based)
async function compileSingleInstrument(index) {
    if (!state.csoundReady) return false;

    var instrCode = state.instruments[index];
    if (!instrCode || !instrCode.trim()) return true;

    try {
        await csound.compileOrc(instrCode);
        lastCompiled.instruments[index] = instrCode;
        consoleLog('Compiled instr ' + (index + 1));
        return true;
    } catch (err) {
        consoleLog('Instr ' + (index + 1) + ' error: ' + err.message);
        return false;
    }
}

// Compile only UDOs if changed
async function compileOpcodesIfChanged() {
    if (!state.csoundReady) return true;

    var currentOpcodes = state.opcodes || '';
    if (currentOpcodes.trim() === (lastCompiled.opcodes || '').trim()) {
        return true; // No change
    }

    if (!currentOpcodes.trim()) {
        lastCompiled.opcodes = '';
        return true;
    }

    try {
        await csound.compileOrc(currentOpcodes);
        lastCompiled.opcodes = currentOpcodes;
        consoleLog('Compiled UDOs');
        return true;
    } catch (err) {
        consoleLog('UDO compile error: ' + err.message);
        return false;
    }
}

// Update a single ftable
async function updateSingleFtable(tableNum, fileName) {
    if (!state.csoundReady) return false;

    try {
        var ftableScore = 'f ' + tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
        await csound.readScore(ftableScore);
        lastCompiled.ftables[tableNum] = { fileName: fileName };
        consoleLog('Updated ftable ' + tableNum);
        return true;
    } catch (err) {
        consoleLog('Ftable ' + tableNum + ' error: ' + err.message);
        return false;
    }
}

// Incremental compile - only recompile what has changed
async function compileInstruments(forceAll) {
    if (!state.csoundReady) {
        consoleLog('Error: Csound not ready');
        return;
    }

    saveCurrentInstrument();
    saveOpcodes();

    var compiledCount = 0;
    var skippedCount = 0;
    var errorCount = 0;

    // Compile UDOs first if changed
    if (forceAll || state.opcodes !== lastCompiled.opcodes) {
        if (state.opcodes && state.opcodes.trim()) {
            try {
                await csound.compileOrc(state.opcodes);
                lastCompiled.opcodes = state.opcodes;
                consoleLog('Compiled UDOs');
            } catch (err) {
                consoleLog('UDO compile error: ' + err.message);
                return;
            }
        } else {
            lastCompiled.opcodes = '';
        }
    }

    // Compile only changed instruments
    for (var i = 0; i < state.instruments.length; i++) {
        var instrCode = state.instruments[i];
        if (!instrCode || !instrCode.trim()) {
            lastCompiled.instruments[i] = '';
            continue;
        }

        // Check if this instrument has changed
        if (!forceAll && lastCompiled.instruments[i] === instrCode) {
            skippedCount++;
            continue;
        }

        try {
            await csound.compileOrc(instrCode);
            lastCompiled.instruments[i] = instrCode;
            compiledCount++;
        } catch (err) {
            consoleLog('Instr ' + (i + 1) + ' error: ' + err.message);
            errorCount++;
        }
    }

    // Compile panic instrument (only once, or if forced)
    if (forceAll || !lastCompiled.panicCompiled) {
        var panicInstr = 'instr 999\n';
        for (var i = 1; i <= 32; i++) {
            panicInstr += '  turnoff2 ' + i + ', 0, 0\n';
        }
        panicInstr += '  turnoff\nendin\n';

        // Note killer instrument - turns off specific fractional instrument instances
        // p4 = fractional instrument number to turn off (e.g., 1.001)
        // Uses mode 4 (exact fractional match) + 8 (only indefinite notes) = 12
        var noteKillerInstr = 'instr 998\n';
        noteKillerInstr += '  itarget = p4\n';
        noteKillerInstr += '  turnoff2 itarget, 12, 1\n';  // mode 12, allow release
        noteKillerInstr += '  turnoff\n';
        noteKillerInstr += 'endin\n';

        try {
            await csound.compileOrc(panicInstr);
            await csound.compileOrc(noteKillerInstr);
            lastCompiled.panicCompiled = true;
        } catch (err) {
            consoleLog('Panic/NoteKiller instr error: ' + err.message);
        }
    }

    // Only reload ftables that have changed
    for (var i = 0; i < state.samples.length; i++) {
        var sample = state.samples[i];
        if (sample.fileName) {
            var lastFtable = lastCompiled.ftables[sample.tableNum];
            if (forceAll || !lastFtable || lastFtable.fileName !== sample.fileName) {
                try {
                    var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + sample.fileName + '" 0 0 0';
                    await csound.readScore(ftableScore);
                    lastCompiled.ftables[sample.tableNum] = { fileName: sample.fileName };
                } catch (err) {
                    consoleLog('Ftable ' + sample.tableNum + ' error: ' + err.message);
                }
            }
        }
    }

    // Report results
    if (compiledCount === 0 && skippedCount > 0 && errorCount === 0) {
        consoleLog('No changes detected (' + skippedCount + ' instruments unchanged)');
        setStatus('No changes');
    } else if (errorCount > 0) {
        consoleLog('Compiled ' + compiledCount + ' instruments (' + errorCount + ' errors, ' + skippedCount + ' unchanged)');
        setStatus('Compiled with errors');
    } else if (compiledCount > 0) {
        consoleLog('Compiled ' + compiledCount + ' instruments (' + skippedCount + ' unchanged)');
        setStatus('Compiled');
    } else {
        consoleLog('Nothing to compile');
        setStatus('Ready');
    }
}

// Force recompile everything (useful after loading a new song)
async function compileAllInstruments() {
    // Clear the tracking state to force full recompile
    lastCompiled.instruments = [];
    lastCompiled.opcodes = '';
    lastCompiled.ftables = {};
    lastCompiled.panicCompiled = false;

    await compileInstruments(true);
}

// ============================================
// UTILITIES
// ============================================

function setStatus(msg) {
    document.getElementById('status-bar').textContent = msg;
}

function updateOctaveDisplay() {
    document.getElementById('octave-display').textContent = state.baseOctave;
}

async function initCsound() {
    consoleLog('Loading Csound 7 WASM...');
    setStatus('Loading Csound...');

    try {
        // Dynamic import of Csound 7
        const { Csound } = await import('./meow/csound.js');

        // Create Csound instance
        csound = await Csound({ useWorker: false });
        consoleLog('Csound instance created');

        // Set up message handlers to capture all Csound output
        csound.on('message', function(msg) {
            consoleLog(msg);
        });

        // Also capture any other output channels and state changes
        if (csound.on) {
            try {
                csound.on('error', function(msg) {
                    consoleLog('ERROR: ' + msg);
                });
                csound.on('play', function() {
                    consoleLog('Csound: play state');
                });
                csound.on('stop', function() {
                    consoleLog('Csound: stop state');
                });
                csound.on('realtimePerformanceStarted', function() {
                    consoleLog('Csound: realtime performance started');
                });
                // Get AudioContext when audio node is created - store for precise timing
                csound.on('onAudioNodeCreated', function(audioNode) {
                    consoleLog('AudioNode created');
                    if (audioNode && audioNode.context) {
                        audioCtx = audioNode.context;  // Store globally for scheduler
                        consoleLog('AudioContext state: ' + audioCtx.state);
                        // Resume if suspended
                        if (audioCtx.state === 'suspended') {
                            var resumeOnInteraction = function() {
                                audioCtx.resume().then(function() {
                                    consoleLog('AudioContext resumed to: ' + audioCtx.state);
                                });
                                document.removeEventListener('click', resumeOnInteraction);
                                document.removeEventListener('keydown', resumeOnInteraction);
                            };
                            document.addEventListener('click', resumeOnInteraction);
                            document.addEventListener('keydown', resumeOnInteraction);
                        }
                    }
                });
            } catch (e) {
                consoleLog('Event setup error: ' + e);
            }
        }

        // Compile initial blank instruments (1-32)
        var orchestra =
            'sr = 44100\n' +
            'ksmps = 32\n' +
            'nchnls = 2\n' +
            '0dbfs = 1\n\n' +
            'gisine ftgen 1, 0, 16384, 10, 1\n\n';

        for (var i = 1; i <= 32; i++) {
            orchestra += 'instr ' + i + '\nendin\n\n';
        }

        // Note killer instrument - turns off specific fractional instrument instances
        // p4 = fractional instrument number to turn off (e.g., 1.001)
        // Mode 12 = 4 (exact fractional match) + 8 (only indefinite notes)
        orchestra += 'instr 998\n';
        orchestra += '  itarget = p4\n';
        orchestra += '  turnoff2 itarget, 12, 1\n';  // allow release envelope
        orchestra += '  turnoff\n';
        orchestra += 'endin\n\n';

        // Panic instrument - uses turnoff2 to kill ALL instances of ALL instruments
        // Mode 0 = turn off all instances, Release 0 = immediate stop
        orchestra += 'instr 999\n';
        for (var i = 1; i <= 32; i++) {
            orchestra += '  turnoff2 ' + i + ', 0, 0\n';
        }
        orchestra += '  turnoff\n';
        orchestra += 'endin\n\n';

        // Enable realtime audio output
        await csound.setOption('-odac -d --nodisplays');
        // Enable full message output (don't suppress displays)
        await csound.setOption('-m7');  // Full message level (amps + range + warnings)
        
        await csound.compileOrc(orchestra);
        consoleLog('Blank instruments initialized (1-32)');

        // Start Csound
        await csound.start();
        consoleLog('Csound started');

        // Keep Csound running with an infinite score (24 hours)
        await csound.readScore('f 0 86400');
        consoleLog('Infinite score scheduled');

        state.csoundReady = true;

        // Compile user instruments (full compile on startup)
        await compileAllInstruments();

        document.getElementById('btn-play').disabled = false;
        document.getElementById('btn-stop').disabled = true;
        document.getElementById('btn-compile').disabled = false;

        setStatus('Ready - Use keyboard for notes, ` to record');
        consoleLog('Ready');

        // Cleanup on page unload
        window.addEventListener('beforeunload', async function() {
            if (csound) {
                try {
                    await csound.stop();
                    await csound.destroy();
                } catch (e) {}
            }
        });

    } catch (err) {
        consoleLog('Csound init error: ' + err.message);
        setStatus('Error loading Csound');
        console.error(err);
    }
}

function cacheDOMReferences() {
    domCache.grid = document.getElementById('tracker-grid');
    domCache.console = document.getElementById('console');
}

// ============================================
// INITIALIZATION
// ============================================

function init() {
    cacheDOMReferences();

    consoleLog('Initializing Csound Mod Tracker...');

    initTracks();
    initPatterns();
    renderTrackerGrid();
    renderTrackList();
    renderTimeline();
    renderTimelineRuler();

    initMainTabs();
    initInstrumentTabs();
    initSampleLoader();
    initSampleEditor();
    initPianoRoll();
    initMIDI();
    initContextMenu();
    initChords();
    renderSampleList();

    // Button events
    document.getElementById('btn-play').addEventListener('click', startPlayback);
    document.getElementById('btn-stop').addEventListener('click', stopPlayback);
    document.getElementById('btn-record').addEventListener('click', toggleRecording);

    // Loop toggle button
    var btnLoop = document.getElementById('btn-loop');
    if (btnLoop) {
        btnLoop.addEventListener('click', function() {
            toggleLoopRegion();
            updateLoopButton();
        });
    }

    // Snap toggle button
    var btnSnap = document.getElementById('btn-snap');
    if (btnSnap) {
        btnSnap.addEventListener('click', function() {
            toggleSnapToMeasure();
            updateSnapButton();
        });
        // Initialize snap button state
        updateSnapButton();
    }

    // Grid snap dropdown
    var gridSnapSelect = document.getElementById('grid-snap');
    if (gridSnapSelect) {
        gridSnapSelect.addEventListener('change', function() {
            state.timeline.gridSnap = parseFloat(this.value);
            consoleLog('Grid snap: ' + this.options[this.selectedIndex].text);
            // Re-render timeline to show new grid resolution
            renderTimeline();
        });
    }

    // Legacy sequence buttons removed - DAW uses clips on timeline
    // Pattern cloning still available via context menu or keyboard shortcut

    // Pattern editor controls
    var btnApplySteps = document.getElementById('btn-apply-pattern-steps');
    if (btnApplySteps) btnApplySteps.addEventListener('click', applyPatternSteps);

    // Note column +/- buttons
    var btnNoteColPlus = document.getElementById('btn-note-col-plus');
    var btnNoteColMinus = document.getElementById('btn-note-col-minus');
    if (btnNoteColPlus) btnNoteColPlus.addEventListener('click', function() {
        var patternIndex = getCurrentPatternIndex();
        if (patternIndex >= 0) {
            addNoteColumn(patternIndex);
            renderTrackerGrid(true);
            updateNoteColDisplay();
            consoleLog('Added note column');
        }
    });
    if (btnNoteColMinus) btnNoteColMinus.addEventListener('click', function() {
        var patternIndex = getCurrentPatternIndex();
        if (patternIndex >= 0) {
            removeNoteColumn(patternIndex);
            renderTrackerGrid(true);
            updateNoteColDisplay();
            consoleLog('Removed note column');
        }
    });

    // Track list sidebar (DAW layout)
    var trackList = document.getElementById('track-list');
    if (trackList) {
        trackList.addEventListener('click', handleTrackListClick);
        renderTrackList();
    }

    var btnScrollUp = document.getElementById('btn-scroll-tracks-up');
    var btnScrollDown = document.getElementById('btn-scroll-tracks-down');
    if (btnScrollUp) btnScrollUp.addEventListener('click', scrollTracksUp);
    if (btnScrollDown) btnScrollDown.addEventListener('click', scrollTracksDown);

    var btnAddTrack = document.getElementById('btn-add-track');
    if (btnAddTrack) {
        btnAddTrack.addEventListener('click', function() {
            // Add a new track
            var newTrackIdx = addTrack();
            state.selectedTrack = newTrackIdx;
            // Scroll to show this track
            if (newTrackIdx >= state.visibleTrackStart + state.visibleTrackCount) {
                state.visibleTrackStart = Math.max(0, newTrackIdx - state.visibleTrackCount + 1);
            }
            renderTrackList();
            renderTimeline();
            consoleLog('Added Track ' + (newTrackIdx + 1));
        });
    }

    var btnRemoveTrack = document.getElementById('btn-remove-track');
    if (btnRemoveTrack) {
        btnRemoveTrack.addEventListener('click', function() {
            if (removeTrack()) {
                renderTrackList();
                renderTimeline();
                consoleLog('Removed last track');
            } else {
                consoleLog('Cannot remove the only track');
            }
        });
    }

    // Timeline (DAW layout)
    var timelineTracks = document.getElementById('timeline-tracks');
    if (timelineTracks) {
        timelineTracks.addEventListener('click', handleTimelineClick);
        timelineTracks.addEventListener('dblclick', handleTimelineDblClick);
        timelineTracks.addEventListener('contextmenu', handleTimelineContextMenu);
        timelineTracks.addEventListener('mousedown', handleTimelineMouseDown);

        // Synchronize track list scroll with timeline scroll
        var trackList = document.getElementById('track-list');
        var timelineHeader = document.querySelector('.timeline-header');

        timelineTracks.addEventListener('scroll', function() {
            // Sync vertical scroll with track list
            if (trackList) {
                trackList.scrollTop = this.scrollTop;
            }
            // Sync ruler horizontal scroll
            if (timelineHeader) {
                timelineHeader.scrollLeft = this.scrollLeft;
            }

            // Update ruler bar markers for visible range
            updateRulerOnScroll();

            // Update timeline scrollbar position
            updateTimelineScrollbar();

            // Auto-extend timeline when scrolling near the right edge
            var scrollRight = this.scrollLeft + this.clientWidth;
            var totalWidth = state.timeline.totalBeats * timelinePixelsPerBeat;
            if (scrollRight >= totalWidth - 200) {
                state.timeline.totalBeats += 400;  // Add 100 more bars
                renderTimeline();
                renderTimelineRuler();
                updateTimelineScrollbar();
            }
        });

        if (trackList) {
            trackList.addEventListener('scroll', function() {
                timelineTracks.scrollTop = this.scrollTop;
            });
        }

        // Wheel zoom (Ctrl+wheel) and timeline extension
        timelineTracks.addEventListener('wheel', function(e) {
            // Ctrl+wheel for zoom
            if (e.ctrlKey) {
                e.preventDefault();
                zoomTimeline(e.deltaY > 0 ? 0.9 : 1.1, e.clientX);
                return;
            }
        }, { passive: false });

        // Middle mouse button drag for zooming
        var middleMouseZoom = { active: false, startX: 0, startZoom: 0 };
        timelineTracks.addEventListener('mousedown', function(e) {
            if (e.button === 1) { // Middle mouse button
                e.preventDefault();
                middleMouseZoom.active = true;
                middleMouseZoom.startX = e.clientX;
                middleMouseZoom.startZoom = timelinePixelsPerBeat;
            }
        });
        document.addEventListener('mousemove', function(e) {
            if (middleMouseZoom.active) {
                var delta = e.clientX - middleMouseZoom.startX;
                var zoomFactor = 1 + (delta / 200);
                // Allow zooming from 5 (zoomed out) to 500 (zoomed in to see 128th/256th notes)
                timelinePixelsPerBeat = Math.max(5, Math.min(500, middleMouseZoom.startZoom * zoomFactor));
                renderTimeline();
                renderTimelineRuler();
            }
        });
        document.addEventListener('mouseup', function(e) {
            if (e.button === 1) {
                middleMouseZoom.active = false;
            }
        });

        renderTimeline();
    }

    // Global mouse handlers for clip dragging
    document.addEventListener('mousemove', handleTimelineMouseMove);
    document.addEventListener('mouseup', handleTimelineMouseUp);

    // Timeline context menu
    var timelineContextMenu = document.getElementById('timeline-context-menu');
    if (timelineContextMenu) {
        timelineContextMenu.addEventListener('click', function(e) {
            var action = e.target.getAttribute('data-action');
            if (action) {
                handleTimelineContextAction(action);
            }
        });
    }

    // Hide context menus on click elsewhere
    document.addEventListener('click', function(e) {
        if (!e.target.closest('#timeline-context-menu')) {
            hideTimelineContextMenu();
        }
    });

    document.getElementById('btn-compile').addEventListener('click', compileInstruments);
    document.getElementById('btn-save').addEventListener('click', saveSong);
    document.getElementById('btn-load').addEventListener('click', function() {
        document.getElementById('file-input').click();
    });
    document.getElementById('btn-export-csd').addEventListener('click', exportCSD);

    // Demo buttons - load 1.cst, 2.cst, 3.cst, 4.cst
    var demoBtns = document.querySelectorAll('.demo-btn');
    demoBtns.forEach(function(btn) {
        btn.addEventListener('click', function() {
            var demoNum = this.getAttribute('data-demo');
            loadDemo(demoNum);
        });
    });

    document.getElementById('btn-toggle-console').addEventListener('click', function() {
        var consoleEl = document.getElementById('console');
        var isHidden = consoleEl.style.display === 'none';
        consoleEl.style.display = isHidden ? 'block' : 'none';
        this.textContent = isHidden ? 'Hide' : 'Show';
    });

    document.getElementById('file-input').addEventListener('change', function(e) {
        if (e.target.files.length > 0) {
            loadSong(e.target.files[0]);
        }
    });

    document.getElementById('bpm').addEventListener('change', function(e) {
        state.bpm = parseInt(e.target.value) || 120;
        if (state.isPlaying) {
            stopPlayback();
            startPlayback();
        }
    });

    // LPB is now per-pattern only (in pattern-lpb input), not global

    document.getElementById('edit-step').addEventListener('change', function(e) {
        var v = parseInt(e.target.value);
        state.editStep = isNaN(v) ? 1 : v;
    });

    document.getElementById('code-editor').addEventListener('blur', saveCurrentInstrument);
    document.getElementById('opcodes-editor').addEventListener('blur', saveOpcodes);

    consoleLog('Keys: z-]/q-]=notes, Arrows=nav, Tab=OFF, `=rec, Ctrl+C/X/V=copy/cut/paste');

    // Initialize Csound 7
    initCsound();
}

if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
} else {
    init();
}
