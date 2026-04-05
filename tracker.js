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
var playbackStartBeat = 0;    // Beat position at playback start

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
    songInfo: '',
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
        cursorBeat: 0,
        cursorTrack: 0,
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

// ============================================
// UNDO SYSTEM
// ============================================
var undoStack = [];
var redoStack = [];
var MAX_UNDO = 50;

function pushUndo(actionType, data) {
    undoStack.push({
        type: actionType,
        data: JSON.parse(JSON.stringify(data)),
        timestamp: Date.now()
    });
    // Limit undo stack size
    while (undoStack.length > MAX_UNDO) {
        undoStack.shift();
    }
    // Clear redo stack when new action is performed
    redoStack = [];
}

function undo() {
    if (undoStack.length === 0) {
        consoleLog('Nothing to undo');
        return;
    }
    var action = undoStack.pop();

    // Save current state to redo stack
    var redoData = captureStateForUndo(action.type);
    redoStack.push({
        type: action.type,
        data: redoData,
        timestamp: Date.now()
    });

    // Restore the previous state
    restoreStateFromUndo(action);
    consoleLog('Undo: ' + action.type);
}

function redo() {
    if (redoStack.length === 0) {
        consoleLog('Nothing to redo');
        return;
    }
    var action = redoStack.pop();

    // Save current state to undo stack
    var undoData = captureStateForUndo(action.type);
    undoStack.push({
        type: action.type,
        data: undoData,
        timestamp: Date.now()
    });

    // Restore the redo state
    restoreStateFromUndo(action);
    consoleLog('Redo: ' + action.type);
}

function captureStateForUndo(actionType) {
    switch (actionType) {
        case 'pattern-edit':
        case 'piano-edit':
            return {
                patterns: JSON.parse(JSON.stringify(state.patterns)),
                selectedClip: JSON.parse(JSON.stringify(state.selectedClip))
            };
        case 'clip-edit':
            return {
                tracks: JSON.parse(JSON.stringify(state.tracks)),
                patterns: JSON.parse(JSON.stringify(state.patterns)),
                selectedClip: JSON.parse(JSON.stringify(state.selectedClip))
            };
        default:
            return {
                patterns: JSON.parse(JSON.stringify(state.patterns)),
                tracks: JSON.parse(JSON.stringify(state.tracks))
            };
    }
}

function restoreStateFromUndo(action) {
    switch (action.type) {
        case 'pattern-edit':
        case 'piano-edit':
            state.patterns = action.data.patterns;
            if (action.data.selectedClip) {
                state.selectedClip = action.data.selectedClip;
            }
            invalidatePatternCache();
            var pattern = getCurrentPattern();
            if (pattern && pattern.type === 'piano') {
                scheduleRenderPianoRoll();
            } else {
                renderTrackerGrid(true);
            }
            renderTimeline();
            break;
        case 'clip-edit':
            state.tracks = action.data.tracks;
            if (action.data.patterns) {
                state.patterns = action.data.patterns;
                invalidatePatternCache();
            }
            if (action.data.selectedClip) {
                state.selectedClip = action.data.selectedClip;
            }
            renderTimeline();
            renderTrackList();
            if (state.selectedClip && state.selectedClip.clipId !== null) {
                var clip = findClipById(state.selectedClip.trackId, state.selectedClip.clipId);
                if (clip) {
                    setPrimaryClip(state.selectedClip.trackId, state.selectedClip.clipId);
                }
            }
            break;
        default:
            if (action.data.patterns) state.patterns = action.data.patterns;
            if (action.data.tracks) state.tracks = action.data.tracks;
            invalidatePatternCache();
            renderTrackerGrid(true);
            renderTimeline();
            renderTrackList();
    }
}

// Piano roll selection state
var pianoSelection = {
    active: false,
    startBeat: 0,
    endBeat: 0,
    startPitch: 0,
    endPitch: 0,
    selectedNotes: []  // Array of indices into pattern.notes
};

var pianoContextState = {
    beat: 0,
    pitch: 0
};

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
var uiFocus = 'tracker'; // 'timeline' | 'tracker' | 'piano'
var selectedClips = [];

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

// ============================================
// UNIFIED NOTE/EVENT STRUCTURE
// ============================================
// All patterns use a single notes array with typed events:
//
// Note event (type: 'note' or missing for legacy):
// {
//     type: 'note',
//     pitch: 60,           // MIDI note number (0-127)
//     startBeat: 0.0,      // Start position in beats
//     duration: 0.25,      // Duration in beats (piano roll). Tracker may leave null.
//     velocity: 1.0,       // 0-1 (null = unset)
//     column: 0,           // Note column for tracker view (polyphony)
//     fx: []               // FX values for this note: ["0100", "0200", ...]
// }
//
// Cell event (tracker-only, step-based params / OFF):
// {
//     type: 'cell',
//     startBeat: 0.0,      // Step position in beats
//     column: 0,
//     note: 'OFF' | '',    // NOTE_OFF to end held notes
//     amp: 'FF' | '',      // Hex velocity (00-FF) or empty
//     fx: []               // FX values for this step: ["0100", ...]
// }
//
// The pattern.type ('tracker' or 'piano') determines the VIEW.
// Tracker view shows step-quantized cells, piano roll shows continuous notes.

function isNoteEvent(ev) {
    return ev && (ev.type === undefined || ev.type === 'note');
}

function isCellEvent(ev) {
    return ev && ev.type === 'cell';
}

function ensurePatternNotes(pattern) {
    if (pattern && !pattern.notes) pattern.notes = [];
    return pattern ? pattern.notes : [];
}

function beatsMatch(a, b) {
    return Math.abs(a - b) < 0.001;
}

function velocityToHex(velocity) {
    if (velocity === null || velocity === undefined) return '--';
    var clamped = Math.max(0, Math.min(1, velocity));
    return Math.round(clamped * 255).toString(16).toUpperCase().padStart(2, '0');
}

function hexToVelocity(ampStr) {
    if (!ampStr || ampStr === '--') return null;
    var val = parseInt(ampStr, 16);
    if (isNaN(val)) return null;
    return Math.max(0, Math.min(255, val)) / 255;
}

function hasFxValues(fxArr) {
    if (!fxArr || fxArr.length === 0) return false;
    for (var i = 0; i < fxArr.length; i++) {
        var v = fxArr[i];
        if (v && v !== '--' && v !== '----') return true;
    }
    return false;
}

function trimFxArray(fxArr) {
    if (!fxArr) return fxArr;
    var last = fxArr.length - 1;
    while (last >= 0) {
        var v = fxArr[last];
        if (v && v !== '--' && v !== '----') break;
        last--;
    }
    fxArr.length = Math.max(0, last + 1);
    return fxArr;
}

function removeEvent(events, eventObj) {
    if (!events || !eventObj) return;
    var idx = events.indexOf(eventObj);
    if (idx >= 0) events.splice(idx, 1);
}

function findTrackerEventsAtStep(pattern, step, noteCol) {
    var lpb = pattern.lpb || state.lpb;
    var stepBeat = step / lpb;
    var events = ensurePatternNotes(pattern);
    var noteEvent = null;
    var cellEvent = null;

    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!ev) continue;
        if ((ev.column || 0) !== noteCol) continue;
        if (!beatsMatch(ev.startBeat, stepBeat)) continue;
        if (isNoteEvent(ev)) noteEvent = ev;
        else if (isCellEvent(ev)) cellEvent = ev;
    }

    return { noteEvent: noteEvent, cellEvent: cellEvent, stepBeat: stepBeat };
}

function findNoteEndingAtStep(pattern, step, noteCol) {
    var lpb = pattern.lpb || state.lpb;
    var stepBeat = step / lpb;
    var events = ensurePatternNotes(pattern);

    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!isNoteEvent(ev)) continue;
        if ((ev.column || 0) !== noteCol) continue;
        if (typeof ev.duration !== 'number' || ev.duration <= 0) continue;
        var endBeat = ev.startBeat + ev.duration;
        if (beatsMatch(endBeat, stepBeat)) return ev;
    }
    return null;
}

function getTrackerCellDisplay(pattern, step, noteCol) {
    var info = findTrackerEventsAtStep(pattern, step, noteCol);
    var noteEvent = info.noteEvent;
    var cellEvent = info.cellEvent;

    var noteName = '---';
    var ampStr = '--';
    var fxArr = [];

    if (noteEvent) {
        if (noteEvent.pitch !== null && noteEvent.pitch !== undefined) {
            noteName = midiToNoteName(noteEvent.pitch);
        }
        ampStr = velocityToHex(noteEvent.velocity);
        fxArr = noteEvent.fx || [];
    } else if (cellEvent && cellEvent.note === NOTE_OFF) {
        noteName = NOTE_OFF;
        ampStr = cellEvent.amp || '--';
        fxArr = cellEvent.fx || [];
    } else if (cellEvent) {
        ampStr = cellEvent.amp || '--';
        fxArr = cellEvent.fx || [];
    } else {
        var endingNote = findNoteEndingAtStep(pattern, step, noteCol);
        if (endingNote) {
            noteName = NOTE_OFF;
        }
    }

    return { noteName: noteName, ampStr: ampStr, fxArr: fxArr };
}

function getTrackerFxValue(pattern, step, noteCol, fxCol) {
    var info = findTrackerEventsAtStep(pattern, step, noteCol);
    var fxArr = null;
    if (info.noteEvent && info.noteEvent.fx) fxArr = info.noteEvent.fx;
    else if (info.cellEvent && info.cellEvent.fx) fxArr = info.cellEvent.fx;
    if (!fxArr || fxArr.length <= fxCol) return '';
    return fxArr[fxCol] || '';
}

function deriveTrackerNoteDurations(events, lpb) {
    if (!events || events.length === 0) return;
    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!isNoteEvent(ev)) continue;

        var endBeat = null;
        for (var j = 0; j < events.length; j++) {
            if (i === j) continue;
            var other = events[j];
            if ((other.column || 0) !== (ev.column || 0)) continue;
            if (other.startBeat <= ev.startBeat) continue;
            if (isNoteEvent(other) || (isCellEvent(other) && other.note === NOTE_OFF)) {
                if (endBeat === null || other.startBeat < endBeat) {
                    endBeat = other.startBeat;
                }
            }
        }

        if (endBeat === null) {
            ev.duration = null;  // Indefinite unless explicitly ended in selection
        } else {
            var dur = endBeat - ev.startBeat;
            ev.duration = dur > 0 ? dur : null;
        }
    }
}

// Create a new empty tracker pattern (step sequencer style)
function createTrackerPattern(steps, lpb, trackId) {
    var patternNum = state.patterns ? state.patterns.length : 0;
    var stepsVal = steps || 16;
    var lpbVal = lpb || state.lpb;
    var pattern = {
        id: patternNum,
        name: 'Pattern ' + (patternNum + 1),
        type: 'tracker',
        trackId: trackId || 0,
        instrument: 1,
        steps: stepsVal,
        lpb: lpbVal,
        beats: stepsVal / lpbVal,  // Derived from steps and lpb
        noteColumns: 1,
        fxColumns: [1],            // Number of FX columns per note column (p6 active by default)
        notes: []                  // Unified notes array
    };
    return pattern;
}

// Add a note column to pattern
function addNoteColumn(patternIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    pattern.noteColumns = (pattern.noteColumns || 1) + 1;
    if (!pattern.fxColumns) pattern.fxColumns = [0];
    pattern.fxColumns.push(0);  // New column starts with 0 FX columns

    markPatternDirty(patternIndex);
}

// Remove a note column from pattern
function removeNoteColumn(patternIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern || (pattern.noteColumns || 1) <= 1) return;

    var removedCol = pattern.noteColumns - 1;
    pattern.noteColumns = removedCol;

    // Remove notes in the deleted column
    if (pattern.notes) {
        pattern.notes = pattern.notes.filter(function(n) {
            return (n.column || 0) < removedCol;
        });
    }

    if (pattern.fxColumns && pattern.fxColumns.length > removedCol) {
        pattern.fxColumns.pop();
    }

    markPatternDirty(patternIndex);
}

// Add FX column to a specific note column in pattern
function addFxColumn(patternIndex, noteColIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    if (!pattern.fxColumns) pattern.fxColumns = [];
    while (pattern.fxColumns.length <= noteColIndex) {
        pattern.fxColumns.push(0);
    }
    pattern.fxColumns[noteColIndex]++;

    markPatternDirty(patternIndex);
}

// Remove FX column from a specific note column in pattern
function removeFxColumn(patternIndex, noteColIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern || !pattern.fxColumns || !pattern.fxColumns[noteColIndex]) return;

    pattern.fxColumns[noteColIndex]--;

    // Truncate FX arrays on notes in this column
    var fxCount = pattern.fxColumns[noteColIndex];
    if (pattern.notes) {
        pattern.notes.forEach(function(note) {
            if ((note.column || 0) === noteColIndex && note.fx && note.fx.length > fxCount) {
                note.fx.length = fxCount;
            }
        });
    }

    markPatternDirty(patternIndex);
}

// Get FX count for a note column
function getFxCount(pattern, noteColIndex) {
    if (!pattern || !pattern.fxColumns) return 0;
    return pattern.fxColumns[noteColIndex] || 0;
}

// ============================================
// STEP-BASED HELPERS (for tracker view)
// ============================================

// Get note at a specific step and column (for tracker view rendering)
function getNoteAtStep(pattern, step, column) {
    if (!pattern || !pattern.notes) return null;

    var lpb = pattern.lpb || state.lpb;
    var stepBeat = step / lpb;
    var stepDuration = 1 / lpb;

    for (var i = 0; i < pattern.notes.length; i++) {
        var note = pattern.notes[i];
        if (!isNoteEvent(note)) continue;
        if ((note.column || 0) !== column) continue;

        // Check if note starts at this step
        if (Math.abs(note.startBeat - stepBeat) < 0.001) {
            return { note: note, index: i, isStart: true };
        }

        // Only consider duration if explicitly set and positive
        if (typeof note.duration === 'number' && note.duration > 0) {
            // Check if note is still sounding at this step (for showing continuation or note-off)
            var noteEnd = note.startBeat + note.duration;
            if (note.startBeat < stepBeat && noteEnd > stepBeat) {
                return { note: note, index: i, isStart: false, isContinuation: true };
            }

            // Check if note ends at this step (show note-off)
            if (Math.abs(noteEnd - stepBeat) < 0.001) {
                return { note: note, index: i, isStart: false, isEnd: true };
            }
        }
    }

    return null;
}

// Set/update a note at a specific step and column
function setNoteAtStep(pattern, step, column, noteName, velocity, fx) {
    if (!pattern) return;
    if (!pattern.notes) pattern.notes = [];

    var lpb = pattern.lpb || state.lpb;
    var stepBeat = step / lpb;
    var stepDuration = 1 / lpb;

    // Find existing note at this step/column
    var existingIdx = -1;
    for (var i = 0; i < pattern.notes.length; i++) {
        var note = pattern.notes[i];
        if ((note.column || 0) === column && Math.abs(note.startBeat - stepBeat) < 0.001) {
            existingIdx = i;
            break;
        }
    }

    // Handle note-off or empty
    if (!noteName || noteName === '' || noteName === '---' || noteName === NOTE_OFF) {
        if (existingIdx >= 0) {
            pattern.notes.splice(existingIdx, 1);
        }
        return;
    }

    // Convert note name to MIDI pitch
    var pitch = noteNameToMidi(noteName);
    if (pitch === null) return;

    // Convert velocity (hex string like "FF" or decimal 0-1)
    var vel = 1.0;
    if (typeof velocity === 'string' && velocity.length > 0) {
        vel = parseInt(velocity, 16) / 255;
    } else if (typeof velocity === 'number') {
        vel = velocity;
    }

    if (existingIdx >= 0) {
        // Update existing note
        pattern.notes[existingIdx].pitch = pitch;
        pattern.notes[existingIdx].velocity = vel;
        if (fx !== undefined) pattern.notes[existingIdx].fx = fx;
    } else {
        // Create new note
        var newNote = {
            pitch: pitch,
            startBeat: stepBeat,
            duration: stepDuration,
            velocity: vel,
            column: column,
            fx: fx || []
        };
        pattern.notes.push(newNote);
    }

    markPatternNoteVizDirtyForPattern(pattern);
}

// Clear note at a specific step and column
function clearNoteAtStep(pattern, step, column) {
    if (!pattern || !pattern.notes) return;

    var lpb = pattern.lpb || state.lpb;
    var stepBeat = step / lpb;

    for (var i = pattern.notes.length - 1; i >= 0; i--) {
        var note = pattern.notes[i];
        if ((note.column || 0) === column && Math.abs(note.startBeat - stepBeat) < 0.001) {
            pattern.notes.splice(i, 1);
            markPatternNoteVizDirtyForPattern(pattern);
            return;
        }
    }
}



// Convert MIDI pitch to note name (e.g., 60 -> "C-4")
function midiToNoteName(pitch) {
    var noteNames = ['C-', 'C#', 'D-', 'D#', 'E-', 'F-', 'F#', 'G-', 'G#', 'A-', 'A#', 'B-'];
    var octave = Math.floor(pitch / 12) - 1;
    var note = pitch % 12;
    return noteNames[note] + octave;
}

// ============================================
// PATTERN DATA CONVERSION (for legacy compatibility)
// ============================================

// Convert tracker pattern.data to notes array
function trackerDataToNotes(pattern) {
    if (!pattern || !pattern.data) return [];

    var notes = [];
    var lpb = pattern.lpb || state.lpb;

    for (var step = 0; step < pattern.steps; step++) {
        var stepData = pattern.data[step];
        if (!stepData || !stepData.columns) continue;

        for (var col = 0; col < stepData.columns.length; col++) {
            var colData = stepData.columns[col];
            if (!colData) continue;

            var stepBeat = step / lpb;
            var noteStr = colData.note || '';
            var ampStr = colData.amp || '';
            var fxArr = colData.fx ? colData.fx.slice() : [];
            var fxHasValues = hasFxValues(fxArr);

            if (noteStr === NOTE_OFF) {
                notes.push({
                    type: 'cell',
                    startBeat: stepBeat,
                    column: col,
                    note: NOTE_OFF,
                    amp: ampStr || '',
                    fx: fxArr
                });
                continue;
            }

            if (noteStr && noteStr !== '---') {
                var pitch = noteNameToMidi(noteStr);
                if (pitch === null) continue;

                notes.push({
                    type: 'note',
                    pitch: pitch,
                    startBeat: stepBeat,
                    duration: null,  // Tracker notes are held until OFF/new note
                    velocity: hexToVelocity(ampStr),
                    column: col,
                    fx: fxArr
                });
                continue;
            }

            // No note - preserve amp/fx as a cell event if present
            if ((ampStr && ampStr !== '--') || fxHasValues) {
                notes.push({
                    type: 'cell',
                    startBeat: stepBeat,
                    column: col,
                    note: '',
                    amp: ampStr || '',
                    fx: fxArr
                });
            }
        }
    }

    return notes;
}

// Convert notes array to tracker pattern.data (for display/editing)
function notesToTrackerData(pattern) {
    if (!pattern) return;

    var lpb = pattern.lpb || state.lpb;
    var numNoteCols = pattern.noteColumns || 1;

    // Initialize empty data structure
    if (!pattern.data) pattern.data = [];
    for (var step = 0; step < pattern.steps; step++) {
        if (!pattern.data[step]) pattern.data[step] = { columns: [] };
        if (!pattern.data[step].columns) pattern.data[step].columns = [];
        while (pattern.data[step].columns.length < numNoteCols) {
            pattern.data[step].columns.push({ note: '', amp: '', fx: [] });
        }
        // Clear existing data
        for (var c = 0; c < numNoteCols; c++) {
            pattern.data[step].columns[c].note = '';
            pattern.data[step].columns[c].amp = '';
        }
    }

    // Populate from notes/events array
    if (!pattern.notes) return;

    var noteMap = {};

    // First pass: note events
    for (var i = 0; i < pattern.notes.length; i++) {
        var note = pattern.notes[i];
        if (!isNoteEvent(note)) continue;

        var step = Math.round(note.startBeat * lpb);
        var col = note.column || 0;

        if (step >= 0 && step < pattern.steps && col < numNoteCols) {
            var cell = pattern.data[step].columns[col];
            cell.note = midiToNoteName(note.pitch);
            cell.amp = (note.velocity === null || note.velocity === undefined) ? '' : velocityToHex(note.velocity);
            cell.fx = note.fx ? note.fx.slice() : [];
            noteMap[step + '_' + col] = true;
        }
    }

    // Second pass: cell events (only if no note event at that step/col)
    for (var i = 0; i < pattern.notes.length; i++) {
        var ev = pattern.notes[i];
        if (!isCellEvent(ev)) continue;

        var step = Math.round(ev.startBeat * lpb);
        var col = ev.column || 0;
        if (step < 0 || step >= pattern.steps || col < 0 || col >= numNoteCols) continue;

        if (noteMap[step + '_' + col]) continue;

        var cell = pattern.data[step].columns[col];
        if (ev.note === NOTE_OFF) {
            cell.note = NOTE_OFF;
        }
        if (ev.amp && ev.amp !== '--') {
            cell.amp = ev.amp;
        }
        if (ev.fx && ev.fx.length > 0) {
            cell.fx = ev.fx.slice();
        }
    }
}

// Sync pattern.data to pattern.notes (call when data is edited)
function syncDataToNotes(pattern) {
    if (!pattern) return;
    if (pattern.type === 'piano') return;
    pattern.notes = trackerDataToNotes(pattern);
}

// Sync pattern.notes to pattern.data (call when notes are edited)
function syncNotesToData(pattern) {
    if (!pattern || pattern.type === 'piano') return;
    notesToTrackerData(pattern);
}

// Create a new empty piano roll pattern (MIDI-style, continuous view)
function createPianoPattern(beats, lpb, trackId) {
    var patternNum = state.patterns ? state.patterns.length : 0;
    var beatsVal = beats || 4;
    var lpbVal = lpb || state.lpb;
    var pattern = {
        id: patternNum,
        name: 'Piano ' + (patternNum + 1),
        type: 'piano',
        trackId: trackId || 0,
        beats: beatsVal,
        lpb: lpbVal,
        steps: beatsVal * lpbVal,  // Derived for compatibility
        instrument: 1,
        noteColumns: 1,            // Piano roll typically uses 1 column
        fxColumns: [0],
        notes: []                  // Unified notes array
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

    var pattern = state.patterns[patternId];
    var clip = {
        id: Date.now() + Math.random(),  // Unique clip ID
        patternId: patternId,
        startBeat: actualStartBeat,
        loopCount: loopCount || 1,
        offset: 0,  // Offset into pattern in beats (for split clips)
        loopLength: pattern ? getPatternBeatsValue(pattern) : null
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

        // Use recording preview if this is the selected clip during recording
        if (state.isRecording && recordingPreviewBeats > patternBeats) {
            var selectedClip = getSelectedClip();
            if (selectedClip && selectedClip.id === clip.id) {
                patternBeats = recordingPreviewBeats;
            }
        }
    } else {
        var patternLpb = pattern.lpb || state.lpb;
        patternBeats = pattern.steps / patternLpb;
    }
    var loopCount = (clip.loopCount !== undefined && clip.loopCount !== null) ? clip.loopCount : 1;
    if (clip.loopLength !== undefined && clip.loopLength !== null) {
        return Math.max(0, clip.loopLength * loopCount);
    }
    var duration = patternBeats * loopCount - (clip.offset || 0);
    return Math.max(0, duration);
}

function getClipLoopLength(clip, pattern) {
    if (!clip || !pattern) return 0;
    if (clip.loopLength !== undefined && clip.loopLength !== null) return clip.loopLength;
    return getPatternBeatsValue(pattern);
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

function getPatternBeatsValue(pattern) {
    if (!pattern) return 0;
    if (pattern.type === 'piano') return pattern.beats || 4;
    var lpb = pattern.lpb || state.lpb;
    return (pattern.steps || 0) / lpb;
}

function quantizeBeatToLpb(beat, lpb) {
    var grid = lpb || state.lpb;
    if (!grid) return beat;
    return Math.round(beat * grid) / grid;
}

function cloneEvent(ev) {
    return JSON.parse(JSON.stringify(ev));
}

function getPatternEventsWithDurations(pattern) {
    if (!pattern || !pattern.notes) return [];

    var events = pattern.notes.map(function(ev) { return cloneEvent(ev); });
    var lpb = pattern.lpb || state.lpb;

    if (pattern.type !== 'piano') {
        deriveTrackerNoteDurations(events, lpb);
        var patternBeats = getPatternBeatsValue(pattern);
        for (var i = 0; i < events.length; i++) {
            var ev = events[i];
            if (!isNoteEvent(ev)) continue;
            if (typeof ev.duration !== 'number' || ev.duration <= 0) {
                var dur = patternBeats - ev.startBeat;
                ev.duration = dur > 0 ? dur : (1 / lpb);
            }
        }
    } else {
        for (var j = 0; j < events.length; j++) {
            var pEv = events[j];
            if (!isNoteEvent(pEv)) continue;
            if (typeof pEv.duration !== 'number' || pEv.duration <= 0) {
                pEv.duration = 1 / lpb;
            }
        }
    }

    return events;
}

function collectClipEventsForSegment(pattern, clip, segStart, segEnd) {
    if (!pattern || !clip) return [];
    if (segEnd <= segStart) return [];

    var patternBeats = getPatternBeatsValue(pattern);
    if (patternBeats <= 0) return [];

    var offset = clip.offset || 0;
    var events = getPatternEventsWithDurations(pattern);
    var result = [];

    // New loopLength-based behavior (non-destructive trim)
    if (clip.loopLength !== undefined && clip.loopLength !== null) {
        var loopLength = clip.loopLength;
        if (loopLength <= 0) return [];

        var loopStart = offset;
        var loopEnd = loopStart + loopLength;
        var wraps = loopEnd > patternBeats;
        var wrapEnd = loopEnd - patternBeats;

        function getLocalStart(evStart) {
            if (!wraps) {
                if (evStart < loopStart || evStart >= loopEnd) return null;
                return evStart - loopStart;
            }
            if (evStart >= loopStart && evStart < patternBeats) {
                return evStart - loopStart;
            }
            if (evStart >= 0 && evStart < wrapEnd) {
                return (patternBeats - loopStart) + evStart;
            }
            return null;
        }

        for (var i = 0; i < events.length; i++) {
            var ev = events[i];
            if (!ev) continue;
            var localStart = getLocalStart(ev.startBeat);
            if (localStart === null) continue;

            var isNote = isNoteEvent(ev);
            var evDur = isNote ? (ev.duration || 0) : 0;
            var maxDur = loopLength - localStart;
            if (isNote && evDur > maxDur) evDur = maxDur;

            var kStart = Math.floor((segStart - localStart) / loopLength) - 1;
            var kEnd = Math.floor((segEnd - localStart) / loopLength) + 1;

            for (var k = kStart; k <= kEnd; k++) {
                var evStart = localStart + (k * loopLength);
                if (isNote) {
                    var evEnd = evStart + evDur;
                    if (evEnd <= segStart || evStart >= segEnd) continue;

                    var newStart = Math.max(evStart, segStart);
                    var newEnd = Math.min(evEnd, segEnd);
                    var newDur = newEnd - newStart;
                    if (newDur <= 0) continue;

                    var newNote = cloneEvent(ev);
                    newNote.startBeat = newStart - segStart;
                    newNote.duration = newDur;
                    result.push(newNote);
                } else if (isCellEvent(ev)) {
                    if (evStart < segStart || evStart >= segEnd) continue;
                    var newCell = cloneEvent(ev);
                    newCell.startBeat = evStart - segStart;
                    result.push(newCell);
                }
            }
        }

        return result;
    }

    // Legacy offset/loopCount behavior
    for (var j = 0; j < events.length; j++) {
        var lev = events[j];
        if (!lev) continue;

        var isNoteLegacy = isNoteEvent(lev);
        var levDur = isNoteLegacy ? (lev.duration || 0) : 0;

        var kStartLegacy = Math.floor((segStart + offset - lev.startBeat - levDur) / patternBeats) - 1;
        var kEndLegacy = Math.floor((segEnd + offset - lev.startBeat) / patternBeats) + 1;

        for (var k2 = kStartLegacy; k2 <= kEndLegacy; k2++) {
            var levStart = lev.startBeat - offset + (k2 * patternBeats);
            if (isNoteLegacy) {
                var levEnd = levStart + levDur;
                if (levEnd <= segStart || levStart >= segEnd) continue;

                var newStartLegacy = Math.max(levStart, segStart);
                var newEndLegacy = Math.min(levEnd, segEnd);
                var newDurLegacy = newEndLegacy - newStartLegacy;
                if (newDurLegacy <= 0) continue;

                var newNoteLegacy = cloneEvent(lev);
                newNoteLegacy.startBeat = newStartLegacy - segStart;
                newNoteLegacy.duration = newDurLegacy;
                result.push(newNoteLegacy);
            } else if (isCellEvent(lev)) {
                if (levStart < segStart || levStart >= segEnd) continue;
                var newCellLegacy = cloneEvent(lev);
                newCellLegacy.startBeat = levStart - segStart;
                result.push(newCellLegacy);
            }
        }
    }

    return result;
}

function normalizeTrackerSegmentEvents(events, segmentBeats, lpb) {
    var grid = lpb || state.lpb;
    var maxBeat = segmentBeats;
    var normalized = [];
    var occupied = {};

    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!ev) continue;

        var start = quantizeBeatToLpb(ev.startBeat, grid);
        if (start < 0 || start >= maxBeat) continue;
        var col = ev.column || 0;

        if (isNoteEvent(ev)) {
            var end = quantizeBeatToLpb(ev.startBeat + ev.duration, grid);
            if (end <= start) continue;
            if (end > maxBeat) end = maxBeat;
            var dur = end - start;
            if (dur <= 0) continue;
            ev.startBeat = start;
            ev.duration = dur;
            normalized.push(ev);
        } else if (isCellEvent(ev)) {
            ev.startBeat = start;
            normalized.push(ev);
        }

        var stepKey = Math.round(start * grid) + '_' + col;
        occupied[stepKey] = true;
    }

    // Add note-off events at note ends (if not already present)
    for (var j = 0; j < normalized.length; j++) {
        var note = normalized[j];
        if (!isNoteEvent(note)) continue;
        if (typeof note.duration !== 'number' || note.duration <= 0) continue;
        var endBeat = note.startBeat + note.duration;
        if (endBeat >= maxBeat - 0.0001) continue;

        var endStep = Math.round(endBeat * grid);
        var endKey = endStep + '_' + (note.column || 0);
        if (occupied[endKey]) continue;

        normalized.push({
            type: 'cell',
            startBeat: endStep / grid,
            column: note.column || 0,
            note: NOTE_OFF,
            amp: '',
            fx: []
        });
        occupied[endKey] = true;
    }

    return normalized;
}

function buildPatternFromClipSegment(pattern, clip, segStart, segDuration) {
    if (!pattern || !clip) return null;
    if (segDuration <= 0) return null;

    var lpb = pattern.lpb || state.lpb;
    var minBeats = (pattern.type === 'piano') ? 0.0001 : (1 / lpb);
    var segStartBeat = segStart;
    var segEndBeat = segStart + segDuration;

    if (pattern.type !== 'piano') {
        segStartBeat = quantizeBeatToLpb(segStartBeat, lpb);
        segEndBeat = quantizeBeatToLpb(segEndBeat, lpb);
        if (segEndBeat <= segStartBeat) {
            segEndBeat = segStartBeat + minBeats;
        }
    }

    var segLen = Math.max(minBeats, segEndBeat - segStartBeat);
    var events = collectClipEventsForSegment(pattern, clip, segStartBeat, segStartBeat + segLen);

    var newPattern;
    if (pattern.type === 'piano') {
        newPattern = createPianoPattern(segLen, lpb, pattern.trackId);
    } else {
        var steps = Math.max(1, Math.round(segLen * lpb));
        newPattern = createTrackerPattern(steps, lpb, pattern.trackId);
        segLen = steps / lpb;
        events = normalizeTrackerSegmentEvents(events, segLen, lpb);
    }

    newPattern.instrument = pattern.instrument || 1;
    newPattern.noteColumns = pattern.noteColumns || 1;
    newPattern.fxColumns = pattern.fxColumns ? pattern.fxColumns.slice() : [0];
    newPattern.name = pattern.name || newPattern.name;
    newPattern.notes = events;

    if (newPattern.type !== 'piano') {
        syncNotesToData(newPattern);
    }

    return newPattern;
}

function addPatternToLibrary(pattern) {
    if (!pattern) return -1;
    pattern.id = state.patterns.length;
    state.patterns.push(pattern);
    return pattern.id;
}

function bakeClipToNewPattern(clip) {
    if (!clip) return -1;
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return -1;
    var duration = getClipDurationBeats(clip);
    if (duration <= 0) return -1;
    var baked = buildPatternFromClipSegment(pattern, clip, 0, duration);
    if (!baked) return -1;
    return addPatternToLibrary(baked);
}

function cleanupUnusedPatterns() {
    var used = {};
    for (var t = 0; t < state.tracks.length; t++) {
        var track = state.tracks[t];
        for (var c = 0; c < track.clips.length; c++) {
            used[track.clips[c].patternId] = true;
        }
    }

    var map = {};
    var newPatterns = [];
    for (var i = 0; i < state.patterns.length; i++) {
        var p = state.patterns[i];
        if (!p || !used[i]) continue;
        var newIdx = newPatterns.length;
        map[i] = newIdx;
        p.id = newIdx;
        newPatterns.push(p);
    }

    // Update clips to new pattern indices; drop clips pointing to missing patterns
    for (var t2 = 0; t2 < state.tracks.length; t2++) {
        var clips = state.tracks[t2].clips;
        for (var ci = clips.length - 1; ci >= 0; ci--) {
            var oldId = clips[ci].patternId;
            if (map[oldId] === undefined) {
                clips.splice(ci, 1);
                continue;
            }
            clips[ci].patternId = map[oldId];
        }
    }

    // Update clip clipboard pattern references
    if (clipboardClip) {
        if (map[clipboardClip.patternId] !== undefined) {
            clipboardClip.patternId = map[clipboardClip.patternId];
        } else {
            clipboardClip = null;
        }
    }
    if (clipboardClips && clipboardClips.clips) {
        var filtered = [];
        for (var cc = 0; cc < clipboardClips.clips.length; cc++) {
            var clipData = clipboardClips.clips[cc];
            if (map[clipData.patternId] !== undefined) {
                clipData.patternId = map[clipData.patternId];
                filtered.push(clipData);
            }
        }
        clipboardClips.clips = filtered;
        if (filtered.length === 0) {
            clipboardClips = null;
        } else {
            var minBeat = Infinity;
            var minTrack = Infinity;
            for (var f = 0; f < filtered.length; f++) {
                if (filtered[f].startBeat < minBeat) minBeat = filtered[f].startBeat;
                if (filtered[f].trackId < minTrack) minTrack = filtered[f].trackId;
            }
            clipboardClips.minBeat = minBeat;
            clipboardClips.minTrack = minTrack;
        }
    }

    state.patterns = newPatterns;
    invalidatePatternCache();
    patternNoteVizDirty = {};
    if (pendingNoteVizRefresh) {
        cancelAnimationFrame(pendingNoteVizRefresh);
        pendingNoteVizRefresh = null;
    }
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

// Find a piano roll pattern at the given beat on the selected track
function findPianoRollAtBeat(beat) {
    var trackId = state.selectedTrack;
    if (trackId === undefined || trackId === null) return null;

    var track = state.tracks[trackId];
    if (!track) return null;

    for (var c = 0; c < track.clips.length; c++) {
        var clip = track.clips[c];
        if (beat >= clip.startBeat && beat < getClipEndBeat(clip)) {
            var pattern = state.patterns[clip.patternId];
            if (pattern && pattern.type === 'piano') {
                return { clip: clip, pattern: pattern, trackId: trackId };
            }
        }
    }
    return null;
}

// Convert beat position to step within a pattern (accounting for loops)
// Returns { step, loopCount } for tracking duplicate triggers
function beatToPatternStep(clip, beat) {
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return { step: -1, loopCount: 0 };

    var localBeat = beat - clip.startBeat;
    if (localBeat < 0) return { step: -1, loopCount: 0 };

    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = pattern.steps / patternLpb;

    // Check if we've exceeded the clip's length
    var clipDuration = getClipDurationBeats(clip);
    if (localBeat >= clipDuration) return { step: -1, loopCount: 0 };

    // LoopLength-based trim
    if (clip.loopLength !== undefined && clip.loopLength !== null) {
        var loopLength = clip.loopLength;
        if (loopLength <= 0) return { step: -1, loopCount: 0 };

        var loopCount = Math.floor(localBeat / loopLength);
        var loopBeat = localBeat % loopLength;
        var patternBeat = (clip.offset || 0) + loopBeat;
        if (patternBeat >= patternBeats) patternBeat -= patternBeats;

        var step = Math.floor(patternBeat * patternLpb);
        return { step: Math.min(step, pattern.steps - 1), loopCount: loopCount };
    }

    // Legacy offset behavior
    localBeat = localBeat + (clip.offset || 0);
    var legacyLoopCount = Math.floor(localBeat / patternBeats);
    var legacyLoopBeat = localBeat % patternBeats;
    var legacyStep = Math.floor(legacyLoopBeat * patternLpb);

    return { step: Math.min(legacyStep, pattern.steps - 1), loopCount: legacyLoopCount };
}

// Get the currently selected clip
function getSelectedClip() {
    if (!state.selectedClip || state.selectedClip.trackId === null || state.selectedClip.clipId === null) {
        return null;
    }

    var track = state.tracks[state.selectedClip.trackId];
    if (!track) return null;

    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === state.selectedClip.clipId) {
            return track.clips[i];
        }
    }
    return null;
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

function ensureTimelineDefaults() {
    if (!state.timeline) state.timeline = {};
    if (state.timeline.snapToMeasure === undefined) state.timeline.snapToMeasure = true;
    if (state.timeline.gridSnap === undefined) state.timeline.gridSnap = 1;
    if (!state.timeline.gridSnapOptions || state.timeline.gridSnapOptions.length === 0) {
        state.timeline.gridSnapOptions = [
            { label: '1/256', beats: 1/64 },
            { label: '1/128', beats: 1/32 },
            { label: '1/64', beats: 1/16 },
            { label: '1/32', beats: 1/8 },
            { label: '1/16', beats: 1/4 },
            { label: '1/8', beats: 1/2 },
            { label: '1/4', beats: 1 },
            { label: '1/2', beats: 2 },
            { label: '1 Bar', beats: 4 }
        ];
    }
    if (state.timeline.loopEnabled === undefined) state.timeline.loopEnabled = false;
    if (state.timeline.loopStart === undefined) state.timeline.loopStart = 0;
    if (state.timeline.loopEnd === undefined) state.timeline.loopEnd = 16;
    if (state.timeline.totalBeats === undefined) state.timeline.totalBeats = 64;
    if (state.timeline.totalMeasures === undefined) {
        state.timeline.totalMeasures = beatsToMeasures(state.timeline.totalBeats);
    }
    if (state.timeline.cursorBeat === undefined) {
        state.timeline.cursorBeat = state.currentBeat || 0;
    }
    if (state.timeline.cursorTrack === undefined) {
        state.timeline.cursorTrack = state.selectedTrack || 0;
    }
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
var clipboardClips = null;

function renderTimeline() {
    var container = document.getElementById('timeline-tracks');
    if (!container) return;

    container.innerHTML = '';

    var start = state.visibleTrackStart;
    var end = Math.min(start + state.visibleTrackCount, state.tracks.length);

    // Auto-extend timeline based on clips (measure-aligned)
    autoExtendTimeline();
    var totalBeats = state.timeline.totalBeats;
    if (state.isRecording && recordingPreviewBeats > 0) {
        var selClip = getSelectedClip();
        if (selClip && (selClip.loopCount === undefined || selClip.loopCount <= 1.0001)) {
            var selPattern = state.patterns[selClip.patternId];
            if (selPattern && selPattern.type === 'piano') {
                var baseLoopLen = getClipLoopLength(selClip, selPattern);
                var previewBeats = Math.max(baseLoopLen, recordingPreviewBeats);
                if (previewBeats > baseLoopLen + 0.0001) {
                    var previewClip = {
                        patternId: selClip.patternId,
                        startBeat: selClip.startBeat,
                        loopCount: 1,
                        loopLength: previewBeats,
                        offset: selClip.offset || 0
                    };
                    var previewDuration = getClipDurationBeats(previewClip);
                    var previewEnd = selClip.startBeat + previewDuration;
                    if (previewEnd > totalBeats) {
                        totalBeats = snapToMeasureEnd(previewEnd);
                    }
                }
            }
        }
    }

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

    updateClipSelectionVisuals(selectedClips);

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

function clipKey(trackId, clipId) {
    return trackId + '_' + clipId;
}

function isClipSelected(trackId, clipId) {
    for (var i = 0; i < selectedClips.length; i++) {
        if (selectedClips[i].trackId === trackId && selectedClips[i].clipId === clipId) {
            return true;
        }
    }
    return false;
}

function updateClipSelectionVisuals(clips) {
    var selectedMap = {};
    for (var i = 0; i < clips.length; i++) {
        selectedMap[clipKey(clips[i].trackId, clips[i].clipId)] = true;
    }

    var clipEls = document.querySelectorAll('.timeline-clip');
    for (var j = 0; j < clipEls.length; j++) {
        var el = clipEls[j];
        var t = parseInt(el.getAttribute('data-track-id'));
        var c = parseFloat(el.getAttribute('data-clip-id'));
        if (selectedMap[clipKey(t, c)]) {
            el.classList.add('selected');
        } else {
            el.classList.remove('selected');
        }
    }
}

function setPrimaryClip(trackId, clipId) {
    state.selectedClip = { trackId: trackId, clipId: clipId };
    state.selectedTrack = trackId;
    state.focusedTrack = trackId;

    var track = state.tracks[trackId];
    var clip = null;
    if (track) {
        for (var i = 0; i < track.clips.length; i++) {
            if (track.clips[i].id === clipId) {
                clip = track.clips[i];
                break;
            }
        }
    }

    if (clip) {
        var pattern = state.patterns[clip.patternId];
        if (pattern) {
            updatePatternPianoTitle(trackId, pattern);

            var trackerContainer = document.getElementById('tracker-container');
            var pianoContainer = document.getElementById('piano-roll-container');
            var patternEditorArea = document.getElementById('pattern-editor-area');

            if (pattern.type === 'piano') {
                if (trackerContainer) trackerContainer.classList.add('hidden');
                if (pianoContainer) pianoContainer.classList.remove('hidden');
                if (patternEditorArea) patternEditorArea.classList.add('piano-mode');
                updatePianoInstrumentSelector();
                scheduleRenderPianoRoll();
            } else {
                if (trackerContainer) trackerContainer.classList.remove('hidden');
                if (pianoContainer) pianoContainer.classList.add('hidden');
                if (patternEditorArea) patternEditorArea.classList.remove('piano-mode');
                renderTrackerGrid(true);
            }
        }
    }

    renderTrackList();
}

function applyClipSelection(clips, primary) {
    selectedClips = [];
    var seen = {};
    for (var i = 0; i < clips.length; i++) {
        var key = clipKey(clips[i].trackId, clips[i].clipId);
        if (seen[key]) continue;
        seen[key] = true;
        selectedClips.push({ trackId: clips[i].trackId, clipId: clips[i].clipId });
    }

    updateClipSelectionVisuals(selectedClips);

    if (!primary && selectedClips.length > 0) {
        primary = selectedClips[0];
    }

    if (primary) {
        setPrimaryClip(primary.trackId, primary.clipId);
    } else {
        state.selectedClip = { trackId: null, clipId: null };
        renderTrackList();
    }
}

function findClipById(trackId, clipId) {
    var track = state.tracks[trackId];
    if (!track) return null;
    for (var i = 0; i < track.clips.length; i++) {
        if (track.clips[i].id === clipId) return track.clips[i];
    }
    return null;
}

function getClipExpandInfo(clip, pattern) {
    var info = {
        show: false,
        expanded: false,
        patternBeats: 0,
        clipLength: 0,
        bufferBeats: null,
        hasBuffer: false
    };
    if (!clip || !pattern) return info;

    var loopCount = (clip.loopCount !== undefined && clip.loopCount !== null) ? clip.loopCount : 1;
    if (loopCount > 1.0001) return info;

    var patternBeats = getPatternBeatsValue(pattern);
    var clipLength = (clip.loopLength !== undefined && clip.loopLength !== null) ? clip.loopLength : patternBeats;
    var bufferBeats = (pattern._bufferBeats !== undefined && pattern._bufferBeats !== null) ? pattern._bufferBeats : null;
    var hasBuffer = bufferBeats !== null && bufferBeats > patternBeats + 0.0001;

    info.patternBeats = patternBeats;
    info.clipLength = clipLength;
    info.bufferBeats = bufferBeats;
    info.hasBuffer = hasBuffer;
    info.show = true;
    info.expanded = hasBuffer;
    return info;
}

function cloneNotesArray(notes) {
    var out = [];
    if (!notes) return out;
    for (var i = 0; i < notes.length; i++) {
        if (!notes[i]) continue;
        out.push(cloneEvent(notes[i]));
    }
    return out;
}

function scaleEventsByRatio(events, ratio) {
    if (!events || Math.abs(ratio - 1) < 0.000001) return;
    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!ev) continue;
        if (typeof ev.startBeat === 'number') {
            ev.startBeat *= ratio;
        }
        if (isNoteEvent(ev) && typeof ev.duration === 'number' && ev.duration > 0) {
            ev.duration *= ratio;
        }
    }
}

function setPatternLengthFromBeats(pattern, beats) {
    if (!pattern) return;
    var length = Math.max(0, beats || 0);
    if (pattern.type === 'piano') {
        pattern.beats = length;
        return;
    }
    var lpb = pattern.lpb || state.lpb;
    var steps = Math.max(1, Math.round(length * lpb));
    pattern.steps = steps;
    pattern.beats = steps / lpb;
}

function isBeatInSegment(beat, offset, length, totalBeats) {
    if (length <= 0 || totalBeats <= 0) return false;
    var end = offset + length;
    if (end <= totalBeats) {
        return beat >= offset && beat < end;
    }
    var wrapEnd = end - totalBeats;
    return beat >= offset || beat < wrapEnd;
}

function mapBeatToBuffer(beat, offset, totalBeats) {
    var mapped = offset + beat;
    if (totalBeats > 0 && mapped >= totalBeats) {
        mapped -= totalBeats;
    }
    return mapped;
}

function mergeContractedNotesIntoBuffer(bufferNotes, bufferBeats, contractedNotes, offset, length) {
    var merged = [];
    var baseNotes = bufferNotes || [];
    var viewNotes = contractedNotes || [];

    for (var i = 0; i < baseNotes.length; i++) {
        var ev = baseNotes[i];
        if (!ev) continue;
        var beat = (typeof ev.startBeat === 'number') ? ev.startBeat : 0;
        if (!isBeatInSegment(beat, offset, length, bufferBeats)) {
            merged.push(cloneEvent(ev));
        }
    }

    for (var j = 0; j < viewNotes.length; j++) {
        var cv = viewNotes[j];
        if (!cv) continue;
        var mapped = cloneEvent(cv);
        var start = (typeof mapped.startBeat === 'number') ? mapped.startBeat : 0;
        mapped.startBeat = mapBeatToBuffer(start, offset, bufferBeats);
        merged.push(mapped);
    }

    return merged;
}

function buildBufferPattern(pattern, bufferNotes, bufferBeats) {
    var lpb = pattern.lpb || state.lpb;
    var steps = Math.max(1, Math.round(bufferBeats * lpb));
    return {
        type: pattern.type,
        notes: bufferNotes || [],
        beats: bufferBeats,
        lpb: pattern.lpb,
        steps: steps
    };
}

function applyPatternLengthWithBuffer(pattern, clip, newBeats) {
    if (!pattern) return false;
    var currentBeats = getPatternBeatsValue(pattern);
    var lpb = pattern.lpb || state.lpb;
    var grid = 1 / lpb;
    var targetBeats = Math.max(grid, Math.round(newBeats / grid) * grid);
    if (Math.abs(targetBeats - currentBeats) < 0.0001) return false;

    var offset = clip ? (clip.offset || 0) : 0;

    if (targetBeats < currentBeats - 0.0001) {
        if (!pattern._bufferNotes || !pattern._bufferBeats) {
            pattern._bufferNotes = cloneNotesArray(pattern.notes || []);
            pattern._bufferBeats = currentBeats;
        } else {
            pattern._bufferNotes = mergeContractedNotesIntoBuffer(
                pattern._bufferNotes,
                pattern._bufferBeats,
                pattern.notes || [],
                offset,
                currentBeats
            );
        }

        var bufferPattern = buildBufferPattern(pattern, pattern._bufferNotes, pattern._bufferBeats);
        var tempClip = { patternId: 0, offset: offset, loopLength: targetBeats, loopCount: 1 };
        pattern.notes = collectClipEventsForSegment(bufferPattern, tempClip, 0, targetBeats);
        setPatternLengthFromBeats(pattern, targetBeats);
    } else {
        if (pattern._bufferNotes && pattern._bufferBeats) {
            pattern._bufferNotes = mergeContractedNotesIntoBuffer(
                pattern._bufferNotes,
                pattern._bufferBeats,
                pattern.notes || [],
                offset,
                currentBeats
            );

            if (targetBeats <= pattern._bufferBeats + 0.0001) {
                var bufferPatternExpand = buildBufferPattern(pattern, pattern._bufferNotes, pattern._bufferBeats);
                var tempClipExpand = { patternId: 0, offset: offset, loopLength: targetBeats, loopCount: 1 };
                pattern.notes = collectClipEventsForSegment(bufferPatternExpand, tempClipExpand, 0, targetBeats);
            } else {
                pattern.notes = cloneNotesArray(pattern._bufferNotes);
            }
        }

        setPatternLengthFromBeats(pattern, targetBeats);

        if (pattern._bufferBeats && targetBeats >= pattern._bufferBeats - 0.0001) {
            pattern._bufferNotes = undefined;
            pattern._bufferBeats = undefined;
        }
    }

    if (clip) {
        var updatedBeats = getPatternBeatsValue(pattern);
        clip.loopLength = updatedBeats;
        clip.loopCount = 1;
        if (clip.offset) {
            clip.offset = updatedBeats > 0 ? (clip.offset % updatedBeats) : 0;
        }
    }

    var patternIndex = getPatternIndex(pattern);
    if (patternIndex >= 0) {
        markPatternNoteVizDirty(patternIndex);
        if (pattern.type !== 'piano') {
            pattern._needsGridRefresh = true;
        }
    }

    return true;
}

function toggleClipExpand(trackId, clipId) {
    var clip = findClipById(trackId, clipId);
    if (!clip) return;
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return;

    var info = getClipExpandInfo(clip, pattern);
    if (!info.show) return;
    if (info.patternBeats <= 0) return;

    if (info.hasBuffer) {
        applyPatternLengthWithBuffer(pattern, clip, info.bufferBeats);
    } else {
        applyPatternLengthWithBuffer(pattern, clip, info.clipLength);
    }

    var patternIndex = getPatternIndex(pattern);
    if (pattern.type !== 'piano') {
        invalidatePatternCache(patternIndex);
    }
    markPatternNoteVizDirty(patternIndex);

    renderTimeline();
    if (state.selectedClip && state.selectedClip.clipId === clip.id && state.selectedClip.trackId === trackId) {
        setPrimaryClip(trackId, clip.id);
    }
}

function shouldShowExpandHandle(clip, pattern) {
    var info = getClipExpandInfo(clip, pattern);
    return info.show;
}

function createClipElement(clip, trackId) {
    var pattern = state.patterns[clip.patternId];
    var renderClip = clip;
    if (state.isRecording && recordingPreviewBeats > 0 && pattern && pattern.type === 'piano') {
        var selectedClip = getSelectedClip();
        if (selectedClip && selectedClip.id === clip.id &&
            (clip.loopCount === undefined || clip.loopCount <= 1.0001)) {
            var baseLoopLen = getClipLoopLength(clip, pattern);
            var previewBeats = Math.max(baseLoopLen, recordingPreviewBeats);
            if (previewBeats > baseLoopLen + 0.0001) {
                renderClip = Object.assign({}, clip, { loopLength: previewBeats, loopCount: 1 });
            }
        }
    }

    var duration = getClipDurationBeats(renderClip);
    var clipWidth = duration * timelinePixelsPerBeat - 2;
    if (clipWidth < 2) clipWidth = 2;

    var el = document.createElement('div');
    el.className = 'timeline-clip';
    el.setAttribute('data-clip-id', clip.id);
    el.setAttribute('data-track-id', trackId);
    el.setAttribute('data-pattern-id', clip.patternId);
    el.style.left = (clip.startBeat * timelinePixelsPerBeat) + 'px';
    el.style.width = clipWidth + 'px';

    if (isClipSelected(trackId, clip.id)) {
        el.classList.add('selected');
    }
    var expandInfo = getClipExpandInfo(clip, pattern);
    if (expandInfo.expanded) {
        el.classList.add('expanded');
    }

    // Color based on pattern type
    if (pattern && pattern.type === 'piano') {
        el.style.background = 'linear-gradient(180deg, #6c63ff 0%, #4a42d4 100%)';
        el.classList.add('piano-clip');

        // Add recording preview indicator if this clip is being expanded
        if (state.isRecording && recordingPreviewBeats > 0) {
            var selectedClip = getSelectedClip();
            if (selectedClip && selectedClip.id === clip.id) {
                el.classList.add('recording-preview');
            }
        }
    } else {
        el.style.background = 'linear-gradient(180deg, #4ecca3 0%, #3ba888 100%)';
        el.classList.add('tracker-clip');
    }

    // Clip header with name
    var header = document.createElement('div');
    header.className = 'clip-header';
    var label = pattern ? pattern.name : 'Pattern ' + (clip.patternId + 1);
    if (clip.loopCount > 1) {
        label += ' \u00D7' + clip.loopCount;
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
    if (pattern && pattern.notes) {
        renderClipNotes(noteViz, pattern, renderClip);
    }

    // Loop handle (top-left) - changes loop count
    var loopHandle = document.createElement('div');
    loopHandle.className = 'clip-loop-handle';
    loopHandle.title = 'Drag to change loop count';
    loopHandle.textContent = '\u27F3';
    el.appendChild(loopHandle);

    // Right resize handle for loop count (drag edge)
    var resizeHandle = document.createElement('div');
    resizeHandle.className = 'clip-resize-handle';
    resizeHandle.title = 'Drag to change loop count';
    el.appendChild(resizeHandle);

    // Split handle (shows on hover at loop boundaries)
    var splitHandle = document.createElement('div');
    splitHandle.className = 'clip-split-handle';
    splitHandle.title = 'Click to split clip here';
    splitHandle.textContent = '\u2702';
    splitHandle.style.display = 'none';
    el.appendChild(splitHandle);

    // Expand/contract handle (side button) - only when not looped
    if (expandInfo.show) {
        var expandHandle = document.createElement('div');
        expandHandle.className = 'clip-expand-handle';
        expandHandle.title = 'Drag to expand/contract pattern length';
        expandHandle.textContent = expandInfo.hasBuffer ? '+' : '\u2194';
        el.appendChild(expandHandle);
    }

    // Show split handle on hover at grid snap positions
    if (pattern) {
        el.addEventListener('mousemove', function(e) {
            if (clipDragState.active) {
                splitHandle.style.display = 'none';
                return;
            }

            var pt = getScaledOffsetInElement(e, el);
            var x = pt.x;
            var clipBeats = getClipDurationBeats(clip);
            if (clipBeats <= 0) return;
            var pixelsPerBeat = clipWidth / clipBeats;
            var gridSnap = state.timeline.gridSnap || 1;
            var gridPixels = gridSnap * pixelsPerBeat;

            // Only show if grid snap markers are far enough apart
            if (gridPixels < 2) {
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
function renderClipNotes(canvas, pattern, clipOrLoopCount) {
    var ctx = canvas.getContext('2d');
    var width = canvas.width;
    var height = canvas.height;

    ctx.clearRect(0, 0, width, height);

    if (!pattern) return;

    var clip = (clipOrLoopCount && typeof clipOrLoopCount === 'object') ? clipOrLoopCount : null;
    var loopCount = (clip && typeof clip.loopCount === 'number') ? clip.loopCount : (typeof clipOrLoopCount === 'number' ? clipOrLoopCount : 1);
    var patternLpb = pattern.lpb || state.lpb;
    var patternBeats = getPatternBeatsValue(pattern);
    var totalBeats = clip ? getClipDurationBeats(clip) : (patternBeats * loopCount);
    if (totalBeats <= 0) return;

    var pixelsPerBeat = width / totalBeats;
    var baseNotes = pattern && pattern.notes ? pattern.notes : [];
    var eventSource = clip ? collectClipEventsForSegment(pattern, clip, 0, totalBeats) : baseNotes;

    // Find note range for scaling
    var minNote = 127, maxNote = 0;
    var notes = [];

    for (var i = 0; i < eventSource.length; i++) {
        var ev = eventSource[i];
        if (!isNoteEvent(ev)) continue;
        if (ev.pitch === null || ev.pitch === undefined) continue;
        var dur = (typeof ev.duration === 'number' && ev.duration > 0) ? ev.duration : (1 / patternLpb);
        minNote = Math.min(minNote, ev.pitch);
        maxNote = Math.max(maxNote, ev.pitch);
        notes.push({
            startBeat: ev.startBeat,
            duration: dur,
            note: ev.pitch
        });
    }

    if (notes.length > 0) {
        // Add some padding to note range
        var noteRange = Math.max(maxNote - minNote, 12);
        var noteCenter = (maxNote + minNote) / 2;
        minNote = Math.floor(noteCenter - noteRange / 2);
        maxNote = Math.ceil(noteCenter + noteRange / 2);

        ctx.fillStyle = 'rgba(255, 255, 255, 0.8)';

        for (var n = 0; n < notes.length; n++) {
            var note = notes[n];
            var x = note.startBeat * pixelsPerBeat;
            var w = Math.max((note.duration) * pixelsPerBeat - 1, 2);
            var y = height - ((note.note - minNote) / (maxNote - minNote)) * (height - 4) - 2;
            var h = Math.max(2, (height - 4) / noteRange);

            ctx.fillRect(x, y, w, h);
        }
    }

    if (clip) {
        var loopLength = getClipLoopLength(clip, pattern);
        var loopMarker = patternBeats > 0 ? patternBeats : loopLength;
        if (loopMarker > 0 && totalBeats > loopMarker + 0.0001) {
            ctx.save();
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.55)';
            ctx.lineWidth = 1;
            for (var b = loopMarker; b < totalBeats - 0.0001; b += loopMarker) {
                var lx = Math.round(b * pixelsPerBeat) + 0.5;
                ctx.beginPath();
                ctx.moveTo(lx, 0);
                ctx.lineTo(lx, height);
                ctx.stroke();
            }
            ctx.restore();
        }
    }
}

// Convert note name to MIDI number
function noteNameToMidi(noteName) {
    if (!noteName || noteName === '' || noteName === NOTE_OFF) return null;

    var noteMap = { 'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11 };
    var match = noteName.match(/^([A-G])([#b]?)-?(\d+)$/i);
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
        var scale = getUiScale();
        var scrollX = timelineTracks.scrollLeft;
        var relativeX = (mouseX - rect.left) / scale + scrollX;
        var beatAtMouse = relativeX / oldZoom;
        var newX = beatAtMouse * timelinePixelsPerBeat;
        timelineTracks.scrollLeft = newX - ((mouseX - rect.left) / scale);
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
    var subdivisions = [
        { div: 1/64 },   // 256th notes
        { div: 1/32 },   // 128th notes
        { div: 1/16 },   // 64th notes
        { div: 1/8 },    // 32nd notes
        { div: 1/4 },    // 16th notes
        { div: 1/2 },    // 8th notes
        { div: 1 },      // quarter notes (beats)
    ];

    var subDiv = 1;
    for (var s = 0; s < subdivisions.length; s++) {
        if (subdivisions[s].div * timelinePixelsPerBeat >= 20) {
            subDiv = subdivisions[s].div;
            break;
        }
    }

    // Use integer steps to avoid floating point accumulation errors
    // Multiply everything by a large factor, iterate as integers, divide back
    var stepMul = Math.round(1 / subDiv); // e.g. subDiv=0.25 -> stepMul=4
    var startIdx = Math.floor(startBeat * stepMul);
    var endIdx = Math.ceil(endBeat * stepMul);

    var maxMarkers = Math.ceil(viewWidth / 15) + 20;
    var markerCount = 0;
    var barPixels = beatsPerBar * timelinePixelsPerBeat;
    var minBarLabelPx = 60;
    var barLabelStep = 1;
    if (barPixels > 0) {
        barLabelStep = Math.max(1, Math.ceil(minBarLabelPx / barPixels));
    }

    for (var idx = startIdx; idx <= endIdx && markerCount < maxMarkers; idx++) {
        var beatPos = idx / stepMul;
        if (beatPos < 0) continue;

        var xPos = beatPos * timelinePixelsPerBeat;
        var marker = document.createElement('span');
        marker.style.position = 'absolute';
        marker.style.left = xPos + 'px';

        // Use integer arithmetic to classify: bar, beat, or sub-beat
        var beatsPerBarMul = beatsPerBar * stepMul;
        var isBar = (idx % beatsPerBarMul) === 0;
        var isBeat = (idx % stepMul) === 0;

        if (isBar) {
            var bar = Math.floor(idx / beatsPerBarMul) + 1;
            if (((bar - 1) % barLabelStep) !== 0) {
                continue;
            }
            marker.className = 'bar-marker';
            marker.textContent = bar;
            ruler.appendChild(marker);
            markerCount++;
        }
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
    var totalBeats = state.timeline.loopEnabled ? state.timeline.loopEnd : state.timeline.totalBeats;

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
    uiFocus = 'timeline';
    if (clipDragState.suppressClick) {
        clipDragState.suppressClick = false;
        return;
    }
    if (timelineSelection.suppressClick) {
        timelineSelection.suppressClick = false;
        return;
    }
    var target = e.target;

    // Hide context menu on click
    hideTimelineContextMenu();

    // Click on expand/contract handle (no-op; drag handles length)
    if (target.classList.contains('clip-expand-handle')) {
        e.stopPropagation();
        return;
    }

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
        !target.classList.contains('clip-resize-handle')) {
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));
        updateTimelineCursorFromEvent(e, trackId);
        selectClip(trackId, clipId);
        return;
    }

    // Click on empty track row or ruler - set playback position
    var row = target.closest('.timeline-track-row');
    if (row) {
        var trackId = parseInt(row.getAttribute('data-track-id'));
        state.selectedTrack = trackId;
        state.focusedTrack = trackId;
        renderTrackList();

        // Set playback position from click
        setPlayheadFromClick(e, trackId);
    }
}

// Set the playhead position from a click event on the timeline
function setPlayheadFromClick(e, trackId) {
    var container = document.getElementById('timeline-tracks');
    if (!container) return;

    var beat = getTimelineBeatFromClientX(e.clientX, container);
    updateTimelineCursor(beat, trackId);
    state.currentBeat = beat;

    // Show and position the playhead
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) {
        playhead.style.display = 'block';
        playhead.style.left = (beat * timelinePixelsPerBeat) + 'px';
    }

    // Update position display
    updateTimelinePlayhead();
}

function getTimelineBeatFromClientX(clientX, container) {
    if (!container) return 0;
    var rect = container.getBoundingClientRect();
    var scale = getUiScale();
    var clickX = (clientX - rect.left) / scale + container.scrollLeft;
    var beat = clickX / timelinePixelsPerBeat;

    var snapBeats = state.timeline.gridSnap || 1;
    beat = Math.round(beat / snapBeats) * snapBeats;
    return Math.max(0, beat);
}

function updateTimelineCursor(beat, trackId) {
    if (typeof beat === 'number' && !isNaN(beat)) {
        state.timeline.cursorBeat = beat;
    }
    if (typeof trackId === 'number' && !isNaN(trackId)) {
        state.timeline.cursorTrack = trackId;
    }
}

function updateTimelineCursorFromEvent(e, trackId) {
    var container = document.getElementById('timeline-tracks');
    if (!container) return;
    var beat = getTimelineBeatFromClientX(e.clientX, container);
    updateTimelineCursor(beat, trackId);
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

    // Calculate split position within clip
    var localBeat = splitBeat - clip.startBeat;
    var clipDuration = getClipDurationBeats(clip);
    if (clipDuration <= 0) return;

    // Quantize split for tracker patterns to step grid
    if (pattern.type !== 'piano') {
        var lpb = pattern.lpb || state.lpb;
        localBeat = quantizeBeatToLpb(localBeat, lpb);
        clipDuration = quantizeBeatToLpb(clipDuration, lpb);
    }

    if (localBeat <= 0.0001 || localBeat >= clipDuration - 0.0001) return;

    var patternBeats = getPatternBeatsValue(pattern);
    var loopLength = getClipLoopLength(clip, pattern);
    if (loopLength <= 0) return;

    var leftDuration = localBeat;
    var rightDuration = clipDuration - localBeat;
    if (leftDuration <= 0 || rightDuration <= 0) return;

    var rightOffset = (clip.offset || 0) + (localBeat % loopLength);
    if (patternBeats > 0) {
        rightOffset = ((rightOffset % patternBeats) + patternBeats) % patternBeats;
    }

    // Keep the original loop window and only split playback duration.
    // This preserves the full pattern data instead of turning each side into a new mini-loop.
    var leftLoopCount = leftDuration / loopLength;
    var rightLoopCount = rightDuration / loopLength;
    if (leftLoopCount <= 0 || rightLoopCount <= 0) return;
    leftLoopCount = parseFloat(leftLoopCount.toFixed(8));
    rightLoopCount = parseFloat(rightLoopCount.toFixed(8));

    // Update original clip to left segment
    clip.isExpanded = false;
    clip.trimOffset = undefined;
    clip.trimLoopLength = undefined;
    clip.trimLoopCount = undefined;
    clip.loopLength = loopLength;
    clip.loopCount = leftLoopCount;

    // Create new clip for right segment
    var newClip = {
        id: Date.now() + Math.random(),
        patternId: clip.patternId,
        startBeat: clip.startBeat + localBeat,
        loopCount: rightLoopCount,
        offset: rightOffset,
        loopLength: loopLength,
        isExpanded: false
    };

    track.clips.push(newClip);

    renderTimeline();
    if (state.selectedClip && state.selectedClip.clipId === clip.id && state.selectedClip.trackId === trackId) {
        setPrimaryClip(trackId, clip.id);
    }
    consoleLog('Split clip at beat ' + (clip.startBeat + localBeat).toFixed(2));
}

// Timeline right-click context menu
var timelineContextState = {
    trackId: 0,
    beat: 0,
    clipId: null
};

function handleTimelineContextMenu(e) {
    e.preventDefault();
    uiFocus = 'timeline';

    var target = e.target;
    var menu = document.getElementById('timeline-context-menu');
    if (!menu) return;

    // Get track and beat from click position
    var row = target.closest('.timeline-track-row');
    if (row) {
        timelineContextState.trackId = parseInt(row.getAttribute('data-track-id'));
        var container = document.getElementById('timeline-tracks');
        timelineContextState.beat = getTimelineBeatFromClientX(e.clientX, container);
        updateTimelineCursor(timelineContextState.beat, timelineContextState.trackId);
    } else {
        var container = document.getElementById('timeline-tracks');
        if (container) {
            timelineContextState.trackId = state.selectedTrack >= 0 ? state.selectedTrack : 0;
            timelineContextState.beat = getTimelineBeatFromClientX(e.clientX, container);
            updateTimelineCursor(timelineContextState.beat, timelineContextState.trackId);
        }
    }

    // Check if clicking on a clip (or any of its children like header/canvas/handles)
    var clipEl = target.closest('.timeline-clip');
    if (clipEl) {
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var clipTrackId = parseInt(clipEl.getAttribute('data-track-id'));
        timelineContextState.clipId = clipId;
        if (!isClipSelected(clipTrackId, clipId)) {
            selectClip(clipTrackId, clipId);
        }
        menu.querySelector('[data-action="delete-clip"]').style.display = 'block';
        var uniqueItem = menu.querySelector('[data-action="make-unique"]');
        var convertItem = menu.querySelector('[data-action="convert-pattern"]');
        if (uniqueItem) uniqueItem.style.display = 'block';
        if (convertItem) {
            convertItem.style.display = 'block';
            var clip = findClipById(clipTrackId, clipId);
            var pattern = clip ? state.patterns[clip.patternId] : null;
            if (pattern && pattern.type === 'piano') {
                convertItem.textContent = 'Convert to Tracker';
            } else {
                convertItem.textContent = 'Convert to Piano Roll';
            }
        }
    } else {
        timelineContextState.clipId = null;
        menu.querySelector('[data-action="delete-clip"]').style.display = 'none';
        var uniqueItem = menu.querySelector('[data-action="make-unique"]');
        var convertItem = menu.querySelector('[data-action="convert-pattern"]');
        if (uniqueItem) uniqueItem.style.display = 'none';
        if (convertItem) convertItem.style.display = 'none';
    }

    // Position and show menu
    menu.style.display = 'block';
    positionMenuAtClient(menu, e.clientX, e.clientY);
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
                selectClip(timelineContextState.trackId, timelineContextState.clipId);
                copyClip();
            }
            break;
        case 'cut-clip':
            if (timelineContextState.clipId !== null) {
                selectClip(timelineContextState.trackId, timelineContextState.clipId);
                cutClip();
            }
            break;
        case 'paste-clip':
            pasteClips(timelineContextState.trackId, timelineContextState.beat);
            break;
        case 'delete-clip':
            if (timelineContextState.clipId !== null) {
                removeClipFromTrack(timelineContextState.trackId, timelineContextState.clipId);
                cleanupUnusedPatterns();
                renderTimeline();
                consoleLog('Deleted clip');
            }
            break;
        case 'make-unique':
            if (timelineContextState.clipId !== null) {
                makeSelectedClipsUnique();
            }
            break;
        case 'convert-pattern':
            if (timelineContextState.clipId !== null) {
                convertSelectedClipPattern();
            }
            break;
        case 'add-piano-roll':
            addPianoRollToTrack(timelineContextState.trackId, timelineContextState.beat);
            break;
    }
}

// ============================================
// CODE EDITOR CONTEXT MENU
// ============================================

var codeEditorContextState = {
    textarea: null,
    selectionStart: 0,
    selectionEnd: 0
};

function handleCodeEditorContextMenu(e) {
    e.preventDefault();

    var menu = document.getElementById('code-editor-context-menu');
    if (!menu) return;

    codeEditorContextState.textarea = e.target;
    codeEditorContextState.selectionStart = e.target.selectionStart;
    codeEditorContextState.selectionEnd = e.target.selectionEnd;

    menu.style.display = 'block';
    positionMenuAtClient(menu, e.clientX, e.clientY);

    // Hide on click elsewhere
    setTimeout(function() {
        document.addEventListener('click', hideCodeEditorContextMenu, { once: true });
    }, 0);
}

function hideCodeEditorContextMenu() {
    var menu = document.getElementById('code-editor-context-menu');
    if (menu) menu.style.display = 'none';
}

function handleCodeEditorContextAction(action) {
    hideCodeEditorContextMenu();

    switch (action) {
        case 'insert-sampler':
            insertCodeTemplate('sampler');
            break;
        case 'insert-oscillator':
            insertCodeTemplate('oscillator');
            break;
        case 'insert-envelope':
            insertCodeTemplate('envelope');
            break;
        case 'insert-filter':
            insertCodeTemplate('filter');
            break;
        case 'insert-reverb':
            insertCodeTemplate('reverb');
            break;
        case 'insert-pfield-comment':
            insertCodeTemplate('pfield');
            break;
    }
}

var codeTemplates = {
    sampler: `    iSample = 100
    iLen    = ftlen(iSample)

    ; parameters
    iFreqHz   = max(p4, 0.001)    ; desired frequency in Hz
    iOffsetN  = limit(p6, 0, 1)   ; normalized offset 0–1
    iBaseNote = 60                 ; MIDI note for C-5
    iBaseFreq = 261.6256           ; Hz for C-5

    ; playback speed ratio
    iRate = iFreqHz / iBaseFreq

    ; offset in samples
    iStart = iOffsetN * iLen
    iEnd   = iLen
    iDist  = iLen - iStart

    ; compute duration in seconds
    iDur = iDist / (sr * iRate)

    ; one-shot ramp
    aPos linseg iStart, iDur, iEnd

    ; table read
    aSig tab aPos, iSample

    outs aSig, aSig`,

    oscillator: `    ; Oscillator with multiple waveforms
    iFreq = p4
    iAmp  = p5

    ; Choose waveform: 0=sine, 1=saw, 2=square, 3=triangle
    iWave = 0

    if (iWave == 0) then
        aOsc poscil iAmp, iFreq
    elseif (iWave == 1) then
        aOsc vco2 iAmp, iFreq, 0      ; sawtooth
    elseif (iWave == 2) then
        aOsc vco2 iAmp, iFreq, 10     ; square
    else
        aOsc vco2 iAmp, iFreq, 12     ; triangle
    endif

    outs aOsc, aOsc`,

    envelope: `    ; ADSR Envelope
    iAtt  = 0.01    ; attack time
    iDec  = 0.1     ; decay time
    iSus  = 0.7     ; sustain level (0-1)
    iRel  = 0.3     ; release time

    ; Create envelope
    aEnv madsr iAtt, iDec, iSus, iRel

    ; Apply to signal
    aOut = aSig * aEnv`,

    filter: `    ; Lowpass Filter with resonance
    iCutoff = 2000   ; cutoff frequency in Hz
    iRes    = 0.5    ; resonance (0-1)

    ; Moog-style lowpass filter
    aFilt moogladder aSig, iCutoff, iRes

    ; Alternative: Butterworth lowpass
    ; aFilt butterlp aSig, iCutoff`,

    reverb: `    ; Stereo Reverb
    iRoomSize = 0.8     ; room size (0-1)
    iDamp     = 0.5     ; high frequency damping (0-1)
    iMix      = 0.3     ; wet/dry mix (0-1)

    ; Freeverb algorithm
    aRevL, aRevR freeverb aSig, aSig, iRoomSize, iDamp

    ; Mix dry and wet
    aOutL = aSig * (1 - iMix) + aRevL * iMix
    aOutR = aSig * (1 - iMix) + aRevR * iMix

    outs aOutL, aOutR`,

    pfield: `    ; P-field reference:
    ; p1 = instrument number (fractional for polyphony)
    ; p2 = start time
    ; p3 = duration (-1 for held notes)
    ; p4 = frequency (Hz)
    ; p5 = amplitude (0-1)
    ; p6 = fx1 value
    ; p7 = fx2 value
    ; ...etc`
};

function insertCodeTemplate(templateName) {
    var textarea = codeEditorContextState.textarea || document.getElementById('code-editor');
    if (!textarea) return;

    var code = codeTemplates[templateName];
    if (!code) return;

    var pos = codeEditorContextState.selectionStart;
    var before = textarea.value.substring(0, pos);
    var after = textarea.value.substring(codeEditorContextState.selectionEnd);

    textarea.value = before + code + after;
    textarea.selectionStart = textarea.selectionEnd = pos + code.length;
    textarea.focus();

    saveCurrentInstrument();
    consoleLog('Inserted ' + templateName + ' template');
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

function addPianoRollToTrack(trackId, beat) {
    // Create a new piano roll pattern with default 4 beats
    var beats = 4;
    var lpb = state.lpb;

    var pattern = createPianoPattern(beats, lpb, trackId);
    state.patterns.push(pattern);
    var patternId = state.patterns.length - 1;

    // Add clip to track
    var clip = addClipToTrack(trackId, patternId, beat, 1);
    if (clip) {
        renderTimeline();
        selectClip(trackId, clip.id);
        consoleLog('Added piano roll to track ' + (trackId + 1));
    }
}

function selectClip(trackId, clipId, options) {
    options = options || {};
    var keepExisting = !!options.keepExisting;

    var clips = keepExisting ? selectedClips.slice() : [];
    if (!isClipSelected(trackId, clipId)) {
        clips.push({ trackId: trackId, clipId: clipId });
    }

    applyClipSelection(clips, { trackId: trackId, clipId: clipId });
}

function updatePatternPianoTitle(trackId, pattern) {
    var titleEl = document.getElementById('pattern-editor-title');
    if (titleEl) {
        var patternType = pattern.type === 'piano' ? ' [Piano Roll]' : '';
        titleEl.textContent = 'Pattern: ' + (pattern.name || 'Untitled') + patternType + ' (Track ' + (trackId + 1) + ')';
    }

    // Update pattern controls
    var stepsInput = document.getElementById('pattern-steps');
    var lpbInput = document.getElementById('pattern-lpb');

    if (stepsInput) {
        // For piano patterns, calculate steps from beats
        var steps = pattern.type === 'piano' ? (pattern.beats * (pattern.lpb || state.lpb)) : (pattern.steps || 16);
        stepsInput.value = steps;
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
        var totalBeats = state.timeline.loopEnabled ? state.timeline.loopEnd : state.timeline.totalBeats;

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
    mode: null,       // 'move', 'resize', 'expand-handle', or 'end-marker'
    clipId: null,
    trackId: null,
    currentTrackId: null,
    startX: 0,
    startBeat: 0,
    startLoopCount: 1,
    clipElement: null,
    startTotalBeats: 0,
    startPatternBeats: 0,
    lastPatternBeats: 0,
    suppressClick: false,
    didDrag: false
};

var timelineSelection = {
    active: false,
    startX: 0,
    startY: 0,
    endX: 0,
    endY: 0,
    didDrag: false,
    suppressClick: false,
    boxEl: null
};

function getTimelineTrackIdAt(clientY) {
    var container = document.getElementById('timeline-tracks');
    if (!container) return null;
    var rect = container.getBoundingClientRect();
    var scale = getUiScale();
    var y = (clientY - rect.top) / scale + container.scrollTop;
    var row = container.querySelector('.timeline-track-row');
    var rowHeight = row ? row.offsetHeight : 60;
    if (rowHeight <= 0) rowHeight = 60;
    var rowIndex = Math.floor(y / rowHeight);
    var trackId = state.visibleTrackStart + rowIndex;
    if (trackId < 0 || trackId >= state.tracks.length) return null;
    return trackId;
}

function moveClipToTrack(clipId, fromTrackId, toTrackId) {
    if (fromTrackId === toTrackId) return null;
    var fromTrack = state.tracks[fromTrackId];
    var toTrack = state.tracks[toTrackId];
    if (!fromTrack || !toTrack) return null;

    var clipIndex = -1;
    for (var i = 0; i < fromTrack.clips.length; i++) {
        if (fromTrack.clips[i].id === clipId) {
            clipIndex = i;
            break;
        }
    }
    if (clipIndex < 0) return null;

    var clip = fromTrack.clips.splice(clipIndex, 1)[0];
    toTrack.clips.push(clip);

    for (var j = 0; j < selectedClips.length; j++) {
        if (selectedClips[j].clipId === clipId && selectedClips[j].trackId === fromTrackId) {
            selectedClips[j].trackId = toTrackId;
        }
    }

    if (state.selectedClip && state.selectedClip.clipId === clipId && state.selectedClip.trackId === fromTrackId) {
        state.selectedClip.trackId = toTrackId;
        state.selectedTrack = toTrackId;
        state.focusedTrack = toTrackId;
    }

    return clip;
}

function handleTimelineMouseDown(e) {
    uiFocus = 'timeline';
    var target = e.target;

    if (target.classList.contains('clip-expand-handle')) {
        e.preventDefault();
        var clipEl = target.closest('.timeline-clip');
        if (!clipEl) return;
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));
        var clip = findClipById(trackId, clipId);
        if (!clip) return;
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        var info = getClipExpandInfo(clip, pattern);
        if (!info.show) return;

        selectClip(trackId, clipId);

        clipDragState.active = true;
        clipDragState.mode = 'expand-handle';
        clipDragState.clipId = clipId;
        clipDragState.trackId = trackId;
        clipDragState.currentTrackId = trackId;
        clipDragState.startX = getScaledClientX(e);
        clipDragState.startPatternBeats = info.patternBeats;
        clipDragState.lastPatternBeats = info.patternBeats;
        clipDragState.clipElement = clipEl;
        clipDragState.didDrag = false;
        document.body.style.cursor = 'ew-resize';
        return;
    }

    // Check if clicking on song end marker
    if (target.classList.contains('timeline-end-marker')) {
        e.preventDefault();
        clipDragState.active = true;
        clipDragState.mode = 'end-marker';
        clipDragState.startX = getScaledClientX(e);
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
        clipDragState.startX = getScaledClientX(e);
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
        clipDragState.startX = getScaledClientX(e);
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
            clip.isExpanded = false;
            clip.trimOffset = undefined;
            clip.trimLoopLength = undefined;
            clip.trimLoopCount = undefined;
            clipDragState.active = true;
            clipDragState.mode = 'resize';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.currentTrackId = trackId;
            clipDragState.startX = getScaledClientX(e);
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
            clip.isExpanded = false;
            clip.trimOffset = undefined;
            clip.trimLoopLength = undefined;
            clip.trimLoopCount = undefined;
            clipDragState.active = true;
            clipDragState.mode = 'loop-handle';
            clipDragState.clipId = clipId;
            clipDragState.trackId = trackId;
            clipDragState.currentTrackId = trackId;
            clipDragState.startX = getScaledClientX(e);
            clipDragState.startLoopCount = clip.loopCount;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'ew-resize';
        }
        return;
    }

    // Start multi-clip selection drag on empty track area
    var row = target.closest('.timeline-track-row');
    var clipEl = target.closest('.timeline-clip');
    if (row && !clipEl && e.button === 0) {
        startTimelineSelection(e);
        return;
    }

    // Check if clicking on clip (for dragging) - but not on handles
    var clipEl = target.closest('.timeline-clip');
    if (clipEl && !target.classList.contains('clip-loop-handle') &&
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
            clipDragState.currentTrackId = trackId;
            clipDragState.startX = getScaledClientX(e);
            clipDragState.startBeat = clip.startBeat;
            clipDragState.clipElement = clipEl;
            document.body.style.cursor = 'grabbing';

            // Select clip and show its pattern in the editor
            selectClip(trackId, clipId);
        }
    }
}

function startTimelineSelection(e) {
    var container = document.getElementById('timeline-tracks');
    if (!container) return;
    var content = container.querySelector('.timeline-content');
    if (!content) return;

    e.preventDefault();
    var rect = container.getBoundingClientRect();
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale + container.scrollLeft;
    var y = (e.clientY - rect.top) / scale + container.scrollTop;

    timelineSelection.active = true;
    timelineSelection.didDrag = false;
    timelineSelection.startX = x;
    timelineSelection.startY = y;
    timelineSelection.endX = x;
    timelineSelection.endY = y;

    if (!timelineSelection.boxEl) {
        timelineSelection.boxEl = document.createElement('div');
        timelineSelection.boxEl.className = 'timeline-selection-box';
    }

    timelineSelection.boxEl.style.left = x + 'px';
    timelineSelection.boxEl.style.top = y + 'px';
    timelineSelection.boxEl.style.width = '0px';
    timelineSelection.boxEl.style.height = '0px';
    if (!content.contains(timelineSelection.boxEl)) {
        content.appendChild(timelineSelection.boxEl);
    }

    document.addEventListener('mousemove', onTimelineSelectionMouseMove);
    document.addEventListener('mouseup', onTimelineSelectionMouseUp);
}

function onTimelineSelectionMouseMove(e) {
    if (!timelineSelection.active) return;
    var container = document.getElementById('timeline-tracks');
    if (!container) return;

    var rect = container.getBoundingClientRect();
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale + container.scrollLeft;
    var y = (e.clientY - rect.top) / scale + container.scrollTop;

    timelineSelection.endX = x;
    timelineSelection.endY = y;

    var minX = Math.min(timelineSelection.startX, timelineSelection.endX);
    var maxX = Math.max(timelineSelection.startX, timelineSelection.endX);
    var minY = Math.min(timelineSelection.startY, timelineSelection.endY);
    var maxY = Math.max(timelineSelection.startY, timelineSelection.endY);

    var moved = Math.abs(maxX - minX) > 3 || Math.abs(maxY - minY) > 3;
    if (moved) timelineSelection.didDrag = true;

    if (timelineSelection.boxEl) {
        timelineSelection.boxEl.style.left = minX + 'px';
        timelineSelection.boxEl.style.top = minY + 'px';
        timelineSelection.boxEl.style.width = (maxX - minX) + 'px';
        timelineSelection.boxEl.style.height = (maxY - minY) + 'px';
    }

    if (!timelineSelection.didDrag) return;

    var selected = [];
    var clipEls = document.querySelectorAll('.timeline-clip');
    var containerRect = container.getBoundingClientRect();

    for (var i = 0; i < clipEls.length; i++) {
        var clipEl = clipEls[i];
        var clipRect = clipEl.getBoundingClientRect();
        var left = (clipRect.left - containerRect.left) / scale + container.scrollLeft;
        var right = left + clipRect.width / scale;
        var top = (clipRect.top - containerRect.top) / scale + container.scrollTop;
        var bottom = top + clipRect.height / scale;

        var intersects = left < maxX && right > minX && top < maxY && bottom > minY;
        if (intersects) {
            selected.push({
                trackId: parseInt(clipEl.getAttribute('data-track-id')),
                clipId: parseFloat(clipEl.getAttribute('data-clip-id'))
            });
        }
    }

    updateClipSelectionVisuals(selected);
}

function onTimelineSelectionMouseUp(e) {
    if (!timelineSelection.active) return;

    timelineSelection.active = false;
    document.removeEventListener('mousemove', onTimelineSelectionMouseMove);
    document.removeEventListener('mouseup', onTimelineSelectionMouseUp);

    if (timelineSelection.boxEl && timelineSelection.boxEl.parentNode) {
        timelineSelection.boxEl.parentNode.removeChild(timelineSelection.boxEl);
    }

    if (timelineSelection.didDrag) {
        var selected = [];
        var clipEls = document.querySelectorAll('.timeline-clip.selected');
        for (var i = 0; i < clipEls.length; i++) {
            selected.push({
                trackId: parseInt(clipEls[i].getAttribute('data-track-id')),
                clipId: parseFloat(clipEls[i].getAttribute('data-clip-id'))
            });
        }

        var primary = null;
        if (state.selectedClip && state.selectedClip.clipId !== null) {
            for (var j = 0; j < selected.length; j++) {
                if (selected[j].trackId === state.selectedClip.trackId && selected[j].clipId === state.selectedClip.clipId) {
                    primary = selected[j];
                    break;
                }
            }
        }
        if (!primary && selected.length > 0) primary = selected[0];

        applyClipSelection(selected, primary);
        timelineSelection.suppressClick = true;
    }
}

function collectSelectedClips() {
    if (selectedClips.length > 0) return selectedClips.slice();
    if (state.selectedClip && state.selectedClip.clipId !== null) {
        return [{ trackId: state.selectedClip.trackId, clipId: state.selectedClip.clipId }];
    }
    return [];
}

function copySelectedClips() {
    var list = collectSelectedClips();
    if (list.length === 0) {
        consoleLog('No clip selected to copy');
        return false;
    }

    var clipData = [];
    var minBeat = Infinity;
    var minTrack = Infinity;

    for (var i = 0; i < list.length; i++) {
        var clip = findClipById(list[i].trackId, list[i].clipId);
        if (!clip) continue;
        clipData.push({
            trackId: list[i].trackId,
            patternId: clip.patternId,
            startBeat: clip.startBeat,
            loopCount: clip.loopCount,
            offset: clip.offset || 0,
            loopLength: clip.loopLength,
            isExpanded: clip.isExpanded || false,
            trimOffset: clip.trimOffset,
            trimLoopLength: clip.trimLoopLength,
            trimLoopCount: clip.trimLoopCount
        });
        if (clip.startBeat < minBeat) minBeat = clip.startBeat;
        if (list[i].trackId < minTrack) minTrack = list[i].trackId;
    }

    if (clipData.length === 0) {
        consoleLog('No clip selected to copy');
        return false;
    }

    clipboardClips = {
        clips: clipData,
        minBeat: minBeat,
        minTrack: minTrack
    };

    clipboardClip = null;
    if (clipData.length === 1) {
        clipboardClip = JSON.parse(JSON.stringify(clipData[0]));
        clipboardClip.sourceTrackId = clipData[0].trackId;
    }

    clipboard.type = null;
    clipboard.data = null;
    consoleLog('Copied ' + clipData.length + ' clip(s)');
    return true;
}

// Copy selected clip(s) to clipboard
function copyClip() {
    copySelectedClips();
}

// Cut selected clip(s) (copy and delete)
function cutClip() {
    var list = collectSelectedClips();
    if (list.length === 0) {
        consoleLog('No clip selected to cut');
        return;
    }

    pushUndo('clip-edit', captureStateForUndo('clip-edit'));
    if (!copySelectedClips()) return;

    for (var i = 0; i < list.length; i++) {
        removeClipFromTrack(list[i].trackId, list[i].clipId);
    }

    applyClipSelection([], null);
    cleanupUnusedPatterns();
    renderTimeline();
    consoleLog('Cut ' + list.length + ' clip(s)');
}

function pasteClips(targetTrackId, targetBeat) {
    if (clipboardClips && clipboardClips.clips && clipboardClips.clips.length > 0) {
        var baseTrack = targetTrackId !== undefined ? targetTrackId : state.selectedTrack;
        var baseBeat = targetBeat !== undefined ? targetBeat : (state.currentBeat || 0);

        if (state.timeline.snapToMeasure) {
            baseBeat = snapToMeasureStart(baseBeat);
        }

        var newSelections = [];
        for (var i = 0; i < clipboardClips.clips.length; i++) {
            var c = clipboardClips.clips[i];
            var destTrack = baseTrack + (c.trackId - clipboardClips.minTrack);
            if (destTrack < 0) continue;
            while (destTrack >= state.tracks.length) {
                addTrack();
            }

            var newClip = {
                id: Date.now() + Math.random(),
                patternId: c.patternId,
                startBeat: baseBeat + (c.startBeat - clipboardClips.minBeat),
                loopCount: c.loopCount,
                offset: c.offset || 0,
                loopLength: c.loopLength,
                isExpanded: c.isExpanded || false,
                trimOffset: c.trimOffset,
                trimLoopLength: c.trimLoopLength,
                trimLoopCount: c.trimLoopCount
            };

            state.tracks[destTrack].clips.push(newClip);
            newSelections.push({ trackId: destTrack, clipId: newClip.id });
        }

        autoExtendTimeline();
        renderTimeline();
        if (newSelections.length > 0) {
            applyClipSelection(newSelections, newSelections[0]);
        }
        consoleLog('Pasted ' + newSelections.length + ' clip(s)');
        return;
    }

    pasteClip(targetTrackId, targetBeat);
}

// Paste single clip at current position
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
        loopCount: clipboardClip.loopCount,
        offset: clipboardClip.offset || 0,
        loopLength: clipboardClip.loopLength,
        isExpanded: clipboardClip.isExpanded || false,
        trimOffset: clipboardClip.trimOffset,
        trimLoopLength: clipboardClip.trimLoopLength,
        trimLoopCount: clipboardClip.trimLoopCount
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

    var deltaX = getScaledClientX(e) - clipDragState.startX;
    var deltaBeat = deltaX / timelinePixelsPerBeat;

    // Handle end marker dragging (snapped to measures)
    if (clipDragState.mode === 'end-marker') {
        var newTotalBeats = Math.max(16, Math.round(clipDragState.startTotalBeats + deltaBeat));

        // Snap to measure boundary
        newTotalBeats = snapToMeasureEnd(newTotalBeats);

        // Ensure it's beyond the furthest clip (at least 1 measure)
        var minBeats = Math.max(getBeatsPerMeasure(), snapToMeasureEnd(getMaxClipEndBeat()));
        newTotalBeats = Math.max(minBeats, newTotalBeats);

        state.timeline.totalBeats = newTotalBeats;
        state.timeline.totalMeasures = beatsToMeasures(newTotalBeats);
        clipDragState.clipElement.style.left = (newTotalBeats * timelinePixelsPerBeat) + 'px';
        var container = document.getElementById('timeline-tracks');
        if (container) {
            var content = container.querySelector('.timeline-content');
            if (content) {
                var totalWidth = newTotalBeats * timelinePixelsPerBeat;
                content.style.width = totalWidth + 'px';
                content.style.minWidth = totalWidth + 'px';
            }
        }
        var ruler = document.getElementById('timeline-ruler');
        if (ruler) {
            var rulerWidth = newTotalBeats * timelinePixelsPerBeat;
            ruler.style.width = rulerWidth + 'px';
            ruler.style.minWidth = rulerWidth + 'px';
        }
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

    if (clipDragState.mode === 'move') {
        var targetTrackId = getTimelineTrackIdAt(e.clientY);
        if (targetTrackId !== null && targetTrackId !== clipDragState.currentTrackId) {
            var moved = moveClipToTrack(clipDragState.clipId, clipDragState.currentTrackId, targetTrackId);
            if (moved) {
                clipDragState.currentTrackId = targetTrackId;
                clipDragState.trackId = targetTrackId;
                if (clipDragState.clipElement) {
                    clipDragState.clipElement.setAttribute('data-track-id', targetTrackId);
                    var targetRow = document.querySelector('.timeline-track-row[data-track-id="' + targetTrackId + '"]');
                    if (targetRow && clipDragState.clipElement.parentNode !== targetRow) {
                        targetRow.appendChild(clipDragState.clipElement);
                    }
                }
            }
        }
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

    if (clipDragState.mode === 'expand-handle') {
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        var lpb = pattern.lpb || state.lpb;
        var grid = 1 / lpb;
        var newBeats = clipDragState.startPatternBeats + deltaBeat;
        newBeats = Math.max(grid, Math.round(newBeats / grid) * grid);

        if (Math.abs(newBeats - clipDragState.lastPatternBeats) < 0.0001) return;

        clipDragState.didDrag = true;
        clipDragState.lastPatternBeats = newBeats;

        var changed = applyPatternLengthWithBuffer(pattern, clip, newBeats);
        if (!changed) return;

        var duration = getClipDurationBeats(clip);
        if (clipDragState.clipElement) {
            var widthPx = Math.max(duration * timelinePixelsPerBeat - 2, 2);
            clipDragState.clipElement.style.width = widthPx + 'px';
            var noteCanvas = clipDragState.clipElement.querySelector('.clip-note-viz');
            if (noteCanvas) {
                noteCanvas.width = Math.max(widthPx, 1);
                renderClipNotes(noteCanvas, pattern, clip);
            }
            var expandHandle = clipDragState.clipElement.querySelector('.clip-expand-handle');
            if (expandHandle) {
                var expandInfo = getClipExpandInfo(clip, pattern);
                expandHandle.textContent = expandInfo.hasBuffer ? '+' : '\u2194';
                if (expandInfo.expanded) {
                    clipDragState.clipElement.classList.add('expanded');
                } else {
                    clipDragState.clipElement.classList.remove('expanded');
                }
            }
        }

        autoExtendTimeline();
        return;
    }

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
        var patternBeats = getPatternBeatsValue(pattern);
        var loopLength = getClipLoopLength(clip, pattern);

        // Calculate new loop count based on drag distance
        var loopsChange = deltaBeat / (loopLength || patternBeats);
        var newLoopCount = Math.max(1, Math.round(clipDragState.startLoopCount + loopsChange));

        clip.loopCount = newLoopCount;
        if (clip.loopLength === undefined || clip.loopLength === null) {
            clip.loopLength = loopLength || patternBeats;
        }

        // Update visual width
        var duration = getClipDurationBeats(clip);
        clipDragState.clipElement.style.width = (duration * timelinePixelsPerBeat - 2) + 'px';

        // Update label in header
        var label = pattern.name || ('Pattern ' + (clip.patternId + 1));
        if (newLoopCount > 1) {
            label += ' \u00D7' + newLoopCount;
        }
        var header = clipDragState.clipElement.querySelector('.clip-header');
        if (header) {
            header.textContent = label;
        }

        // Auto-extend timeline if clip resized beyond bounds
        autoExtendTimeline();
    } else if (clipDragState.mode === 'loop-handle') {
        // Resize clip to whole loop units (pattern-length snapping)
        var pattern = state.patterns[clip.patternId];
        if (!pattern) return;

        var patternBeats = getPatternBeatsValue(pattern);
        var loopLength = getClipLoopLength(clip, pattern);
        var baseSnap = loopLength || patternBeats;
        if (!baseSnap || baseSnap <= 0) baseSnap = state.timeline.gridSnap || 1;

        // Calculate new total duration snapped to grid
        var oldDuration = (loopLength || patternBeats) * clipDragState.startLoopCount;
        var newDuration = oldDuration + deltaBeat;
        // Snap duration to pattern length so loops repeat only full pattern steps
        newDuration = Math.max(baseSnap, Math.round(newDuration / baseSnap) * baseSnap);
        // Convert back to loopCount (accounting for offset)
        var newLoopCount = newDuration / (loopLength || patternBeats);
        // Minimum: at least one full loop
        newLoopCount = Math.max(1, newLoopCount);

        clip.loopCount = newLoopCount;
        if (clip.loopLength === undefined || clip.loopLength === null) {
            clip.loopLength = loopLength || patternBeats;
        }

        // Update visual width
        var duration = getClipDurationBeats(clip);
        clipDragState.clipElement.style.width = (duration * timelinePixelsPerBeat - 2) + 'px';

        // Update label in header
        var label = pattern.name || ('Pattern ' + (clip.patternId + 1));
        if (newLoopCount > 1) {
            var displayLoops = Math.round(newLoopCount * 100) / 100;
            label += ' \u00D7' + displayLoops;
        }
        var header = clipDragState.clipElement.querySelector('.clip-header');
        if (header) {
            header.textContent = label;
        }

        autoExtendTimeline();
    }
}

function handleTimelineMouseUp(e) {
    if (clipDragState.active) {
        var wasExpand = clipDragState.mode === 'expand-handle';
        var expandTrackId = clipDragState.trackId;
        var expandClipId = clipDragState.clipId;
        var expandDidDrag = clipDragState.didDrag;
        clipDragState.active = false;
        clipDragState.mode = null;
        clipDragState.clipId = null;
        clipDragState.trackId = null;
        clipDragState.currentTrackId = null;
        clipDragState.clipElement = null;
        clipDragState.didDrag = false;
        document.body.style.cursor = '';
        renderTimeline();  // Re-render to ensure proper state

        if (wasExpand) {
            clipDragState.suppressClick = expandDidDrag;
            var expandClip = findClipById(expandTrackId, expandClipId);
            var expandPattern = expandClip ? state.patterns[expandClip.patternId] : null;
            if (expandPattern && expandPattern._needsGridRefresh) {
                var patternIndex = getPatternIndex(expandPattern);
                invalidatePatternCache(patternIndex);
                expandPattern._needsGridRefresh = false;
            }
            if (state.selectedClip &&
                state.selectedClip.clipId === expandClipId &&
                state.selectedClip.trackId === expandTrackId) {
                setPrimaryClip(expandTrackId, expandClipId);
            }
        } else {
            clipDragState.suppressClick = false;
        }
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
        var scale = getUiScale();
        var container = document.getElementById('timeline-tracks');
        var scrollX = container ? container.scrollLeft : 0;
        var x = (e.clientX - rect.left) / scale + scrollX;
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
    var clip = findClipById(trackId, clipId);
    if (!clip) return;
    switchEditorView('song');
    setPatternCollapsed(false);
    selectClip(trackId, clipId);
    consoleLog('Editing pattern ' + (clip.patternId + 1) + ' from track ' + (trackId + 1));
}

function getContextClipSelection() {
    if (timelineContextState.clipId === null) return [];
    if (selectedClips.length > 0) {
        for (var i = 0; i < selectedClips.length; i++) {
            if (selectedClips[i].trackId === timelineContextState.trackId &&
                selectedClips[i].clipId === timelineContextState.clipId) {
                return selectedClips.slice();
            }
        }
    }
    return [{ trackId: timelineContextState.trackId, clipId: timelineContextState.clipId }];
}

function clonePatternFromPattern(pattern, trackId) {
    var cloned = JSON.parse(JSON.stringify(pattern));
    cloned.id = state.patterns.length;
    cloned.trackId = trackId || 0;
    var baseName = pattern.name || (pattern.type === 'piano' ? 'Piano' : 'Pattern');
    cloned.name = baseName + ' (unique)';
    state.patterns.push(cloned);
    return cloned.id;
}

function makeSelectedClipsUnique() {
    var clips = getContextClipSelection();
    if (clips.length === 0) {
        consoleLog('No clip selected');
        return;
    }

    for (var i = 0; i < clips.length; i++) {
        var clip = findClipById(clips[i].trackId, clips[i].clipId);
        if (!clip) continue;
        var pattern = state.patterns[clip.patternId];
        if (!pattern) continue;
        var newPatternId = clonePatternFromPattern(pattern, clips[i].trackId);
        clip.patternId = newPatternId;
    }

    renderTimeline();
    if (state.selectedClip && state.selectedClip.clipId !== null) {
        setPrimaryClip(state.selectedClip.trackId, state.selectedClip.clipId);
    }
    consoleLog('Made pattern unique');
}

function fxHexToFloatValue(fxStr) {
    if (!fxStr || fxStr === '--' || fxStr === '----') return 0;
    var val = parseInt(fxStr, 16);
    if (isNaN(val)) return 0;
    return val / 65535;
}

function fxFloatToHexValue(val) {
    if (typeof val !== 'number' || !isFinite(val)) return '0000';
    var clamped = Math.max(0, Math.min(1, val));
    return Math.round(clamped * 65535).toString(16).toUpperCase().padStart(4, '0');
}

function convertTrackerPatternToPiano(pattern) {
    if (!pattern) return;
    if (pattern.data && (!pattern.notes || pattern.notes.length === 0)) {
        pattern.notes = trackerDataToNotes(pattern);
    }

    var lpb = pattern.lpb || state.lpb;
    var beats = (pattern.steps || 16) / lpb;
    var events = pattern.notes || [];
    var notes = [];

    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if (!isNoteEvent(ev)) continue;
        var startBeat = Math.max(0, Math.min(beats, ev.startBeat || 0));

        var endBeat = null;
        for (var j = 0; j < events.length; j++) {
            if (i === j) continue;
            var other = events[j];
            if (!other || (other.column || 0) !== (ev.column || 0)) continue;
            if (other.startBeat <= startBeat) continue;
            if (isNoteEvent(other) || (isCellEvent(other) && other.note === NOTE_OFF)) {
                if (endBeat === null || other.startBeat < endBeat) {
                    endBeat = other.startBeat;
                }
            }
        }

        var duration = null;
        if (endBeat === null || endBeat <= startBeat) {
            duration = 1 / lpb;
        } else {
            duration = Math.max(1 / lpb, Math.min(beats - startBeat, endBeat - startBeat));
        }

        var fxArr = [];
        if (ev.fx && ev.fx.length) {
            for (var fx = 0; fx < ev.fx.length; fx++) {
                fxArr.push(fxHexToFloatValue(ev.fx[fx]));
            }
        }

        notes.push({
            type: 'note',
            pitch: ev.pitch,
            startBeat: startBeat,
            duration: duration,
            velocity: ev.velocity,
            column: ev.column || 0,
            fx: fxArr
        });
    }

    pattern.type = 'piano';
    pattern.beats = beats;
    pattern.steps = Math.round(beats * lpb);
    pattern.noteColumns = 1;
    pattern.fxColumns = [0];
    pattern.notes = notes;
    pattern._bufferNotes = undefined;
    pattern._bufferBeats = undefined;
}

function convertPianoPatternToTracker(pattern) {
    if (!pattern) return;
    var lpb = pattern.lpb || state.lpb;
    var beats = pattern.beats || 4;
    var steps = Math.max(1, Math.round(beats * lpb));
    var grid = 1 / lpb;

    var notes = pattern.notes || [];
    var events = [];
    var maxFx = 0;
    var maxCol = 0;

    for (var i = 0; i < notes.length; i++) {
        var note = notes[i];
        if (!isNoteEvent(note)) continue;

        var startBeat = Math.max(0, Math.round(note.startBeat / grid) * grid);
        var duration = (typeof note.duration === 'number' && note.duration > 0) ? note.duration : grid;
        var endBeat = Math.round((startBeat + duration) / grid) * grid;
        if (endBeat <= startBeat) endBeat = startBeat + grid;
        if (endBeat > beats) endBeat = beats;
        var col = note.column || 0;
        if (col > maxCol) maxCol = col;

        var fxArr = [];
        if (note.fx && note.fx.length) {
            for (var fx = 0; fx < note.fx.length; fx++) {
                var fxVal = note.fx[fx];
                if (typeof fxVal === 'number') {
                    fxArr.push(fxFloatToHexValue(fxVal));
                } else if (typeof fxVal === 'string' && fxVal !== '' && fxVal !== '--' && fxVal !== '----') {
                    fxArr.push(fxVal.toString().toUpperCase().padStart(4, '0'));
                }
            }
        }
        maxFx = Math.max(maxFx, fxArr.length);

        events.push({
            type: 'note',
            pitch: note.pitch,
            startBeat: startBeat,
            duration: null,
            velocity: note.velocity,
            column: col,
            fx: fxArr
        });

        if (endBeat < beats - 0.0001) {
            events.push({
                type: 'cell',
                startBeat: endBeat,
                column: col,
                note: NOTE_OFF,
                amp: '',
                fx: []
            });
        }
    }

    pattern.type = 'tracker';
    pattern.steps = steps;
    pattern.beats = steps / lpb;
    pattern.noteColumns = maxCol + 1;
    pattern.fxColumns = [];
    for (var c = 0; c < pattern.noteColumns; c++) {
        pattern.fxColumns.push(maxFx);
    }
    pattern.notes = events;
    pattern._bufferNotes = undefined;
    pattern._bufferBeats = undefined;
    notesToTrackerData(pattern);
}

function convertSelectedClipPattern() {
    var clips = getContextClipSelection();
    if (clips.length === 0) {
        consoleLog('No clip selected');
        return;
    }

    var primary = clips[0];
    var clip = findClipById(primary.trackId, primary.clipId);
    if (!clip) return;
    var pattern = state.patterns[clip.patternId];
    if (!pattern) return;

    var oldBeats = getPatternBeatsValue(pattern);
    if (pattern.type === 'piano') {
        convertPianoPatternToTracker(pattern);
    } else {
        convertTrackerPatternToPiano(pattern);
    }
    var newBeats = getPatternBeatsValue(pattern);
    if (clip.loopLength === undefined || clip.loopLength === null || Math.abs(clip.loopLength - oldBeats) < 0.0001) {
        clip.loopLength = newBeats;
    }

    renderTimeline();
    setPrimaryClip(primary.trackId, primary.clipId);
    consoleLog('Converted pattern type');
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
    deleteSelectedClips();
}

function deleteSelectedClips() {
    var list = collectSelectedClips();
    if (list.length === 0) {
        consoleLog('No clip selected');
        return;
    }

    pushUndo('clip-edit', captureStateForUndo('clip-edit'));

    for (var i = 0; i < list.length; i++) {
        removeClipFromTrack(list[i].trackId, list[i].clipId);
    }

    applyClipSelection([], null);
    cleanupUnusedPatterns();
    currentGridPatternIndex = -1;
    renderTimeline();
    renderTrackList();
    renderTrackerGrid(true);
    consoleLog('Deleted ' + list.length + ' clip(s)');
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
    var oldLpb = pattern.lpb || state.lpb;
    var oldBeats = (oldSteps || 0) / (oldLpb || state.lpb);
    var ratio = (oldLpb && newLpb) ? (oldLpb / newLpb) : 1;

    // Update LPB
    pattern.lpb = newLpb;

    // Update steps if changed
    if (newSteps !== oldSteps) {
        pattern.steps = newSteps;
    }

    if (Math.abs(ratio - 1) >= 0.000001) {
        scaleEventsByRatio(pattern.notes, ratio);
        if (pattern._bufferNotes) {
            scaleEventsByRatio(pattern._bufferNotes, ratio);
        }
        if (pattern._bufferBeats !== undefined && pattern._bufferBeats !== null) {
            pattern._bufferBeats *= ratio;
        }

        for (var ti = 0; ti < state.tracks.length; ti++) {
            var clips = state.tracks[ti].clips;
            for (var ci = 0; ci < clips.length; ci++) {
                var clip = clips[ci];
                if (clip.patternId !== patternIndex) continue;
                if (typeof clip.offset === 'number') clip.offset *= ratio;
                if (clip.loopLength !== undefined && clip.loopLength !== null) clip.loopLength *= ratio;
                if (clip.trimOffset !== undefined && clip.trimOffset !== null) clip.trimOffset *= ratio;
                if (clip.trimLoopLength !== undefined && clip.trimLoopLength !== null) clip.trimLoopLength *= ratio;
            }
        }
    }

    // Update beats derived from steps/lpb (tracker patterns)
    pattern.beats = pattern.steps / (pattern.lpb || state.lpb);
    var newBeats = pattern.beats;

    // Keep clip loop length in sync with pattern length unless explicitly trimmed
    for (var ti2 = 0; ti2 < state.tracks.length; ti2++) {
        var clips2 = state.tracks[ti2].clips;
        for (var ci2 = 0; ci2 < clips2.length; ci2++) {
            var clip2 = clips2[ci2];
            if (clip2.patternId !== patternIndex) continue;
            if (clip2.loopLength === undefined || clip2.loopLength === null ||
                Math.abs(clip2.loopLength - oldBeats) < 0.0001) {
                clip2.loopLength = newBeats;
            }
            if (typeof clip2.offset === 'number' && newBeats > 0) {
                clip2.offset = clip2.offset % newBeats;
            }
        }
    }

    if (Math.abs(ratio - 1) >= 0.000001) {
        var maxBeats = pattern.beats;
        for (var tj = 0; tj < state.tracks.length; tj++) {
            var tclips = state.tracks[tj].clips;
            for (var cj = 0; cj < tclips.length; cj++) {
                var c = tclips[cj];
                if (c.patternId !== patternIndex) continue;
                if (typeof c.offset === 'number' && maxBeats > 0) {
                    c.offset = c.offset % maxBeats;
                }
            }
        }
    }

    // Trim events beyond new length
    if (pattern.notes && pattern.notes.length > 0) {
        var maxBeat = pattern.beats;
        pattern.notes = pattern.notes.filter(function(ev) {
            return ev && ev.startBeat < maxBeat + 0.0001;
        });
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

    markPatternNoteVizDirty(patternIndex);
}

var patternNoteVizDirty = {};
var pendingNoteVizRefresh = null;

function getPatternIndex(pattern) {
    if (!pattern) return -1;
    return state.patterns.indexOf(pattern);
}

function markPatternNoteVizDirty(patternIndex) {
    if (patternIndex === null || patternIndex === undefined || patternIndex < 0) return;
    patternNoteVizDirty[patternIndex] = true;
    scheduleNoteVizRefresh();
}

function markPatternNoteVizDirtyForPattern(pattern) {
    var idx = getPatternIndex(pattern);
    if (idx >= 0) {
        markPatternNoteVizDirty(idx);
    }
}

function scheduleNoteVizRefresh() {
    if (state.isPlaying) return;
    if (pendingNoteVizRefresh) return;
    pendingNoteVizRefresh = requestAnimationFrame(function() {
        pendingNoteVizRefresh = null;
        flushPatternNoteVizDirty();
    });
}

function refreshClipNoteVizForPattern(patternIndex) {
    var pattern = state.patterns[patternIndex];
    if (!pattern) return;

    var clipEls = document.querySelectorAll('.timeline-clip[data-pattern-id="' + patternIndex + '"]');
    for (var i = 0; i < clipEls.length; i++) {
        var clipEl = clipEls[i];
        var trackId = parseInt(clipEl.getAttribute('data-track-id'));
        var clipId = parseFloat(clipEl.getAttribute('data-clip-id'));
        var clip = findClipById(trackId, clipId);
        var canvas = clipEl.querySelector('.clip-note-viz');
        if (canvas && clip) {
            renderClipNotes(canvas, pattern, clip);
        }
    }
}

function flushPatternNoteVizDirty() {
    var keys = Object.keys(patternNoteVizDirty);
    if (keys.length === 0) return;

    for (var i = 0; i < keys.length; i++) {
        var idx = parseInt(keys[i]);
        if (!isNaN(idx)) {
            refreshClipNoteVizForPattern(idx);
        }
    }

    patternNoteVizDirty = {};
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

        // Per-note-column FX +/- buttons
        var fxBtns = document.createElement('div');
        fxBtns.className = 'fx-col-controls';
        fxBtns.innerHTML =
            '<button class="btn-fx-minus" data-pattern="' + patternIndex + '" data-note-col="' + nc + '" title="Remove p-field">-p</button>' +
            '<button class="btn-fx-plus" data-pattern="' + patternIndex + '" data-note-col="' + nc + '" title="Add p-field">+p</button>';

        // Labels row for this note column (Note/Vel + FX labels)
        var labelsInner = document.createElement('div');
        labelsInner.className = 'note-column-labels';
        labelsInner.innerHTML = '<div class="cell note-label">Note</div>' +
                                '<div class="cell amp-label">Vel</div>';

        // FX column labels for this note column (p6, p7, p8, etc.)
        var fxCount = getFxCount(pattern, nc);
        for (var fx = 0; fx < fxCount; fx++) {
            var fxLabel = document.createElement('div');
            fxLabel.className = 'cell fx-label';
            fxLabel.textContent = 'p' + (6 + fx);
            labelsInner.appendChild(fxLabel);
        }

        noteColLabels.appendChild(fxBtns);
        noteColLabels.appendChild(labelsInner);

        labelsRow.appendChild(noteColLabels);
    }

    rows.appendChild(labelsRow);

    // Ensure pattern has notes array (convert legacy data if needed)
    if (!pattern.notes || pattern.notes.length === 0) {
        pattern.notes = pattern.data ? trackerDataToNotes(pattern) : [];
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
// Uses unified notes array - derives display from getNoteAtStep
function createDataRowSingle(step, pattern) {
    var row = document.createElement('div');
    row.className = 'track-row';
    row.setAttribute('data-step', step);

    // Row number
    var rowNum = document.createElement('div');
    rowNum.className = 'row-number';
    rowNum.textContent = step.toString().padStart(3, '0');
    row.appendChild(rowNum);

    var numNoteCols = pattern.noteColumns || 1;

    // Render each note column from unified events
    for (var nc = 0; nc < numNoteCols; nc++) {
        var cellData = getTrackerCellDisplay(pattern, step, nc);
        var noteName = cellData.noteName;
        var ampStr = cellData.ampStr;
        var fxArr = cellData.fxArr;

        var noteColEl = document.createElement('div');
        noteColEl.className = 'note-column-group';
        noteColEl.setAttribute('data-note-col', nc);

        // Note cell
        var noteCell = document.createElement('div');
        noteCell.className = 'cell note';
        noteCell.setAttribute('data-step', step);
        noteCell.setAttribute('data-note-col', nc);
        noteCell.setAttribute('data-type', 'note');
        noteCell.textContent = noteName || '---';
        if (noteName === NOTE_OFF) {
            noteCell.classList.add('note-off');
        }
        noteColEl.appendChild(noteCell);

        // Amp cell
        var ampCell = document.createElement('div');
        ampCell.className = 'cell amp';
        ampCell.setAttribute('data-step', step);
        ampCell.setAttribute('data-note-col', nc);
        ampCell.setAttribute('data-type', 'amp');
        ampCell.textContent = ampStr || '--';
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

            var fxVal = fxArr[fx];
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
        if (!state.isPlaying) {
            flushPatternNoteVizDirty();
        }
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

    if (!state.isPlaying) {
        flushPatternNoteVizDirty();
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
    uiFocus = 'tracker';

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
    uiFocus = 'tracker';
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
    var isCodeEditor = e.target && (e.target.id === 'code-editor' || e.target.id === 'opcodes-editor');
    if (isCodeEditor && e.altKey && (e.code === 'KeyC' || e.key === 'c' || e.key === 'C')) {
        e.preventDefault();
        e.stopPropagation();
        if (e.target.id === 'code-editor') {
            compileCurrentInstrumentIfChanged();
        } else {
            saveOpcodes();
            compileOpcodesIfChanged();
        }
        return;
    }

    // Skip if in textarea or other input (except our edit input)
    if (e.target.tagName === 'TEXTAREA') return;
    if (e.target.tagName === 'INPUT' && e.target !== editInput) return;

    // If editing, let the edit input handle it
    if (editingCell && e.target === editInput) return;

    // Undo/Redo (Ctrl+Z / Ctrl+Y)
    if (e.ctrlKey && (e.key === 'z' || e.key === 'Z') && !e.shiftKey) {
        e.preventDefault();
        undo();
        return;
    }
    if (e.ctrlKey && (e.key === 'y' || e.key === 'Y')) {
        e.preventDefault();
        redo();
        return;
    }

    // Cut/Copy/Paste (Ctrl+X/C/V)
    if (e.ctrlKey && (e.key === 'x' || e.key === 'X')) {
        e.preventDefault();
        cutSelection();
        return;
    }
    if (e.ctrlKey && (e.key === 'c' || e.key === 'C')) {
        e.preventDefault();
        copySelection();
        return;
    }
    if (e.ctrlKey && (e.key === 'v' || e.key === 'V')) {
        e.preventDefault();
        pasteSelection();
        return;
    }

    // Select All (Ctrl+A)
    if (e.ctrlKey && (e.key === 'a' || e.key === 'A')) {
        e.preventDefault();
        selectAll();
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

    // Timeline delete (Delete/Backspace)
    if (uiFocus === 'timeline' && (e.key === 'Delete' || e.key === 'Backspace')) {
        e.preventDefault();
        deleteSelectedClips();
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
            pasteSelection();
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
            var pattern = getCurrentPattern();
            if (pattern && pattern.type === 'piano' && uiFocus === 'piano') {
                var semitone = keyboardMap[key];
                var pitch = (state.baseOctave + 1) * 12 + semitone;
                startPianoRollRecordNote(pitch, 100);
            } else {
                var semitone = keyboardMap[key];
                var noteName = semitoneToNoteName(semitone, state.baseOctave);
                recordNote(noteName);
            }
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
        var pattern = getCurrentPattern();
        if (state.isRecording && pattern && pattern.type === 'piano' && uiFocus === 'piano') {
            var semitone = keyboardMap[key];
            var pitch = (state.baseOctave + 1) * 12 + semitone;
            finishPianoRollRecordNote(pitch);
        }
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
    if (!pattern) return;

    var info = findTrackerEventsAtStep(pattern, step, noteCol);
    var noteEvent = info.noteEvent;
    var cellEvent = info.cellEvent;
    var stepBeat = info.stepBeat;
    var events = ensurePatternNotes(pattern);

    function ensureCellEvent() {
        if (!cellEvent) {
            cellEvent = { type: 'cell', startBeat: stepBeat, column: noteCol, note: '', amp: '', fx: [] };
            events.push(cellEvent);
        }
    }

    function cleanupCellEvent() {
        if (!cellEvent) return;
        var hasAmp = cellEvent.amp && cellEvent.amp !== '--';
        var hasFx = hasFxValues(cellEvent.fx);
        var hasNote = cellEvent.note && cellEvent.note !== '';
        if (!hasAmp && !hasFx && !hasNote) {
            removeEvent(events, cellEvent);
            cellEvent = null;
        }
    }

    if (type === 'note') {
        if (!value || value === '---') {
            // Clear note, preserve amp/fx in a cell event if present
            if (noteEvent) {
                var ampHex = velocityToHex(noteEvent.velocity);
                var fxCopy = noteEvent.fx ? noteEvent.fx.slice() : [];
                if ((ampHex && ampHex !== '--') || hasFxValues(fxCopy)) {
                    ensureCellEvent();
                    if (ampHex && ampHex !== '--') cellEvent.amp = ampHex;
                    if (hasFxValues(fxCopy)) cellEvent.fx = fxCopy;
                }
                removeEvent(events, noteEvent);
                noteEvent = null;
            }
            if (cellEvent && cellEvent.note === NOTE_OFF) {
                cellEvent.note = '';
                cleanupCellEvent();
            }
        } else if (value === NOTE_OFF) {
            // Note-off cell
            if (noteEvent) {
                var ampHex = velocityToHex(noteEvent.velocity);
                var fxCopy = noteEvent.fx ? noteEvent.fx.slice() : [];
                ensureCellEvent();
                if (ampHex && ampHex !== '--') cellEvent.amp = ampHex;
                if (hasFxValues(fxCopy)) cellEvent.fx = fxCopy;
                removeEvent(events, noteEvent);
                noteEvent = null;
            }
            ensureCellEvent();
            cellEvent.note = NOTE_OFF;
        } else {
            // Normal note
            var pitch = noteNameToMidi(value);
            if (pitch === null) return;

            if (!noteEvent) {
                noteEvent = {
                    type: 'note',
                    pitch: pitch,
                    startBeat: stepBeat,
                    duration: null,
                    velocity: null,
                    column: noteCol,
                    fx: []
                };
                events.push(noteEvent);
            } else {
                noteEvent.pitch = pitch;
            }

            // Transfer amp/fx from cell event if present
            if (cellEvent) {
                if (cellEvent.amp && cellEvent.amp !== '--') {
                    noteEvent.velocity = hexToVelocity(cellEvent.amp);
                }
                if (cellEvent.fx && cellEvent.fx.length > 0) {
                    noteEvent.fx = cellEvent.fx.slice();
                }
                if (cellEvent.note === NOTE_OFF) cellEvent.note = '';
                cellEvent.amp = '';
                cellEvent.fx = [];
                cleanupCellEvent();
            }
        }
    } else if (type === 'amp') {
        if (noteEvent) {
            noteEvent.velocity = value ? hexToVelocity(value) : null;
        } else {
            if (!value) {
                if (cellEvent) {
                    cellEvent.amp = '';
                    cleanupCellEvent();
                }
            } else {
                ensureCellEvent();
                cellEvent.amp = value;
            }
        }
    } else if (type === 'fx') {
        if (noteEvent) {
            if (!noteEvent.fx) noteEvent.fx = [];
            while (noteEvent.fx.length <= fxCol) {
                noteEvent.fx.push('');
            }
            noteEvent.fx[fxCol] = value || '';
            trimFxArray(noteEvent.fx);
        } else {
            if (!value) {
                if (cellEvent && cellEvent.fx) {
                    cellEvent.fx[fxCol] = '';
                    trimFxArray(cellEvent.fx);
                    cleanupCellEvent();
                }
            } else {
                ensureCellEvent();
                if (!cellEvent.fx) cellEvent.fx = [];
                while (cellEvent.fx.length <= fxCol) {
                    cellEvent.fx.push('');
                }
                cellEvent.fx[fxCol] = value;
                trimFxArray(cellEvent.fx);
            }
        }
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

    contextMenu.classList.add('visible');
    positionMenuAtClient(contextMenu, x, y);
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

    if (!pattern) {
        consoleLog('No pattern selected');
        return;
    }

    // Get all selected FX cells sorted by step
    var fxCells = [];
    for (var i = 0; i < selectedCells.length; i++) {
        var info = getCellInfo(selectedCells[i]);
        if (info && info.type === 'fx') {
            var fxStr = getTrackerFxValue(pattern, info.step, info.noteCol, info.col);
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

            // Set the value in the unified events
            var hexValue = interpolatedValue.toString(16).toUpperCase().padStart(4, '0');
            setCellValue(cell.info.step, cell.info.noteCol, cell.info.col, 'fx', hexValue);
            updateCellDisplay(cell.cell, 'fx', hexValue);
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

    for (var i = 0; i < notes.length; i++) {
        setCellValue(step, i, 0, 'note', notes[i]);
        var info = findTrackerEventsAtStep(pattern, step, i);
        if (info.noteEvent && (info.noteEvent.velocity === null || info.noteEvent.velocity === undefined)) {
            setCellValue(step, i, 0, 'amp', 'FF');
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
            if (noteCell) updateCellDisplay(noteCell, 'note', notes[i]);
            if (ampCell) {
                var ampVal = '';
                var info = findTrackerEventsAtStep(pattern, step, i);
                if (info.noteEvent && info.noteEvent.velocity !== null && info.noteEvent.velocity !== undefined) {
                    ampVal = velocityToHex(info.noteEvent.velocity);
                }
                updateCellDisplay(ampCell, 'amp', ampVal);
            }
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
    if (!pattern || pattern.type === 'piano') return;

    pushUndo('pattern-edit', captureStateForUndo('pattern-edit'));

    for (var i = 0; i < selectedCells.length; i++) {
        var cell = selectedCells[i];
        var info = getCellInfo(cell);
        if (!info) continue;

        if (info.type === 'note') {
            setCellValue(info.step, info.noteCol, 0, 'note', '');
            updateCellDisplay(cell, 'note', '');
        } else if (info.type === 'amp') {
            setCellValue(info.step, info.noteCol, 0, 'amp', '');
            updateCellDisplay(cell, 'amp', '');
        } else if (info.type === 'fx') {
            setCellValue(info.step, info.noteCol, info.col, 'fx', '');
            updateCellDisplay(cell, 'fx', '');
        }
    }

    markPatternDirty(patternIndex);
    consoleLog('Cleared ' + selectedCells.length + ' cell(s)');
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

        // Start non-playback preview timer (updates at ~60fps for smooth 1/16th visualization)
        if (!state.isPlaying) {
            startRecordingPreviewTimer();
        }
    } else {
        btn.classList.remove('recording');
        consoleLog('Recording OFF');
        setStatus('Recording stopped');

        // Stop preview timer and reset preview
        stopRecordingPreviewTimer();
        recordingPreviewBeats = 0;
        lastRecordingPreviewBeats = 0;
        renderTimeline();
    }
}

// Timer for live preview during non-playback recording
function startRecordingPreviewTimer() {
    stopRecordingPreviewTimer();  // Clear any existing timer
    recordingPreviewTimer = setInterval(function() {
        if (!state.isRecording) {
            stopRecordingPreviewTimer();
            return;
        }
        // If playback started, the visualUpdateLoop handles it
        if (state.isPlaying) {
            return;
        }
        updateRecordingPreviewNonPlayback();
    }, 16);  // ~60fps for smooth updates
}

function stopRecordingPreviewTimer() {
    if (recordingPreviewTimer) {
        clearInterval(recordingPreviewTimer);
        recordingPreviewTimer = null;
    }
}

// Update preview when recording without playback (stationary recording)
function updateRecordingPreviewNonPlayback() {
    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') {
        recordingPreviewBeats = 0;
        return;
    }

    var clip = getSelectedClip();
    if (!clip) {
        recordingPreviewBeats = 0;
        return;
    }

    // Check if any notes are currently being held
    var heldNotes = Object.keys(midiNoteStartBeats);
    if (heldNotes.length === 0) {
        if (recordingPreviewBeats !== 0) {
            recordingPreviewBeats = 0;
            renderTimeline();
        }
        return;
    }

    // Calculate expected end beat for each held note based on elapsed time
    var baseBeats = getClipLoopLength(clip, pattern) || (pattern.beats || 0);
    var maxEndBeat = baseBeats;
    var quantizeBeats = pianoRoll.quantize || 0.25;

    for (var i = 0; i < heldNotes.length; i++) {
        var noteInfo = midiNoteStartBeats[heldNotes[i]];
        if (noteInfo && noteInfo.startTime) {
            // Calculate duration from elapsed time
            var elapsedMs = performance.now() - noteInfo.startTime;
            var elapsedBeats = (elapsedMs / 1000) * (state.bpm / 60);
            var endBeat = noteInfo.beat + Math.max(quantizeBeats, Math.ceil(elapsedBeats / quantizeBeats) * quantizeBeats);

            if (endBeat > maxEndBeat) {
                maxEndBeat = endBeat;
            }
        }
    }

    // Set preview to rounded-up value (nearest 4 beats)
    var newPreview = 0;
    if (maxEndBeat > baseBeats) {
        newPreview = Math.ceil(maxEndBeat / 4) * 4;
    }

    // Re-render timeline if preview changed at 1/16th note resolution
    var quantizedPreview = Math.floor(newPreview * 4) / 4;
    var quantizedLast = Math.floor(lastRecordingPreviewBeats * 4) / 4;

    if (quantizedPreview !== quantizedLast) {
        recordingPreviewBeats = newPreview;
        lastRecordingPreviewBeats = newPreview;
    }

    var didExpand = applyRecordingPreviewToClip(pattern, clip);
    if (quantizedPreview !== quantizedLast || didExpand) {
        renderTimeline();
        scheduleRenderPianoRoll();
    }
}

function recordNote(noteName) {
    if (!state.isRecording) return;

    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    var noteCol = state.focusedNoteCol || 0;

    setCellValue(state.focusedStep, noteCol, 0, 'note', noteName);
    setCellValue(state.focusedStep, noteCol, 0, 'amp', 'FF');  // Default velocity (full volume)

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
        // Reset recording preview when playback stops
        recordingPreviewBeats = 0;
        lastRecordingPreviewBeats = 0;
        return;
    }

    flushPatternNoteVizDirty();

    // Update timeline playhead position
    updateTimelinePlayhead();

    // Live expansion preview during recording
    if (state.isRecording) {
        updateRecordingPreview();
    }

    // If a clip is selected, show the current step in that pattern
    if (state.selectedClip && state.selectedClip.trackId !== null && state.selectedClip.clipId !== null) {
        var track = state.tracks[state.selectedClip.trackId];
        if (track) {
            for (var i = 0; i < track.clips.length; i++) {
                if (track.clips[i].id === state.selectedClip.clipId) {
                    var clip = track.clips[i];
                    var pattern = state.patterns[clip.patternId];

                    // Check if current beat is within this clip
                    if (state.currentBeat >= clip.startBeat && state.currentBeat < getClipEndBeat(clip)) {
                        // Update tracker grid playhead for tracker patterns
                        if (!pattern || pattern.type !== 'piano') {
                            var stepInfo = beatToPatternStep(clip, state.currentBeat);
                            if (stepInfo.step !== lastPlayedStep) {
                                updatePlayhead(stepInfo.step);
                                lastPlayedStep = stepInfo.step;
                            }
                        }

                        // Piano roll playhead is disabled; avoid repaint here
                    }
                    break;
                }
            }
        }
    }

    pendingVisualUpdate = requestAnimationFrame(visualUpdateLoop);
}

// Calculate and update live recording preview expansion
function updateRecordingPreview() {
    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') {
        recordingPreviewBeats = 0;
        return;
    }

    var clip = getSelectedClip();
    if (!clip) {
        recordingPreviewBeats = 0;
        return;
    }

    // Check if any notes are currently being held
    var heldNotes = Object.keys(midiNoteStartBeats);
    var baseBeats = getClipLoopLength(clip, pattern) || (pattern.beats || 0);
    if (heldNotes.length === 0) {
        // No held notes - check if playhead position would extend pattern
        var currentRelativeBeat = getPlaybackBeatNow() - clip.startBeat;
        var quantizeBeats = pianoRoll.quantize || 0.25;
        var quantizedBeat = Math.ceil(currentRelativeBeat / quantizeBeats) * quantizeBeats;

        if (quantizedBeat > baseBeats) {
            recordingPreviewBeats = Math.ceil(quantizedBeat / 4) * 4;  // Round up to 4 beats
        } else {
            recordingPreviewBeats = 0;
        }
    } else {
        // Calculate expected end beat for each held note
        var maxEndBeat = baseBeats;
        var quantizeBeats = pianoRoll.quantize || 0.25;
        var currentRelativeBeat = getPlaybackBeatNow() - clip.startBeat;

        for (var i = 0; i < heldNotes.length; i++) {
            var noteInfo = midiNoteStartBeats[heldNotes[i]];
            if (noteInfo) {
                // Calculate where this note would end if released now
                var endBeat = Math.ceil(currentRelativeBeat / quantizeBeats) * quantizeBeats;
                // Ensure minimum duration of 1/16 note
                endBeat = Math.max(endBeat, noteInfo.beat + quantizeBeats);
                if (endBeat > maxEndBeat) {
                    maxEndBeat = endBeat;
                }
            }
        }

        // Set preview to rounded-up value (nearest 4 beats for clean display)
        if (maxEndBeat > baseBeats) {
            recordingPreviewBeats = Math.ceil(maxEndBeat / 4) * 4;
        } else {
            recordingPreviewBeats = 0;
        }
    }

    // Re-render timeline if preview changed at 1/16th note resolution
    var quantizedPreview = Math.floor(recordingPreviewBeats * 4) / 4;
    var quantizedLast = Math.floor(lastRecordingPreviewBeats * 4) / 4;

    var didExpand = applyRecordingPreviewToClip(pattern, clip);
    if (quantizedPreview !== quantizedLast || didExpand) {
        lastRecordingPreviewBeats = recordingPreviewBeats;
        renderTimeline();
        scheduleRenderPianoRoll();
    }
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

        // Handle piano roll patterns
        if (pattern.type === 'piano') {
            schedulePianoNotesAtBeat(trackId, clip, pattern, beat, p2);
            continue;
        }

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

        var stepBeat = step / patternLpb;
        var events = pattern.notes || [];
        var stepEvents = {};

        for (var e = 0; e < events.length; e++) {
            var ev = events[e];
            if (!ev) continue;
            if (!beatsMatch(ev.startBeat, stepBeat)) continue;
            var col = ev.column || 0;
            if (!stepEvents[col]) stepEvents[col] = { note: null, cell: null };
            if (isNoteEvent(ev)) stepEvents[col].note = ev;
            else if (isCellEvent(ev)) stepEvents[col].cell = ev;
        }

        var stepDuration = 60 / (state.bpm * patternLpb);
        // Use pattern's instrument setting (1-128), not track ID
        var instrNum = pattern.instrument || 1;

        for (var colKey in stepEvents) {
            var nc = parseInt(colKey);
            var entry = stepEvents[colKey];
            var noteEvent = entry.note;
            var cellEvent = entry.cell;

            // Voice key is per-track per-noteCol (persists across clips on same track)
            var voiceKey = trackId + '_' + nc;

            var hasOff = cellEvent && cellEvent.note === NOTE_OFF;
            if (hasOff) {
                if (activeVoices[voiceKey]) {
                    var voice = activeVoices[voiceKey];
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
            }

            if (noteEvent) {
                var freq = midiNoteToFreq(noteEvent.pitch);
                if (!isNaN(freq)) {
                    // Check if there's already a voice in this column that needs to be turned off
                    var hadOldVoice = false;
                    if (activeVoices[voiceKey]) {
                        hadOldVoice = true;
                        var oldVoice = activeVoices[voiceKey];
                        var offMsg = 'i 998 ' + p2.toFixed(4) + ' 0.01 ' + oldVoice.instrInstance;
                        try {
                            csound.inputMessage(offMsg);
                            logVoice('OFF-REPLACE', voiceKey, { oldInstr: oldVoice.instrInstance, oldNote: oldVoice.noteName, msg: offMsg });
                        } catch (err) {
                            logVoice('OFF-REPLACE-ERROR', voiceKey, { error: err.message || err });
                        }
                        delete activeVoices[voiceKey];
                    }

                    // Allocate new unique fractional instance
                    var instrInstance = instrNum + '.' + voiceCounter.toString().padStart(3, '0');
                    voiceCounter++;
                    if (voiceCounter > 999) voiceCounter = 1;

                    var amp = (noteEvent.velocity === null || noteEvent.velocity === undefined) ? 0.5 : noteEvent.velocity;
                    var noteOnP2 = hadOldVoice ? (p2 + 0.005).toFixed(4) : p2.toFixed(4);
                    var pfields = [instrInstance, noteOnP2, -1, freq.toFixed(4), amp.toFixed(4)];

                    // Add FX columns as p6, p7, etc.
                    var fxCount = (noteEvent.fx || []).length;
                    for (var fx = 0; fx < fxCount; fx++) {
                        var fxStr = noteEvent.fx[fx];
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
                        logVoice('ON', voiceKey, { instr: instrInstance, note: midiToNoteName(noteEvent.pitch), freq: freq.toFixed(2), msg: onMsg });
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
                        noteName: midiToNoteName(noteEvent.pitch)
                    };
                }
            } else if (cellEvent && hasFxValues(cellEvent.fx) && activeVoices[voiceKey]) {
                // FX update on held note
                var hasFx = false;
                var fxValues = [];
                var voice = activeVoices[voiceKey];
                var fxCount = Math.max((cellEvent.fx || []).length, voice.fxCount || 0);

                for (var fx = 0; fx < fxCount; fx++) {
                    var fxStr = cellEvent.fx && cellEvent.fx[fx] ? cellEvent.fx[fx] : '';
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--' && fxStr !== '----') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                        hasFx = true;
                    }
                    fxValues.push(fxVal);
                }

                if (hasFx) {
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

// Track active piano roll voices for note-off scheduling
var activePianoVoices = {};

function schedulePianoNotesAtBeat(trackId, clip, pattern, beat, p2) {
    if (!pattern.notes || pattern.notes.length === 0) return;

    // Calculate local beat within the pattern (accounting for clip start and looping)
    var localBeat = beat - clip.startBeat;
    var patternBeats = pattern.beats || 4;

    if (localBeat < 0) return;

    var loopCount = 0;
    var playBeat = localBeat;

    if (clip.loopLength !== undefined && clip.loopLength !== null) {
        var loopLength = clip.loopLength;
        if (loopLength <= 0) return;

        loopCount = Math.floor(localBeat / loopLength);
        var loopBeat = localBeat % loopLength;
        playBeat = (clip.offset || 0) + loopBeat;
        if (playBeat >= patternBeats) playBeat -= patternBeats;
    } else {
        // Legacy offset behavior
        playBeat = localBeat + (clip.offset || 0);
        loopCount = Math.floor(playBeat / patternBeats);
        playBeat = playBeat % patternBeats;
        if (playBeat < 0) playBeat += patternBeats;
    }

    // Scheduler step size (in beats) - use max LPB for finest resolution
    var maxLpb = getMaxLpb() || state.lpb;
    var schedulerStepBeats = 1 / maxLpb;
    var windowStart = playBeat - schedulerStepBeats;
    var eps = schedulerStepBeats * 0.001;
    var hasWrapWindow = windowStart < 0;

    // Get instrument number for this pattern
    var instrNum = pattern.instrument || 1;

    // Find notes that start at this beat
    for (var i = 0; i < pattern.notes.length; i++) {
        var note = pattern.notes[i];
        if (!isNoteEvent(note)) continue;

        var startBeat = note.startBeat;
        // Check if this note start is within the current scheduler window
        var inWindow = false;
        if (!hasWrapWindow) {
            inWindow = (startBeat > windowStart + eps && startBeat <= playBeat + eps);
        } else {
            var wrapStart = windowStart + patternBeats;
            inWindow = (startBeat > wrapStart + eps && startBeat <= patternBeats + eps) ||
                       (startBeat <= playBeat + eps);
        }

        if (inWindow) {
            var voiceKey = trackId + '_piano_' + i + '_' + loopCount;

            // Skip if already played in this loop
            if (activePianoVoices[voiceKey]) continue;

            // Calculate duration in seconds
            if (typeof note.duration !== 'number' || note.duration <= 0) continue;
            var durationSecs = (note.duration * 60) / state.bpm;
            var freq = midiNoteToFreq(note.pitch);
            var amp = (note.velocity === null || note.velocity === undefined) ? 0.5 : note.velocity;

            // Create unique instrument instance (string format to avoid float precision issues)
            voiceCounter++;
            if (voiceCounter > 999) voiceCounter = 1;
            var instrInstance = instrNum + '.' + voiceCounter.toString().padStart(3, '0');

            // Schedule note-on
            var pfields = [instrInstance, p2.toFixed(4), durationSecs.toFixed(4), freq.toFixed(4), amp.toFixed(4)];
            var fxValues = note.fx || [];
            var fxCount = Math.min(8, fxValues.length);
            for (var fx = 0; fx < fxCount; fx++) {
                var fxVal = fxValues[fx];
                if (typeof fxVal === 'string' && fxVal !== '' && fxVal !== '--' && fxVal !== '----') {
                    var parsed = parseInt(fxVal, 16);
                    fxVal = isNaN(parsed) ? 0 : parsed;
                }
                if (typeof fxVal !== 'number' || !isFinite(fxVal)) fxVal = 0;
                pfields.push(fxVal);
            }
            var msg = 'i ' + pfields.join(' ');

            try {
                csound.inputMessage(msg);
                activePianoVoices[voiceKey] = {
                    instrInstance: instrInstance,
                    endBeat: beat + note.duration
                };
                logVoice('PIANO-ON', voiceKey, { instr: instrInstance, pitch: note.pitch, duration: note.duration });
            } catch (err) {
                logVoice('PIANO-ON-ERROR', voiceKey, { error: err.message || err });
            }
        }
    }

    // Clean up expired piano voices
    var keysToDelete = [];
    for (var key in activePianoVoices) {
        if (activePianoVoices[key].endBeat <= beat) {
            keysToDelete.push(key);
        }
    }
    for (var j = 0; j < keysToDelete.length; j++) {
        delete activePianoVoices[keysToDelete[j]];
    }
}

function midiNoteToFreq(midiNote) {
    return 440 * Math.pow(2, (midiNote - 69) / 12);
}

// Get note duration in steps for a specific note column
function getNoteDurationStepsSingle(pattern, startStep, noteColIndex) {
    var lpb = pattern.lpb || state.lpb;
    var startBeat = startStep / lpb;
    var endBeat = pattern.steps / lpb;
    var events = pattern.notes || [];

    for (var i = 0; i < events.length; i++) {
        var ev = events[i];
        if ((ev.column || 0) !== noteColIndex) continue;
        if (ev.startBeat <= startBeat) continue;
        if (isNoteEvent(ev) || (isCellEvent(ev) && ev.note === NOTE_OFF)) {
            if (ev.startBeat < endBeat) endBeat = ev.startBeat;
        }
    }

    var durationBeats = endBeat - startBeat;
    if (durationBeats <= 0) durationBeats = 1 / lpb;
    return Math.max(1, Math.round(durationBeats * lpb));
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

function getPlaybackBeatNow() {
    if (!state.isPlaying || !audioCtx) return state.currentBeat;

    var elapsedSecs = audioCtx.currentTime - playbackStartTime;
    var elapsedBeats = elapsedSecs * (state.bpm / 60);
    var beat = playbackStartBeat + elapsedBeats;

    if (state.timeline.loopEnabled) {
        var loopStart = state.timeline.loopStart || 0;
        var loopLen = (state.timeline.loopEnd || 0) - loopStart;
        if (loopLen > 0) {
            var rel = beat - loopStart;
            rel = ((rel % loopLen) + loopLen) % loopLen;
            beat = loopStart + rel;
        }
    }

    return beat;
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

        // Check loop region or stop at song end
        if (state.timeline.loopEnabled) {
            // Loop within the loop region
            if (state.currentBeat >= state.timeline.loopEnd) {
                // Turn off all held notes before looping
                turnOffAllActiveVoices(nextStepTime - audioCtx.currentTime);
                state.currentBeat = state.timeline.loopStart;
                clipLastStep = {};  // Reset clip tracking for loop
                activeVoices = {};  // Reset active voices for loop
                activePianoVoices = {};  // Reset piano roll voices for loop
                voiceCounter = 1;
            }
        } else {
            // Stop at the song end marker when looping is disabled
            var endPoint = state.timeline.totalBeats;
            if (state.currentBeat >= endPoint) {
                state.currentBeat = endPoint;
                stopPlayback();
                return;
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

    // If the playhead is at/after the end, restart from loop start or 0
    var playbackEnd = state.timeline.loopEnabled ? state.timeline.loopEnd : state.timeline.totalBeats;
    if (state.currentBeat >= playbackEnd - 0.0001) {
        state.currentBeat = state.timeline.loopEnabled ? state.timeline.loopStart : 0;
    }
    if (state.currentBeat < 0) {
        state.currentBeat = state.timeline.loopEnabled ? state.timeline.loopStart : 0;
    }

    state.isPlaying = true;
    clipLastStep = {};  // Reset clip step tracking
    activeVoices = {};  // Reset active voices
    voiceCounter = 1;  // Reset voice counter
    logVoice('PLAYBACK-START', 'all', { beat: state.currentBeat, voiceCounter: voiceCounter });

    // Show timeline playhead
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) playhead.style.display = 'block';

    prerenderAllPatterns();

    // Initialize precise timing using Web Audio clock
    playbackStartBeat = state.currentBeat;
    playbackStartTime = audioCtx.currentTime;
    nextStepTime = audioCtx.currentTime;
    // Start lookahead scheduler (runs every 25ms, schedules 100ms ahead)
    scheduler();

    // Visual updates are decoupled from audio - use requestAnimationFrame
    pendingVisualUpdate = requestAnimationFrame(visualUpdateLoop);

    // Stop non-playback preview timer (visualUpdateLoop handles it during playback)
    stopRecordingPreviewTimer();

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
    // If already stopped, second click goes back to beginning
    if (!state.isPlaying) {
        state.currentBeat = 0;
        var playhead = document.getElementById('timeline-playhead');
        if (playhead) {
            playhead.style.left = '0px';
        }
        updateTimelinePlayhead();
        killAllNotes();
        consoleLog('Returned to start');
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
    activePianoVoices = {};
    voiceCounter = 1;

    // Clear MIDI recording state
    midiNoteStartBeats = {};

    // Reset recording preview
    recordingPreviewBeats = 0;
    lastRecordingPreviewBeats = 0;

    // Restart preview timer if still recording (for non-playback recording mode)
    if (state.isRecording) {
        startRecordingPreviewTimer();
    }

    var rows = document.querySelectorAll('.track-row.playing');
    for (var i = 0; i < rows.length; i++) {
        rows[i].classList.remove('playing');
    }

    // Keep playhead visible at stopped position so user can resume from there
    var playhead = document.getElementById('timeline-playhead');
    if (playhead) {
        playhead.style.display = 'block';
        playhead.style.left = (state.currentBeat * timelinePixelsPerBeat) + 'px';
    }

    document.getElementById('btn-play').disabled = false;
    // Keep stop button enabled for "panic" functionality (second click kills all notes)
    consoleLog('Stopped at beat ' + state.currentBeat.toFixed(2));
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
            if (p && p.type !== 'piano') syncNotesToData(p);
            return {
                id: p.id,
                name: p.name,
                type: p.type,
                trackId: p.trackId,
                instrument: p.instrument || 1,
                steps: p.steps,
                lpb: p.lpb,
                beats: p.beats,
                noteColumns: p.noteColumns,
                fxColumns: p.fxColumns,
                notes: p.notes,
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
        songInfo: state.songInfo,
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

function saveSongAs(name) {
    saveCurrentInstrument();
    saveOpcodes();

    // Serialize ftable pool with base64-encoded audio data
    var serializedFtables = state.ftablePool.map(function(item) {
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
        version: 6,
        bpm: state.bpm,
        lpb: state.lpb,
        timeSignature: state.timeSignature,
        quantize: state.quantize,
        patterns: state.patterns.map(function(p) {
            if (p && p.type !== 'piano') syncNotesToData(p);
            return {
                id: p.id,
                name: p.name,
                type: p.type,
                trackId: p.trackId,
                instrument: p.instrument || 1,
                steps: p.steps,
                lpb: p.lpb,
                beats: p.beats,
                noteColumns: p.noteColumns,
                fxColumns: p.fxColumns,
                notes: p.notes,
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
        songInfo: state.songInfo,
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
    a.download = name + '.cst';
    a.click();

    URL.revokeObjectURL(url);

    var sizeKB = (json.length / 1024).toFixed(1);
    consoleLog('Song saved as "' + name + '.cst" (v6 format, ' + sizeKB + 'KB)');
}

// ============================================
// CLIPBOARD OPERATIONS (Unified Events Format)
// ============================================
// All copy/paste operations use unified event format:
// - Note events: { type:'note', pitch, startBeat, duration, velocity, column, fx }
// - Cell events: { type:'cell', startBeat, column, note, amp, fx }
// This allows copying between tracker and piano roll seamlessly.

function cutSelection() {
    if (uiFocus === 'timeline') {
        cutClip();
        return;
    }

    copySelection();
    deleteSelection();
}

function copySelection() {
    if (uiFocus === 'timeline') {
        copySelectedClips();
        return;
    }

    var pattern = getCurrentPattern();
    if (!pattern) return;

    // Clear clip clipboard when copying notes
    clipboardClip = null;
    clipboardClips = null;

    var copiedEvents = [];
    var lpb = pattern.lpb || state.lpb;

    if (uiFocus === 'piano') {
        if (pattern.type !== 'piano') {
            consoleLog('Nothing to copy');
            return;
        }
        // Copy selected piano roll notes
        if (pianoSelection.selectedNotes.length > 0) {
            var notes = pattern.notes || [];
            pianoSelection.selectedNotes.forEach(function(idx) {
                if (notes[idx]) {
                    var n = JSON.parse(JSON.stringify(notes[idx]));
                    n.type = 'note';
                    copiedEvents.push(n);
                }
            });
        } else if (pianoRoll.dragNote) {
            var n = JSON.parse(JSON.stringify(pianoRoll.dragNote));
            n.type = 'note';
            copiedEvents.push(n);
        }
    } else if (uiFocus === 'tracker') {
        if (pattern.type === 'piano') {
            consoleLog('Nothing to copy');
            return;
        }
        // Copy selected tracker cells - convert to unified events
        if (selectedCells.length > 0) {
            // Group cells by step and noteCol to find complete rows
            var noteMap = {};  // key: "step_col" -> { note, amp, fx }

            for (var i = 0; i < selectedCells.length; i++) {
                var info = getCellInfo(selectedCells[i]);
                if (!info) continue;

                var key = info.step + '_' + info.noteCol;
                if (!noteMap[key]) {
                    noteMap[key] = { step: info.step, noteCol: info.noteCol, note: '', amp: '', fx: [] };
                }

                var value = selectedCells[i].textContent;
                if (info.type === 'note') {
                    noteMap[key].note = value;
                } else if (info.type === 'amp') {
                    noteMap[key].amp = value;
                } else if (info.type === 'fx') {
                    while (noteMap[key].fx.length <= info.col) {
                        noteMap[key].fx.push('');
                    }
                    noteMap[key].fx[info.col] = value;
                }
            }

            // Convert grouped cells to events
            for (var key in noteMap) {
                var cell = noteMap[key];
                var stepBeat = cell.step / lpb;
                var ampVal = (cell.amp && cell.amp !== '--') ? cell.amp : '';
                var fxVals = cell.fx.slice();

                if (cell.note === NOTE_OFF) {
                    copiedEvents.push({
                        type: 'cell',
                        startBeat: stepBeat,
                        column: cell.noteCol,
                        note: NOTE_OFF,
                        amp: ampVal,
                        fx: fxVals
                    });
                    continue;
                }

                if (cell.note && cell.note !== '---') {
                    var pitch = noteNameToMidi(cell.note);
                    if (pitch === null) continue;

                    copiedEvents.push({
                        type: 'note',
                        pitch: pitch,
                        startBeat: stepBeat,
                        duration: null,
                        velocity: hexToVelocity(ampVal),
                        column: cell.noteCol,
                        fx: fxVals
                    });
                    continue;
                }

                if ((ampVal && ampVal !== '') || hasFxValues(fxVals)) {
                    copiedEvents.push({
                        type: 'cell',
                        startBeat: stepBeat,
                        column: cell.noteCol,
                        note: '',
                        amp: ampVal,
                        fx: fxVals
                    });
                }
            }

            // Derive tracker note durations for cross-view paste
            deriveTrackerNoteDurations(copiedEvents, lpb);
        }
    } else {
        consoleLog('Nothing to copy');
        return;
    }

    if (copiedEvents.length > 0) {
        clipboard.type = 'events';
        clipboard.data = copiedEvents;
        consoleLog('Copied ' + copiedEvents.length + ' event(s)');
    } else {
        consoleLog('Nothing to copy');
    }
}

function pasteSelection() {
    if (uiFocus === 'timeline') {
        if (!clipboardClip && (!clipboardClips || !clipboardClips.clips || clipboardClips.clips.length === 0)) {
            if (clipboard.type === 'events') {
                consoleLog('Clipboard has note data. Paste in tracker or piano roll.');
            } else {
                consoleLog('No clip in clipboard');
            }
            return;
        }
        var targetTrack = (state.timeline.cursorTrack !== undefined && state.timeline.cursorTrack !== null) ?
            state.timeline.cursorTrack : (state.selectedTrack >= 0 ? state.selectedTrack : 0);
        var targetBeat = (typeof state.timeline.cursorBeat === 'number') ? state.timeline.cursorBeat : (state.currentBeat || 0);
        pasteClips(targetTrack, targetBeat);
        return;
    }

    if (!clipboard.data || !clipboard.type) {
        if (clipboardClip || (clipboardClips && clipboardClips.clips && clipboardClips.clips.length > 0)) {
            consoleLog('Clipboard has a clip. Paste on the timeline.');
        } else {
            consoleLog('Nothing to paste');
        }
        return;
    }

    var pattern = getCurrentPattern();
    if (!pattern) return;

    // Handle unified events format (works for both tracker and piano roll)
    if (clipboard.type === 'events') {
        if (uiFocus === 'piano' && pattern.type !== 'piano') {
            consoleLog('Nothing to paste');
            return;
        }
        if (uiFocus === 'tracker' && pattern.type === 'piano') {
            consoleLog('Nothing to paste');
            return;
        }

        pushUndo(pattern.type === 'piano' ? 'piano-edit' : 'pattern-edit', captureStateForUndo('pattern-edit'));

        var lpb = pattern.lpb || state.lpb;

        // Find the earliest startBeat and column in clipboard
        var minBeat = Infinity;
        var minCol = Infinity;
        var minStep = Infinity;
        clipboard.data.forEach(function(ev) {
            if (!ev) return;
            if (ev.startBeat < minBeat) minBeat = ev.startBeat;
            var col = ev.column || 0;
            if (col < minCol) minCol = col;
            var step = Math.round(ev.startBeat * lpb);
            if (step < minStep) minStep = step;
        });

        if (pattern.type === 'piano') {
            // Paste to piano roll (note events only)
            if (!pattern.notes) pattern.notes = [];

            var pasteOffset = (typeof pianoRoll.lastClickBeat === 'number') ? pianoRoll.lastClickBeat : 0;
            var pastedCount = 0;

            clipboard.data.forEach(function(ev) {
                if (!isNoteEvent(ev)) return;
                var newNote = JSON.parse(JSON.stringify(ev));
                newNote.type = 'note';
                newNote.startBeat = newNote.startBeat - minBeat + pasteOffset;
                if (typeof newNote.duration !== 'number' || newNote.duration <= 0) {
                    newNote.duration = pianoRoll.quantize || 0.25;
                }
                pattern.notes.push(newNote);
                pastedCount++;
            });

            consoleLog('Pasted ' + pastedCount + ' note(s) to piano roll');
            if (pastedCount > 0) {
                markPatternNoteVizDirtyForPattern(pattern);
            }
            scheduleRenderPianoRoll();
        } else {
            // Paste to tracker grid
            var startStep = state.focusedStep || 0;
            var startCol = state.focusedNoteCol || 0;
            var pastedCount = 0;

            clipboard.data.forEach(function(ev) {
                if (!ev) return;
                var eventStep = Math.round(ev.startBeat * lpb);
                var targetStep = eventStep - minStep + startStep;
                var targetCol = (ev.column || 0) - minCol + startCol;

                if (targetStep < 0 || targetStep >= pattern.steps) return;
                if (targetCol < 0 || targetCol >= pattern.noteColumns) return;

                if (isNoteEvent(ev)) {
                    if (ev.pitch === null || ev.pitch === undefined) return;
                    setCellValue(targetStep, targetCol, 0, 'note', midiToNoteName(ev.pitch));
                    if (ev.velocity !== null && ev.velocity !== undefined) {
                        setCellValue(targetStep, targetCol, 0, 'amp', velocityToHex(ev.velocity));
                    } else {
                        setCellValue(targetStep, targetCol, 0, 'amp', '');
                    }
                    if (ev.fx && ev.fx.length > 0) {
                        for (var fx = 0; fx < ev.fx.length; fx++) {
                            setCellValue(targetStep, targetCol, fx, 'fx', ev.fx[fx] || '');
                        }
                    }

                    // If duration is set (e.g., from piano roll), insert NOTE_OFF
                    if (typeof ev.duration === 'number' && ev.duration > 0) {
                        var offStep = Math.round((ev.startBeat + ev.duration) * lpb) - minStep + startStep;
                        if (offStep >= 0 && offStep < pattern.steps) {
                            var offInfo = findTrackerEventsAtStep(pattern, offStep, targetCol);
                            if (!offInfo.noteEvent) {
                                setCellValue(offStep, targetCol, 0, 'note', NOTE_OFF);
                            }
                        }
                    }
                    pastedCount++;
                } else if (isCellEvent(ev)) {
                    if (ev.note === NOTE_OFF) {
                        setCellValue(targetStep, targetCol, 0, 'note', NOTE_OFF);
                    }
                    if (ev.amp !== undefined) {
                        setCellValue(targetStep, targetCol, 0, 'amp', ev.amp || '');
                    }
                    if (ev.fx && ev.fx.length > 0) {
                        for (var fx = 0; fx < ev.fx.length; fx++) {
                            setCellValue(targetStep, targetCol, fx, 'fx', ev.fx[fx] || '');
                        }
                    }
                    pastedCount++;
                }
            });

            consoleLog('Pasted ' + pastedCount + ' event(s) to tracker');
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
        return;
    }

    // Legacy support for old tracker-cells format
    if (clipboard.type === 'tracker-cells' && pattern.type !== 'piano' && uiFocus === 'tracker') {
        pushUndo('pattern-edit', captureStateForUndo('pattern-edit'));

        var startStep = state.focusedStep || 0;
        var startNoteCol = state.focusedNoteCol || 0;

        var minStep = Infinity, minNoteCol = Infinity;
        clipboard.data.forEach(function(c) {
            if (c.step < minStep) minStep = c.step;
            if (c.noteCol < minNoteCol) minNoteCol = c.noteCol;
        });

        clipboard.data.forEach(function(c) {
            var targetStep = c.step - minStep + startStep;
            var targetNoteCol = c.noteCol - minNoteCol + startNoteCol;

            if (targetStep < pattern.steps && targetNoteCol < pattern.noteColumns) {
                if (c.type === 'note') setCellValue(targetStep, targetNoteCol, 0, 'note', c.value);
                else if (c.type === 'amp') setCellValue(targetStep, targetNoteCol, 0, 'amp', c.value);
                else if (c.type === 'fx') setCellValue(targetStep, targetNoteCol, c.col, 'fx', c.value);
            }
        });

        consoleLog('Pasted ' + clipboard.data.length + ' cells');
        invalidatePatternCache();
        renderTrackerGrid(true);
    }
}

function pasteAtSelection() {
    uiFocus = 'tracker';
    pasteSelection();
}

function deleteSelection() {
    var pattern = getCurrentPattern();
    if (!pattern) return;

    pushUndo(pattern.type === 'piano' ? 'piano-edit' : 'pattern-edit', captureStateForUndo('pattern-edit'));

    if (pattern.type === 'piano') {
        // Delete selected piano roll notes
        if (pianoSelection.selectedNotes.length > 0) {
            var notes = pattern.notes || [];
            // Sort indices descending to remove from end first
            var sorted = pianoSelection.selectedNotes.slice().sort(function(a, b) { return b - a; });
            sorted.forEach(function(idx) {
                notes.splice(idx, 1);
            });
            pianoSelection.selectedNotes = [];
            consoleLog('Deleted ' + sorted.length + ' notes');
            markPatternNoteVizDirtyForPattern(pattern);
            scheduleRenderPianoRoll();
        } else if (pianoRoll.dragNote && pianoRoll.dragNoteIndex >= 0) {
            var notes = pattern.notes || [];
            notes.splice(pianoRoll.dragNoteIndex, 1);
            pianoRoll.dragNote = null;
            pianoRoll.dragNoteIndex = -1;
            consoleLog('Deleted 1 note');
            markPatternNoteVizDirtyForPattern(pattern);
            scheduleRenderPianoRoll();
        }
    } else {
        // Delete selected tracker cells
        if (selectedCells.length > 0) {
            for (var i = 0; i < selectedCells.length; i++) {
                var info = getCellInfo(selectedCells[i]);
                if (!info) continue;
                if (info.type === 'note') setCellValue(info.step, info.noteCol, 0, 'note', '');
                else if (info.type === 'amp') setCellValue(info.step, info.noteCol, 0, 'amp', '');
                else if (info.type === 'fx') setCellValue(info.step, info.noteCol, info.col, 'fx', '');
            }
            consoleLog('Deleted ' + selectedCells.length + ' cells');
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
    }
}

function selectAll() {
    var pattern = getCurrentPattern();
    if (!pattern) return;

    if (pattern.type === 'piano') {
        // Select all piano roll notes
        var notes = pattern.notes || [];
        pianoSelection.selectedNotes = [];
        for (var i = 0; i < notes.length; i++) {
            pianoSelection.selectedNotes.push(i);
        }
        consoleLog('Selected ' + notes.length + ' notes');
        scheduleRenderPianoRoll();
    } else {
        // Select all tracker cells - this is handled elsewhere
        consoleLog('Select all for tracker not implemented');
    }
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
            state.songInfo = songData.songInfo || '';
            state.currentInstrument = 0;
            state.selectedClip = { trackId: null, clipId: null };

            // Normalize patterns (notes/events)
            state.patterns.forEach(function(p) {
                if (!p) return;
                if (!p.lpb) p.lpb = state.lpb;
                if (!p.noteColumns) p.noteColumns = 1;
                if (!p.fxColumns) {
                    p.fxColumns = [];
                    while (p.fxColumns.length < p.noteColumns) p.fxColumns.push(0);
                }
                if (p.type === 'tracker') {
                    if (!p.steps) p.steps = 16;
                    p.beats = p.steps / (p.lpb || state.lpb);
                    if (!p.notes || p.notes.length === 0) {
                        if (p.data) p.notes = trackerDataToNotes(p);
                        else p.notes = [];
                    }
                } else if (p.type === 'piano') {
                    if (!p.beats) {
                        p.beats = p.steps ? (p.steps / (p.lpb || state.lpb)) : 4;
                    }
                    if (!p.notes) p.notes = [];
                }
            });

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
                ensureTimelineDefaults();
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
                ensureTimelineDefaults();
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
                    // Ensure fileName has leading slash for Csound WASM filesystem
                    var fileName = item.fileName || ('/' + (item.name || 'sample_ft' + item.tableNum + '.wav').replace(/[^a-zA-Z0-9._-]/g, '_'));
                    if (fileName.charAt(0) !== '/') fileName = '/' + fileName;

                    state.ftablePool.push({
                        tableNum: item.tableNum,
                        name: item.name,
                        libraryId: item.libraryId,
                        fileName: fileName
                    });

                    // Restore sample data for Csound
                    if (item.rawDataB64) {
                        var rawData = base64ToArrayBuffer(item.rawDataB64);
                        state.samples.push({
                            tableNum: item.tableNum,
                            name: item.name,
                            fileName: fileName,
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
            var infoEl = document.getElementById('song-info-text');
            if (infoEl) infoEl.value = state.songInfo || '';

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
            state.songInfo = songData.songInfo || '';
        state.currentInstrument = 0;
        state.selectedClip = { trackId: null, clipId: null };

        // Normalize patterns (notes/events)
        state.patterns.forEach(function(p) {
            if (!p) return;
            if (!p.lpb) p.lpb = state.lpb;
            if (!p.noteColumns) p.noteColumns = 1;
            if (!p.fxColumns) {
                p.fxColumns = [];
                while (p.fxColumns.length < p.noteColumns) p.fxColumns.push(0);
            }
            if (p.type === 'tracker') {
                if (!p.steps) p.steps = 16;
                p.beats = p.steps / (p.lpb || state.lpb);
                if (!p.notes || p.notes.length === 0) {
                    if (p.data) p.notes = trackerDataToNotes(p);
                    else p.notes = [];
                }
            } else if (p.type === 'piano') {
                if (!p.beats) {
                    p.beats = p.steps ? (p.steps / (p.lpb || state.lpb)) : 4;
                }
                if (!p.notes) p.notes = [];
            }
        });

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
            ensureTimelineDefaults();
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
            ensureTimelineDefaults();
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
                var fileName = item.fileName || ('/' + (item.name || 'sample_ft' + item.tableNum + '.wav').replace(/[^a-zA-Z0-9._-]/g, '_'));
                if (fileName.charAt(0) !== '/') fileName = '/' + fileName;

                state.ftablePool.push({
                    tableNum: item.tableNum,
                    name: item.name,
                    libraryId: item.libraryId,
                    fileName: fileName
                });
                if (item.rawDataB64) {
                    state.samples.push({
                        tableNum: item.tableNum,
                        name: item.name,
                        fileName: fileName,
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
        var infoEl = document.getElementById('song-info-text');
        if (infoEl) infoEl.value = state.songInfo || '';

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

    function isEmptyInstrument(code, instrIndex) {
        if (!code) return true;
        var trimmed = code.replace(/\r/g, '').trim();
        if (!trimmed) return true;
        var lines = trimmed.split('\n').map(function(line) {
            return line.replace(/;.*/, '').trim();
        }).filter(function(line) { return line.length > 0; });
        if (lines.length === 0) return true;
        var collapsed = lines.join(' ').replace(/\s+/g, ' ').trim();
        var emptyPattern = new RegExp('^instr\\s+' + (instrIndex + 1) + '\\s*endin$', 'i');
        return emptyPattern.test(collapsed);
    }

    var instrumentBlocks = [];
    for (var ins = 0; ins < state.instruments.length; ins++) {
        var instrCode = state.instruments[ins];
        if (!isEmptyInstrument(instrCode, ins)) {
            instrumentBlocks.push(instrCode);
        }
    }

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

    if (state.songInfo && state.songInfo.trim()) {
        csd += '; Song Info\n';
        state.songInfo.replace(/\r/g, '').split('\n').forEach(function(line) {
            csd += '; ' + line + '\n';
        });
        csd += '\n';
    }

    if (state.opcodes && state.opcodes.trim()) {
        csd += '; User Defined Opcodes\n' + state.opcodes + '\n\n';
    }

    csd += instrumentBlocks.join('\n\n');
    csd += '\n</CsInstruments>\n<CsScore>\n';

    // Add ftable load statements at the top of the score
    if (ftableStatements.length > 0) {
        csd += '; Load sample ftables\n';
        csd += ftableStatements.join('\n') + '\n\n';
    }

    var scoreEvents = [];
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
            var instrNum = pattern.instrument || 1;
            var clipDuration = getClipDurationBeats(clip);
            var clipEvents = collectClipEventsForSegment(pattern, clip, 0, clipDuration);

            for (var ei = 0; ei < clipEvents.length; ei++) {
                var ev = clipEvents[ei];
                if (!ev) continue;
                if (pattern.type === 'piano' && !isNoteEvent(ev)) continue;

                var eventBeat = clip.startBeat + ev.startBeat;
                var eventTime = eventBeat * (60 / state.bpm);

                allClipEvents.push({
                    time: eventTime,
                    trackIdx: trackIdx,
                    noteCol: ev.column || 0,
                    instrNum: instrNum,
                    event: ev,
                    stepDuration: stepDuration,
                    isPiano: pattern.type === 'piano'
                });
            }
        }
    }

    allClipEvents.sort(function(a, b) { return a.time - b.time; });

    function exportFxValue(val) {
        if (typeof val === 'number' && isFinite(val)) return val;
        if (typeof val === 'string' && val !== '' && val !== '--' && val !== '----') {
            var parsed = parseInt(val, 16);
            if (!isNaN(parsed)) return parsed;
        }
        return 0;
    }

    function nextInstrInstance(instrNum) {
        var suffix = csdVoiceCounter.toString().padStart(3, '0');
        csdVoiceCounter++;
        if (csdVoiceCounter > 999) csdVoiceCounter = 1;
        return instrNum + '.' + suffix;
    }

    function pushScoreEvent(p1, time, p3, fields) {
        var p1Str = String(p1);
        var p2Str = time.toFixed(4);
        var p3Num = (typeof p3 === 'number') ? p3 : parseFloat(p3) || 0;
        var p3Str = p3Num.toFixed(4);
        var line = 'i ' + p1Str + ' ' + p2Str + ' ' + p3Str;
        if (fields && fields.length > 0) {
            line += ' ' + fields.join(' ');
        }
        scoreEvents.push({
            time: time,
            p1: parseFloat(p1Str),
            p3: p3Num,
            line: line
        });
    }

    for (var i = 0; i < allClipEvents.length; i++) {
        var evt = allClipEvents[i];
        var ev = evt.event;
        var stepTime = evt.time;
        var instrNum = evt.instrNum;

        // Clean up expired voices so updates don't target ended notes
        for (var vk in csdActiveVoices) {
            if (csdActiveVoices[vk].endTime <= stepTime + 0.0001) {
                delete csdActiveVoices[vk];
            }
        }

        if (evt.isPiano && isNoteEvent(ev)) {
            var durationBeats = (typeof ev.duration === 'number' && ev.duration > 0) ? ev.duration : (1 / (state.lpb || 4));
            var durationSecs = (durationBeats * 60) / state.bpm;
            var freq = midiNoteToFreq(ev.pitch);
            var amp = (ev.velocity === null || ev.velocity === undefined) ? 0.5 : ev.velocity;

            var instrInstance = nextInstrInstance(instrNum);
            var pfields = [freq.toFixed(4), amp.toFixed(4)];
            var fxValues = ev.fx || [];
            for (var fx = 0; fx < fxValues.length; fx++) {
                pfields.push(exportFxValue(fxValues[fx]));
            }

            // Start held note
            pushScoreEvent(instrInstance, stepTime, -1, pfields);
            // Explicit note-off using negative p1
            pushScoreEvent('-' + instrInstance, stepTime + durationSecs, 0, []);
            continue;
        }

        var voiceKey = evt.trackIdx + '_' + evt.noteCol;

        if (isCellEvent(ev) && ev.note === NOTE_OFF) {
            var offVoice = csdActiveVoices[voiceKey];
            if (offVoice && offVoice.endTime > stepTime + 0.0001) {
                pushScoreEvent('-' + offVoice.instr, stepTime, 0, []);
                offVoice.endTime = stepTime;
            }
            continue;
        }

        if (isNoteEvent(ev)) {
            var freq = midiNoteToFreq(ev.pitch);
            var durationBeats = (typeof ev.duration === 'number' && ev.duration > 0) ? ev.duration : (1 / (state.lpb || 4));
            var durationSecs = (durationBeats * 60) / state.bpm;

            var instrInstance = nextInstrInstance(instrNum);

            var amp = (ev.velocity === null || ev.velocity === undefined) ? 0.5 : ev.velocity;
            var fxValues = [];
            for (var fx = 0; fx < (ev.fx || []).length; fx++) {
                fxValues.push(exportFxValue(ev.fx[fx]));
            }

            var pfields = [freq.toFixed(4), amp.toFixed(4)];
            for (var fx = 0; fx < fxValues.length; fx++) {
                pfields.push(fxValues[fx]);
            }

            // Start held note
            pushScoreEvent(instrInstance, stepTime, -1, pfields);
            // Explicit note-off using negative p1
            pushScoreEvent('-' + instrInstance, stepTime + durationSecs, 0, []);

            csdActiveVoices[voiceKey] = {
                instr: instrInstance,
                freq: freq,
                amp: amp,
                fxCount: fxValues.length,
                endTime: stepTime + durationSecs
            };
        } else if (isCellEvent(ev) && hasFxValues(ev.fx) && csdActiveVoices[voiceKey]) {
            var voice = csdActiveVoices[voiceKey];
            if (voice.endTime <= stepTime + 0.0001) continue;

            var fxValues = [];
            var fxCount = Math.max((ev.fx || []).length, voice.fxCount || 0);
            var hasFx = false;

            for (var fx = 0; fx < fxCount; fx++) {
                var fxStr = ev.fx && ev.fx[fx] ? ev.fx[fx] : '';
                if (fxStr !== '' && fxStr !== '--' && fxStr !== '----') hasFx = true;
                fxValues.push(exportFxValue(fxStr));
            }

            if (hasFx) {
                var updateFields = [voice.freq.toFixed(4), voice.amp.toFixed(4)];
                for (var u = 0; u < fxValues.length; u++) {
                    updateFields.push(fxValues[u]);
                }
                pushScoreEvent(voice.instr, stepTime, -1, updateFields);
                voice.fxCount = Math.max(voice.fxCount || 0, fxValues.length);
            }
        }
    }

    scoreEvents.sort(function(a, b) {
        if (a.time !== b.time) return a.time - b.time;
        if (a.p1 !== b.p1) return a.p1 - b.p1;
        return a.p3 - b.p3;
    });

    csd += scoreEvents.map(function(ev) { return ev.line; }).join('\n');
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
        consoleLog('CSD exported as ZIP (' + scoreEvents.length + ' events, ' + sampleFiles.length + ' samples, ' + totalSize + 'KB)');
    } else {
        // No samples - just export plain CSD
        var blob = new Blob([csd], { type: 'text/plain' });
        var url = URL.createObjectURL(blob);
        var a = document.createElement('a');
        a.href = url;
        a.download = 'composition.csd';
        a.click();
        URL.revokeObjectURL(url);
        consoleLog('CSD exported (' + scoreEvents.length + ' events)');
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
    var activeTab = document.querySelector('.main-tab.active');
    var currentTabName = activeTab ? activeTab.getAttribute('data-tab') : 'instruments';
    mainTabs.forEach(function(tab) {
        tab.addEventListener('click', function() {
            var tabName = this.getAttribute('data-tab');
            if (tabName === currentTabName) return;

            if (currentTabName === 'opcodes') {
                saveOpcodes();
                compileOpcodesIfChanged();
            } else if (currentTabName === 'instruments') {
                saveCurrentInstrument();
            }

            mainTabs.forEach(function(t) { t.classList.remove('active'); });
            this.classList.add('active');

            document.querySelectorAll('.tab-content').forEach(function(content) {
                content.classList.add('hidden');
            });
            document.getElementById('tab-' + tabName).classList.remove('hidden');

            currentTabName = tabName;
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

function compileCurrentInstrumentIfChanged() {
    saveCurrentInstrument();
    if (!state.csoundReady) return;
    var idx = state.currentInstrument;
    var currentCode = state.instruments[idx] || '';
    var lastCode = lastCompiled.instruments[idx] || '';
    if (currentCode !== lastCode) {
        compileSingleInstrument(idx);
    }
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
            // Ensure fileName has leading slash for Csound WASM filesystem
            var fileName = sample.fileName || ('/' + (sample.name || 'sample_ft' + sample.tableNum + '.wav'));
            if (fileName.charAt(0) !== '/') fileName = '/' + fileName;
            // Update the sample's fileName for consistency
            sample.fileName = fileName;

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
    velocityGrid: null,
    keysContainer: null,
    gridContainer: null,
    pixelsPerBeat: 40,
    noteHeight: 16,
    velocityLaneHeight: 50,
    velocityParam: 'p5',
    octaves: 9,  // C0 to C8
    lowestNote: 24,  // C1 (MIDI note 24)
    bgCacheCanvas: null,
    bgCacheKey: '',
    // State for interactions
    isDragging: false,
    dragMode: null,  // 'move', 'resize', 'draw'
    dragStartX: 0,
    dragStartY: 0,
    dragStartPitch: 0,
    dragNote: null,
    dragNoteIndex: -1,
    originalNoteData: null,
    lastClickBeat: 0,
    lastClickPitch: null,
    drawPreviewPitch: null,
    docTracking: false,
    velocityDragging: false,
    velocityDragIndices: null
};

var pianoRollRenderPending = false;

function scheduleRenderPianoRoll() {
    if (pianoRollRenderPending) return;
    pianoRollRenderPending = true;
    requestAnimationFrame(function() {
        pianoRollRenderPending = false;
        renderPianoRoll();
    });
}

function initPianoRoll() {
    pianoRoll.canvas = document.getElementById('piano-roll-canvas');
    pianoRoll.velocityCanvas = document.getElementById('velocity-canvas');
    pianoRoll.keysContainer = document.getElementById('piano-keys');
    pianoRoll.gridContainer = document.querySelector('.piano-roll-grid');
    pianoRoll.velocityGrid = document.querySelector('.velocity-grid');

    if (pianoRoll.canvas) {
        pianoRoll.ctx = pianoRoll.canvas.getContext('2d');
        pianoRoll.canvas.addEventListener('mousedown', handlePianoRollMouseDown);
        pianoRoll.canvas.addEventListener('mousemove', handlePianoRollMouseMove);
        pianoRoll.canvas.addEventListener('mouseup', handlePianoRollMouseUp);
        pianoRoll.canvas.addEventListener('mouseleave', handlePianoRollMouseUp);
        pianoRoll.canvas.addEventListener('dblclick', handlePianoRollDblClick);
        pianoRoll.canvas.addEventListener('contextmenu', handlePianoRollContextMenu);
    }

    if (pianoRoll.velocityCanvas) {
        pianoRoll.velocityCtx = pianoRoll.velocityCanvas.getContext('2d');
        pianoRoll.velocityCanvas.addEventListener('mousedown', handleVelocityMouseDown);
        pianoRoll.velocityCanvas.addEventListener('mousemove', handleVelocityMouseMove);
        pianoRoll.velocityCanvas.addEventListener('mouseup', handleVelocityMouseUp);
        pianoRoll.velocityCanvas.addEventListener('mouseleave', handleVelocityMouseUp);
    }

    if (pianoRoll.gridContainer && pianoRoll.keysContainer) {
        pianoRoll.gridContainer.addEventListener('scroll', function() {
            pianoRoll.keysContainer.scrollTop = pianoRoll.gridContainer.scrollTop;
            if (pianoRoll.velocityGrid) {
                pianoRoll.velocityGrid.scrollLeft = pianoRoll.gridContainer.scrollLeft;
            } else if (pianoRoll.velocityCanvas) {
                pianoRoll.velocityCanvas.style.transform = 'translateX(' + (-pianoRoll.gridContainer.scrollLeft) + 'px)';
            }
        });

        pianoRoll.gridContainer.addEventListener('wheel', function(e) {
            if (e.ctrlKey) {
                e.preventDefault();
                var factor = e.deltaY > 0 ? 0.9 : 1.1;
                zoomPianoRoll(factor);
                return;
            }
        }, { passive: false });

        pianoRoll.keysContainer.addEventListener('wheel', function(e) {
            if (!pianoRoll.gridContainer) return;
            pianoRoll.gridContainer.scrollTop += e.deltaY;
            pianoRoll.gridContainer.scrollLeft += e.deltaX;
            e.preventDefault();
        }, { passive: false });
    }

    // Quantize selector
    var quantizeSelect = document.getElementById('piano-quantize');
    if (quantizeSelect) {
        quantizeSelect.addEventListener('change', function() {
            pianoRoll.quantize = parseFloat(this.value) || 0.25;
        });
        pianoRoll.quantize = parseFloat(quantizeSelect.value) || 0.25;
    }

    // Velocity/parameter lane selector (p5-p13)
    var velocitySelect = document.getElementById('velocity-param-select');
    if (velocitySelect) {
        velocitySelect.addEventListener('change', function() {
            pianoRoll.velocityParam = this.value || 'p5';
            scheduleRenderPianoRoll();
        });
        pianoRoll.velocityParam = velocitySelect.value || 'p5';
    }

    // Zoom buttons
    var btnZoomIn = document.getElementById('btn-piano-zoom-in');
    var btnZoomOut = document.getElementById('btn-piano-zoom-out');
    if (btnZoomIn) btnZoomIn.addEventListener('click', function() { zoomPianoRoll(1.25); });
    if (btnZoomOut) btnZoomOut.addEventListener('click', function() { zoomPianoRoll(0.8); });

    // Instrument selector
    var instrSelect = document.getElementById('piano-instrument');
    if (instrSelect) {
        instrSelect.addEventListener('change', function() {
            var pattern = getCurrentPattern();
            if (pattern && pattern.type === 'piano') {
                pattern.instrument = parseInt(this.value) || 1;
            }
        });
    }

    // Keyboard shortcuts for piano roll
    document.addEventListener('keydown', function(e) {
        // Only handle when piano roll is visible
        var pianoContainer = document.getElementById('piano-roll-container');
        if (!pianoContainer || pianoContainer.classList.contains('hidden')) return;

        // Don't handle if focus is in a text input
        if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

        var pattern = getCurrentPattern();
        if (!pattern || pattern.type !== 'piano') return;

        // Delete key - delete selected note
        if (e.key === 'Delete' && !e.ctrlKey && !e.altKey && !e.shiftKey) {
            if (pianoSelection.selectedNotes && pianoSelection.selectedNotes.length > 0) {
                e.preventDefault();
                deleteSelection();
                return;
            }
            if (pianoRoll.dragNote && pianoRoll.dragNoteIndex >= 0) {
                e.preventDefault();
                var notes = pattern.notes || [];
                if (pianoRoll.dragNoteIndex < notes.length) {
                    notes.splice(pianoRoll.dragNoteIndex, 1);
                    pianoRoll.dragNote = null;
                    pianoRoll.dragNoteIndex = -1;
                    markPatternNoteVizDirtyForPattern(pattern);
                    scheduleRenderPianoRoll();
                }
                return;
            }
        }

        // Ctrl+D - duplicate selected note
        if (e.ctrlKey && (e.key === 'd' || e.key === 'D') && !e.altKey && !e.shiftKey) {
            if (pianoRoll.dragNote) {
                e.preventDefault();
                var notes = pattern.notes || [];
                var newNote = {
                    pitch: pianoRoll.dragNote.pitch,
                    startBeat: pianoRoll.dragNote.startBeat + pianoRoll.dragNote.duration,
                    duration: pianoRoll.dragNote.duration,
                    velocity: pianoRoll.dragNote.velocity || 0.8
                };
                notes.push(newNote);
                markPatternNoteVizDirtyForPattern(pattern);
                // Select the new note
                pianoRoll.dragNote = newNote;
                pianoRoll.dragNoteIndex = notes.length - 1;
                scheduleRenderPianoRoll();
                return;
            }
        }

        // Arrow keys - move selected note
        if (pianoRoll.dragNote && (e.key === 'ArrowUp' || e.key === 'ArrowDown' || e.key === 'ArrowLeft' || e.key === 'ArrowRight')) {
            e.preventDefault();
            var quantize = pianoRoll.quantize || 0.25;

            if (e.key === 'ArrowUp') {
                pianoRoll.dragNote.pitch = Math.min(127, pianoRoll.dragNote.pitch + 1);
            } else if (e.key === 'ArrowDown') {
                pianoRoll.dragNote.pitch = Math.max(0, pianoRoll.dragNote.pitch - 1);
            } else if (e.key === 'ArrowLeft') {
                pianoRoll.dragNote.startBeat = Math.max(0, pianoRoll.dragNote.startBeat - quantize);
            } else if (e.key === 'ArrowRight') {
                pianoRoll.dragNote.startBeat += quantize;
            }
            markPatternNoteVizDirtyForPattern(pattern);
            scheduleRenderPianoRoll();
            return;
        }

        // +/- keys - change note duration
        if (pianoRoll.dragNote && (e.key === '+' || e.key === '=' || e.key === '-' || e.key === '_')) {
            e.preventDefault();
            var quantize = pianoRoll.quantize || 0.25;
            if (e.key === '+' || e.key === '=') {
                pianoRoll.dragNote.duration += quantize;
            } else {
                pianoRoll.dragNote.duration = Math.max(quantize, pianoRoll.dragNote.duration - quantize);
            }
            markPatternNoteVizDirtyForPattern(pattern);
            scheduleRenderPianoRoll();
            return;
        }
    });

    renderPianoKeys();
}

function attachCodeEditorShortcuts() {
    var codeEditor = document.getElementById('code-editor');
    if (codeEditor) {
        codeEditor.addEventListener('keydown', function(e) {
            if (e.altKey && (e.code === 'KeyC' || e.key === 'c' || e.key === 'C')) {
                e.preventDefault();
                e.stopPropagation();
                compileCurrentInstrumentIfChanged();
            }
        }, true);
    }

    var opcodesEditor = document.getElementById('opcodes-editor');
    if (opcodesEditor) {
        opcodesEditor.addEventListener('keydown', function(e) {
            if (e.altKey && (e.code === 'KeyC' || e.key === 'c' || e.key === 'C')) {
                e.preventDefault();
                e.stopPropagation();
                saveOpcodes();
                compileOpcodesIfChanged();
            }
        }, true);
    }
}

// Update piano roll instrument selector with available instruments
function updatePianoInstrumentSelector() {
    var select = document.getElementById('piano-instrument');
    if (!select) return;

    var pattern = getCurrentPattern();
    var currentInstr = (pattern && pattern.instrument) ? pattern.instrument : 1;

    select.innerHTML = '';

    // Match pattern editor: list all instrument numbers
    var maxInstr = Math.max(1, state.instruments ? state.instruments.length : 128);
    for (var i = 1; i <= maxInstr; i++) {
        var option = document.createElement('option');
        option.value = i;
        option.textContent = i;
        if (i === currentInstr) {
            option.selected = true;
        }

        select.appendChild(option);
    }

    if (!select.value) {
        select.value = String(Math.max(1, Math.min(currentInstr, maxInstr)));
    }
}

function renderPianoKeys() {
    if (!pianoRoll.keysContainer) return;
    pianoRoll.keysContainer.innerHTML = '';

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
            startPianoRollRecordNote(note, 100);
            this.classList.add('playing');
        });
        key.addEventListener('mouseup', function() {
            var note = parseInt(this.getAttribute('data-note'));
            stopMidiNote(note);
            finishPianoRollRecordNote(note);
            this.classList.remove('playing');
        });
        key.addEventListener('mouseleave', function() {
            var note = parseInt(this.getAttribute('data-note'));
            stopMidiNote(note);
            finishPianoRollRecordNote(note);
            this.classList.remove('playing');
        });

        pianoRoll.keysContainer.appendChild(key);
    }

    // Keep note height aligned to actual key height (responsive layouts)
    var firstKey = pianoRoll.keysContainer.firstChild;
    if (firstKey) {
        var keyHeight = Math.round(firstKey.getBoundingClientRect().height);
        if (keyHeight > 0 && keyHeight !== pianoRoll.noteHeight) {
            pianoRoll.noteHeight = keyHeight;
        }
    }
}

// Get notes array from current pattern (single source of truth)
function getPianoNotes() {
    var pattern = getCurrentPattern();
    if (pattern && pattern.type === 'piano') {
        return pattern.notes || [];
    }
    return [];
}

// Get pattern beats
function getPianoPatternBeats() {
    var pattern = getCurrentPattern();
    if (!pattern) return 4;
    if (pattern.type === 'piano') {
        return pattern.beats || 4;
    }
    return (pattern.steps || 16) / (pattern.lpb || state.lpb);
}

function renderPianoRoll() {
    if (!pianoRoll.canvas || !pianoRoll.ctx) return;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') {
        // Clear canvas if no piano pattern
        pianoRoll.ctx.fillStyle = '#1a1a2e';
        pianoRoll.ctx.fillRect(0, 0, pianoRoll.canvas.width, pianoRoll.canvas.height);
        return;
    }

    if (pianoRoll.keysContainer && pianoRoll.keysContainer.firstChild) {
        var keyHeight = Math.round(pianoRoll.keysContainer.firstChild.getBoundingClientRect().height);
        if (keyHeight > 0 && keyHeight !== pianoRoll.noteHeight) {
            pianoRoll.noteHeight = keyHeight;
        }
    }

    var patternBeats = pattern.beats || 4;
    var patternLpb = pattern.lpb || state.lpb;
    var totalNotes = pianoRoll.octaves * 12;
    var displayBeats = patternBeats;
    var showRecordingPreview = state.isRecording && recordingPreviewBeats > patternBeats + 0.0001;
    if (showRecordingPreview) {
        displayBeats = recordingPreviewBeats;
    }

    // Size canvas
    var width = Math.max(400, displayBeats * pianoRoll.pixelsPerBeat);
    var height = totalNotes * pianoRoll.noteHeight;
    pianoRoll.canvas.width = width;
    pianoRoll.canvas.height = height;

    var ctx = pianoRoll.ctx;

    // Cache static background (rows + beat highlights + grid lines)
    var bgKey = [
        width,
        height,
        displayBeats,
        patternLpb,
        pianoRoll.pixelsPerBeat,
        pianoRoll.noteHeight,
        pianoRoll.octaves,
        pianoRoll.lowestNote
    ].join('|');

    if (!pianoRoll.bgCacheCanvas || pianoRoll.bgCacheKey !== bgKey) {
        var bg = document.createElement('canvas');
        bg.width = width;
        bg.height = height;
        var bgCtx = bg.getContext('2d');

        bgCtx.fillStyle = '#1a1a2e';
        bgCtx.fillRect(0, 0, width, height);

        for (var i = 0; i < totalNotes; i++) {
            var y = i * pianoRoll.noteHeight;
            var noteNum = pianoRoll.lowestNote + (totalNotes - i - 1);
            var isBlack = [1, 3, 6, 8, 10].indexOf(noteNum % 12) !== -1;

            if (isBlack) {
                bgCtx.fillStyle = '#12122a';
                bgCtx.fillRect(0, y, width, pianoRoll.noteHeight);
            }

            bgCtx.strokeStyle = '#0f3460';
            bgCtx.lineWidth = 1;
            bgCtx.beginPath();
            bgCtx.moveTo(0, y);
            bgCtx.lineTo(width, y);
            bgCtx.stroke();
        }

        var beatCount = Math.ceil(displayBeats);
        for (var b = 0; b < beatCount; b++) {
            var bx = b * pianoRoll.pixelsPerBeat;
            var bxEnd = Math.min(width, (b + 1) * pianoRoll.pixelsPerBeat);
            var bw = bxEnd - bx;
            if (bw <= 0) continue;
            bgCtx.fillStyle = (b % 2 === 0) ? 'rgba(255, 255, 255, 0.05)' : 'rgba(0, 0, 0, 0.08)';
            bgCtx.fillRect(bx, 0, bw, height);
        }

        var stepsPerBeat = patternLpb;
        var totalSteps = displayBeats * stepsPerBeat;
        for (var step = 0; step <= totalSteps; step++) {
            var gx = (step / stepsPerBeat) * pianoRoll.pixelsPerBeat;
            var isBeat = step % stepsPerBeat === 0;
            var isBar = step % (stepsPerBeat * 4) === 0;

            bgCtx.strokeStyle = isBar ? '#2a4a7a' : (isBeat ? '#1a3a5a' : '#0f3460');
            bgCtx.lineWidth = isBar ? 2 : 1;
            bgCtx.beginPath();
            bgCtx.moveTo(gx, 0);
            bgCtx.lineTo(gx, height);
            bgCtx.stroke();
        }

        pianoRoll.bgCacheCanvas = bg;
        pianoRoll.bgCacheKey = bgKey;
    }

    ctx.drawImage(pianoRoll.bgCacheCanvas, 0, 0);

    if (showRecordingPreview) {
        var previewX = patternBeats * pianoRoll.pixelsPerBeat;
        var previewW = Math.max(0, width - previewX);
        if (previewW > 0) {
            ctx.save();
            ctx.fillStyle = 'rgba(255, 68, 68, 0.08)';
            ctx.fillRect(previewX, 0, previewW, height);
            ctx.strokeStyle = 'rgba(255, 68, 68, 0.6)';
            ctx.lineWidth = 2;
            ctx.beginPath();
            ctx.moveTo(previewX, 0);
            ctx.lineTo(previewX, height);
            ctx.stroke();
            ctx.restore();
        }
    }

    // Draw notes from pattern
    var notes = pattern.notes || [];
    for (var i = 0; i < notes.length; i++) {
        var note = notes[i];
        if (!isNoteEvent(note)) continue;
        var isSelected = pianoRoll.dragNote === note || pianoSelection.selectedNotes.indexOf(i) >= 0;
        drawPianoNote(ctx, note, isSelected);
    }

    // Draw selected paste position
    if (typeof pianoRoll.lastClickBeat === 'number') {
        var posX = pianoRoll.lastClickBeat * pianoRoll.pixelsPerBeat;
        ctx.save();
        ctx.strokeStyle = 'rgba(255, 255, 255, 0.75)';
        ctx.lineWidth = 1;
        ctx.setLineDash([4, 3]);
        ctx.beginPath();
        ctx.moveTo(posX, 0);
        ctx.lineTo(posX, height);
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.restore();
    }

    // Draw selection rectangle if active
    if (pianoSelection.active && pianoRoll.dragMode === 'select') {
        var selStartX = pianoSelection.startBeat * pianoRoll.pixelsPerBeat;
        var selEndX = pianoSelection.endBeat * pianoRoll.pixelsPerBeat;
        var selStartY = (totalNotes - (pianoSelection.startPitch - pianoRoll.lowestNote) - 1) * pianoRoll.noteHeight;
        var selEndY = (totalNotes - (pianoSelection.endPitch - pianoRoll.lowestNote) - 1) * pianoRoll.noteHeight;

        var rectX = Math.min(selStartX, selEndX);
        var rectY = Math.min(selStartY, selEndY);
        var rectW = Math.abs(selEndX - selStartX);
        var rectH = Math.abs(selEndY - selStartY);

        ctx.strokeStyle = '#4ecca3';
        ctx.lineWidth = 2;
        ctx.strokeRect(rectX, rectY, rectW, rectH);
        ctx.fillStyle = 'rgba(78, 204, 163, 0.15)';
        ctx.fillRect(rectX, rectY, rectW, rectH);
    }

    // Playhead is shown only in the song view

    renderVelocityLane();

    if (!state.isPlaying) {
        flushPatternNoteVizDirty();
    }

    if (pianoRoll.gridContainer && pianoRoll.keysContainer) {
        pianoRoll.keysContainer.scrollTop = pianoRoll.gridContainer.scrollTop;
        if (pianoRoll.velocityGrid) {
            pianoRoll.velocityGrid.scrollLeft = pianoRoll.gridContainer.scrollLeft;
        } else if (pianoRoll.velocityCanvas) {
            pianoRoll.velocityCanvas.style.transform = 'translateX(' + (-pianoRoll.gridContainer.scrollLeft) + 'px)';
        }
    }
}

function drawPianoNote(ctx, note, isSelected) {
    var totalNotes = pianoRoll.octaves * 12;
    var noteRow = totalNotes - (note.pitch - pianoRoll.lowestNote) - 1;

    if (noteRow < 0 || noteRow >= totalNotes) return;  // Out of range
    if (typeof note.duration !== 'number' || note.duration <= 0) return;

    var y = noteRow * pianoRoll.noteHeight;
    var x = note.startBeat * pianoRoll.pixelsPerBeat;
    var w = Math.max(4, note.duration * pianoRoll.pixelsPerBeat);

    // Note fill
    var velocity = note.velocity || 0.8;
    var brightness = Math.floor(velocity * 60 + 40);
    ctx.fillStyle = isSelected ? '#ff9f43' : 'hsl(160, 60%, ' + brightness + '%)';
    ctx.fillRect(x + 1, y + 1, w - 2, pianoRoll.noteHeight - 2);

    // Note border
    ctx.strokeStyle = isSelected ? '#fff' : 'rgba(0,0,0,0.4)';
    ctx.lineWidth = isSelected ? 2 : 1;
    ctx.strokeRect(x + 1, y + 1, w - 2, pianoRoll.noteHeight - 2);

    // Resize handle indicator (right edge)
    ctx.fillStyle = 'rgba(255,255,255,0.3)';
    ctx.fillRect(x + w - 5, y + 1, 4, pianoRoll.noteHeight - 2);
}

function renderVelocityLane() {
    if (!pianoRoll.velocityCanvas || !pianoRoll.velocityCtx) return;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var patternBeats = pattern.beats || 4;
    var laneHeight = pianoRoll.velocityLaneHeight || 50;
    var canvas = pianoRoll.velocityCanvas;
    var ctx = pianoRoll.velocityCtx;
    var paramIndex = getPianoParamIndex();

    canvas.width = Math.max(400, patternBeats * pianoRoll.pixelsPerBeat);
    canvas.height = laneHeight;

    ctx.fillStyle = '#12122a';
    ctx.fillRect(0, 0, canvas.width, laneHeight);

    // Draw parameter bars for each note
    var notes = pattern.notes || [];
    for (var i = 0; i < notes.length; i++) {
        var note = notes[i];
        if (!isNoteEvent(note)) continue;
        var x = note.startBeat * pianoRoll.pixelsPerBeat;
        var value = getPianoNoteParamValue(note, paramIndex);
        var h = Math.max(0, Math.min(1, value)) * laneHeight;

        ctx.fillStyle = '#4ecca3';
        ctx.fillRect(x + 2, laneHeight - h, 8, h);
    }
}

function getVelocityTargetsAtX(pattern, x) {
    if (!pattern || pattern.type !== 'piano') return [];
    var notes = pattern.notes || [];
    if (notes.length === 0) return [];

    var clickBeat = x / pianoRoll.pixelsPerBeat;
    var thresholdPx = Math.max(6, Math.min(12, pianoRoll.pixelsPerBeat * 0.3));
    var thresholdBeats = thresholdPx / pianoRoll.pixelsPerBeat;
    var hits = [];

    for (var i = 0; i < notes.length; i++) {
        if (!isNoteEvent(notes[i])) continue;
        if (Math.abs(notes[i].startBeat - clickBeat) <= thresholdBeats) {
            hits.push(i);
        }
    }

    if (hits.length === 0) return [];
    if (pianoSelection.selectedNotes.length > 0) {
        var selectedHits = [];
        for (var j = 0; j < pianoSelection.selectedNotes.length; j++) {
            var idx = pianoSelection.selectedNotes[j];
            if (hits.indexOf(idx) >= 0) {
                selectedHits.push(idx);
            }
        }
        if (selectedHits.length > 0) return selectedHits;
    }

    return hits;
}

function velocityFromY(y, height) {
    var laneHeight = height || pianoRoll.velocityLaneHeight || 50;
    var v = (laneHeight - y) / laneHeight;
    return Math.max(0, Math.min(1, v));
}

function getPianoParamIndex() {
    if (!pianoRoll.velocityParam || pianoRoll.velocityParam === 'p5') return -1;
    var num = parseInt(pianoRoll.velocityParam.replace('p', ''), 10);
    if (isNaN(num) || num < 6) return -1;
    return num - 6;
}

function getPianoNoteParamValue(note, paramIndex) {
    if (!note) return 0;
    if (paramIndex < 0) {
        return (note.velocity === null || note.velocity === undefined) ? 0.5 : note.velocity;
    }
    var fxArr = note.fx || [];
    var val = fxArr[paramIndex];
    if (typeof val === 'number') {
        return val;
    }
    if (typeof val === 'string' && val !== '' && val !== '--' && val !== '----') {
        var parsed = parseInt(val, 16);
        if (!isNaN(parsed)) {
            return parsed / 65535;
        }
    }
    return 0;
}

function setPianoNoteParamValue(note, paramIndex, value) {
    if (!note) return;
    if (paramIndex < 0) {
        note.velocity = value;
        return;
    }
    if (!note.fx) note.fx = [];
    while (note.fx.length <= paramIndex) {
        note.fx.push(0);
    }
    note.fx[paramIndex] = value;
}

function getPianoRollPoint(e, clamp) {
    var rect = pianoRoll.canvas.getBoundingClientRect();
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale;
    var y = (e.clientY - rect.top) / scale;
    if (clamp && pianoRoll.canvas) {
        var maxX = pianoRoll.canvas.width;
        var maxY = pianoRoll.canvas.height;
        x = Math.max(0, Math.min(maxX, x));
        y = Math.max(0, Math.min(maxY, y));
    }
    return { x: x, y: y };
}

function startPianoRollDocTracking() {
    if (pianoRoll.docTracking) return;
    document.addEventListener('mousemove', handlePianoRollMouseMove);
    document.addEventListener('mouseup', handlePianoRollMouseUp);
    pianoRoll.docTracking = true;
}

function stopPianoRollDocTracking() {
    if (!pianoRoll.docTracking) return;
    document.removeEventListener('mousemove', handlePianoRollMouseMove);
    document.removeEventListener('mouseup', handlePianoRollMouseUp);
    pianoRoll.docTracking = false;
}

function getVelocityCanvasPoint(e) {
    var rect = pianoRoll.velocityCanvas.getBoundingClientRect();
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale;
    var y = (e.clientY - rect.top) / scale;

    if (pianoRoll.velocityGrid) {
        x += pianoRoll.velocityGrid.scrollLeft;
    }

    return { x: x, y: y, height: rect.height / scale };
}

function applyVelocityToNotes(pattern, indices, y, height) {
    if (!pattern || pattern.type !== 'piano') return;
    if (!indices || indices.length === 0) return;

    var notes = pattern.notes || [];
    var v = velocityFromY(y, height);
    var paramIndex = getPianoParamIndex();
    for (var i = 0; i < indices.length; i++) {
        var idx = indices[i];
        if (notes[idx]) {
            setPianoNoteParamValue(notes[idx], paramIndex, v);
        }
    }
    markPatternNoteVizDirtyForPattern(pattern);
}

function handleVelocityMouseDown(e) {
    if (e.button !== 0) return;
    uiFocus = 'piano';

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var pt = getVelocityCanvasPoint(e);

    var indices = getVelocityTargetsAtX(pattern, pt.x);
    if (indices.length === 0) return;

    pianoRoll.velocityDragging = true;
    pianoRoll.velocityDragIndices = indices;

    pushUndo('piano-edit', captureStateForUndo('piano-edit'));

    applyVelocityToNotes(pattern, indices, pt.y, pt.height);
    scheduleRenderPianoRoll();
    e.preventDefault();
}

function handleVelocityMouseMove(e) {
    if (!pianoRoll.velocityCanvas) return;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var pt = getVelocityCanvasPoint(e);

    if (!pianoRoll.velocityDragging) {
        var hits = getVelocityTargetsAtX(pattern, pt.x);
        pianoRoll.velocityCanvas.style.cursor = hits.length > 0 ? 'ns-resize' : 'default';
        return;
    }

    applyVelocityToNotes(pattern, pianoRoll.velocityDragIndices || [], pt.y, pt.height);
    scheduleRenderPianoRoll();
    e.preventDefault();
}

function handleVelocityMouseUp() {
    if (!pianoRoll.velocityDragging) return;
    pianoRoll.velocityDragging = false;
    pianoRoll.velocityDragIndices = null;
    if (pianoRoll.velocityCanvas) {
        pianoRoll.velocityCanvas.style.cursor = 'default';
    }
}

// Find note at canvas position
function findPianoNoteAt(x, y) {
    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return { note: null, index: -1, edge: false };

    var notes = pattern.notes || [];
    var totalNotes = pianoRoll.octaves * 12;
    var clickBeat = x / pianoRoll.pixelsPerBeat;
    var clickRow = Math.floor(y / pianoRoll.noteHeight);
    var clickPitch = pianoRoll.lowestNote + (totalNotes - clickRow - 1);

    for (var i = notes.length - 1; i >= 0; i--) {  // Check from top (last drawn)
        var note = notes[i];
        if (!isNoteEvent(note)) continue;
        if (typeof note.duration !== 'number' || note.duration <= 0) continue;
        if (note.pitch !== clickPitch) continue;

        var noteStart = note.startBeat;
        var noteEnd = note.startBeat + note.duration;

        if (clickBeat >= noteStart && clickBeat <= noteEnd) {
            var noteEndX = noteEnd * pianoRoll.pixelsPerBeat;
            var isNearRightEdge = Math.abs(x - noteEndX) < 10;
            return { note: note, index: i, edge: isNearRightEdge };
        }
    }

    return { note: null, index: -1, edge: false };
}

function handlePianoRollMouseDown(e) {
    if (e.button !== 0) return;  // Left click only

    uiFocus = 'piano';
    var pt = getPianoRollPoint(e, true);
    var x = pt.x;
    var y = pt.y;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var totalNotes = pianoRoll.octaves * 12;
    var quantize = pianoRoll.quantize || 0.25;
    var clickBeat = x / pianoRoll.pixelsPerBeat;
    var snappedBeat = Math.max(0, Math.round(clickBeat / quantize) * quantize);
    var clickRow = Math.floor(y / pianoRoll.noteHeight);
    var clickPitch = pianoRoll.lowestNote + (totalNotes - clickRow - 1);
    pianoRoll.lastClickBeat = snappedBeat;
    pianoRoll.lastClickPitch = clickPitch;

    var found = findPianoNoteAt(x, y);
    var insertMode = e.ctrlKey;

    // Drag for selection box (when not inserting)
    if (!insertMode && !found.note) {
        pianoRoll.isDragging = true;
        pianoRoll.dragStartX = x;
        pianoRoll.dragStartY = y;
        pianoRoll.dragMode = 'select';
        pianoRoll.canvas.style.cursor = 'crosshair';
        pianoSelection.active = true;
        pianoSelection.startBeat = x / pianoRoll.pixelsPerBeat;
        pianoSelection.startPitch = pianoRoll.lowestNote + (pianoRoll.octaves * 12 - Math.floor(y / pianoRoll.noteHeight) - 1);
        if (!e.shiftKey) {
            pianoSelection.selectedNotes = [];
        }
        pianoRoll.drawPreviewPitch = null;
        startPianoRollDocTracking();
        scheduleRenderPianoRoll();
        return;
    }

    if (!insertMode && found.note) {
        var idx = pianoSelection.selectedNotes.indexOf(found.index);
        if (e.shiftKey) {
            if (idx >= 0) {
                pianoSelection.selectedNotes.splice(idx, 1);
            } else {
                pianoSelection.selectedNotes.push(found.index);
            }
        } else if (idx < 0) {
            pianoSelection.selectedNotes = [found.index];
        }

        pianoRoll.isDragging = true;
        pianoRoll.dragStartX = x;
        pianoRoll.dragStartY = y;
        pianoRoll.dragNote = found.note;
        pianoRoll.dragNoteIndex = found.index;
        pianoRoll.originalNoteData = {
            startBeat: found.note.startBeat,
            duration: found.note.duration,
            pitch: found.note.pitch
        };

        // Save undo state before modifying
        pushUndo('piano-edit', captureStateForUndo('piano-edit'));

        if (found.edge) {
            pianoRoll.dragMode = 'resize';
            pianoRoll.canvas.style.cursor = 'ew-resize';
        } else {
            pianoRoll.dragMode = 'move';
            pianoRoll.canvas.style.cursor = 'grabbing';
        }

        startPianoRollDocTracking();
        scheduleRenderPianoRoll();
        return;
    }

    if (!insertMode) {
        // Just set paste/position when not inserting; keep selection
        pianoRoll.drawPreviewPitch = null;
        scheduleRenderPianoRoll();
        return;
    }

    pianoRoll.isDragging = true;
    pianoRoll.dragStartX = x;
    pianoRoll.dragStartY = y;
    pianoRoll.dragMode = 'draw';
    pianoRoll.dragNote = null;
    pianoRoll.dragNoteIndex = -1;
    pianoSelection.selectedNotes = [];  // Clear selection on empty click
    if (clickPitch >= pianoRoll.lowestNote && clickPitch < pianoRoll.lowestNote + totalNotes) {
        pianoRoll.drawPreviewPitch = clickPitch;
        previewMidiNote(clickPitch, 100);
    } else {
        pianoRoll.drawPreviewPitch = null;
    }

    startPianoRollDocTracking();
    scheduleRenderPianoRoll();
}

function handlePianoRollMouseMove(e) {
    var pt = getPianoRollPoint(e, pianoRoll.isDragging);
    var x = pt.x;
    var y = pt.y;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    // Update cursor when not dragging
    if (!pianoRoll.isDragging) {
        if (e.ctrlKey) {
            pianoRoll.canvas.style.cursor = 'crosshair';
            return;
        }
        var found = findPianoNoteAt(x, y);
        if (found.note) {
            pianoRoll.canvas.style.cursor = found.edge ? 'ew-resize' : 'pointer';
        } else {
            pianoRoll.canvas.style.cursor = 'crosshair';
        }
        return;
    }

    var quantize = pianoRoll.quantize || 0.25;
    var totalNotes = pianoRoll.octaves * 12;

    // Selection box mode
    if (pianoRoll.dragMode === 'select') {
        pianoSelection.endBeat = x / pianoRoll.pixelsPerBeat;
        pianoSelection.endPitch = pianoRoll.lowestNote + (totalNotes - Math.floor(y / pianoRoll.noteHeight) - 1);
        scheduleRenderPianoRoll();
        return;
    }

    if (pianoRoll.dragMode === 'resize' && pianoRoll.dragNote) {
        // Resize note duration
        var newEndBeat = x / pianoRoll.pixelsPerBeat;
        var newDuration = newEndBeat - pianoRoll.dragNote.startBeat;
        newDuration = Math.max(quantize, Math.round(newDuration / quantize) * quantize);
        pianoRoll.dragNote.duration = newDuration;
        markPatternNoteVizDirtyForPattern(pattern);
        scheduleRenderPianoRoll();
    } else if (pianoRoll.dragMode === 'move' && pianoRoll.dragNote) {
        // Move note position and pitch
        var deltaX = x - pianoRoll.dragStartX;
        var deltaY = y - pianoRoll.dragStartY;

        var deltaBeat = deltaX / pianoRoll.pixelsPerBeat;
        var newStart = pianoRoll.originalNoteData.startBeat + deltaBeat;
        newStart = Math.max(0, Math.round(newStart / quantize) * quantize);

        var deltaRows = Math.round(deltaY / pianoRoll.noteHeight);
        var newPitch = pianoRoll.originalNoteData.pitch - deltaRows;
        newPitch = Math.max(pianoRoll.lowestNote, Math.min(pianoRoll.lowestNote + totalNotes - 1, newPitch));

        pianoRoll.dragNote.startBeat = newStart;
        pianoRoll.dragNote.pitch = newPitch;
        markPatternNoteVizDirtyForPattern(pattern);
        scheduleRenderPianoRoll();
    }
}

function handlePianoRollMouseUp(e) {
    if (!pianoRoll.isDragging) {
        stopPianoRollDocTracking();
        return;
    }
    if (e && e.type === 'mouseleave') return;

    var pt = getPianoRollPoint(e, true);
    var x = pt.x;
    var y = pt.y;

    var pattern = getCurrentPattern();
    var didChange = false;

    // Finalize selection box
    if (pianoRoll.dragMode === 'select' && pattern && pattern.type === 'piano') {
        var notes = pattern.notes || [];
        var minBeat = Math.min(pianoSelection.startBeat, pianoSelection.endBeat);
        var maxBeat = Math.max(pianoSelection.startBeat, pianoSelection.endBeat);
        var minPitch = Math.min(pianoSelection.startPitch, pianoSelection.endPitch);
        var maxPitch = Math.max(pianoSelection.startPitch, pianoSelection.endPitch);

        pianoSelection.selectedNotes = [];
        for (var i = 0; i < notes.length; i++) {
            var n = notes[i];
            var noteEnd = n.startBeat + n.duration;
            // Check if note intersects selection box
            if (n.startBeat < maxBeat && noteEnd > minBeat && n.pitch >= minPitch && n.pitch <= maxPitch) {
                pianoSelection.selectedNotes.push(i);
            }
        }
        pianoSelection.active = false;
        consoleLog('Selected ' + pianoSelection.selectedNotes.length + ' notes');
    } else if (pianoRoll.dragMode === 'draw' && pattern && pattern.type === 'piano') {
        // Create new note
        var quantize = pianoRoll.quantize || 0.25;
        var totalNotes = pianoRoll.octaves * 12;

        var beat = x / pianoRoll.pixelsPerBeat;
        beat = Math.max(0, Math.round(beat / quantize) * quantize);

        var row = Math.floor(y / pianoRoll.noteHeight);
        var pitch = pianoRoll.lowestNote + (totalNotes - row - 1);

        if (pitch >= pianoRoll.lowestNote && pitch < pianoRoll.lowestNote + totalNotes) {
            // Save undo state
            pushUndo('piano-edit', captureStateForUndo('piano-edit'));

            var newNote = {
                type: 'note',
                pitch: pitch,
                startBeat: beat,
                duration: quantize,
                velocity: 0.8
            };

            if (!pattern.notes) pattern.notes = [];
            pattern.notes.push(newNote);
            didChange = true;

            // Preview the note
            if (pianoRoll.drawPreviewPitch === null) {
                previewMidiNote(pitch, Math.floor(newNote.velocity * 127));
            }
        }
    } else if (pianoRoll.dragMode === 'resize' || pianoRoll.dragMode === 'move') {
        // Auto-extend pattern if note goes beyond
        if (pianoRoll.dragNote && pattern) {
            var noteEnd = pianoRoll.dragNote.startBeat + pianoRoll.dragNote.duration;
            if (noteEnd > pattern.beats) {
                pattern.beats = Math.ceil(noteEnd);
                renderTimeline();
                didChange = true;
            }
        }
        if (pianoRoll.dragNote) {
            didChange = true;
        }
    }

    // Reset drag state
    pianoRoll.isDragging = false;
    pianoRoll.dragMode = null;
    pianoRoll.dragNote = null;
    pianoRoll.dragNoteIndex = -1;
    pianoRoll.originalNoteData = null;
    pianoRoll.canvas.style.cursor = 'crosshair';

    if (pianoRoll.drawPreviewPitch !== null) {
        stopMidiNote(pianoRoll.drawPreviewPitch);
        pianoRoll.drawPreviewPitch = null;
    }

    if (didChange && pattern) {
        markPatternNoteVizDirtyForPattern(pattern);
    }

    scheduleRenderPianoRoll();
    stopPianoRollDocTracking();
}

function handlePianoRollContextMenu(e) {
    e.preventDefault();
    uiFocus = 'piano';

    var menu = document.getElementById('piano-roll-context-menu');
    if (!menu) return;

    var rect = pianoRoll.canvas.getBoundingClientRect();
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale;
    var y = (e.clientY - rect.top) / scale;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var totalNotes = pianoRoll.octaves * 12;
    var quantize = pianoRoll.quantize || 0.25;
    var clickBeat = x / pianoRoll.pixelsPerBeat;
    var snappedBeat = Math.max(0, Math.round(clickBeat / quantize) * quantize);
    var clickRow = Math.floor(y / pianoRoll.noteHeight);
    var clickPitch = pianoRoll.lowestNote + (totalNotes - clickRow - 1);
    pianoRoll.lastClickBeat = snappedBeat;
    pianoRoll.lastClickPitch = clickPitch;
    pianoContextState.beat = snappedBeat;
    pianoContextState.pitch = clickPitch;

    var found = findPianoNoteAt(x, y);
    if (found.note && found.index !== -1) {
        if (pianoSelection.selectedNotes.indexOf(found.index) < 0) {
            pianoSelection.selectedNotes = [found.index];
        }
    }

    menu.classList.add('visible');
    positionMenuAtClient(menu, e.clientX, e.clientY);

    var submenu = menu.querySelector('.context-submenu[data-menu="quantize"]');
    var quantizeItem = menu.querySelector('.context-menu-item.has-submenu[data-action="quantize"]');
    if (submenu && quantizeItem) {
        quantizeItem.classList.remove('open');
        submenu.style.top = quantizeItem.offsetTop + 'px';
        submenu.style.left = menu.offsetWidth + 6 + 'px';
    }
}

function quantizeBeat(beat) {
    if (state.quantize === 'off') return beat;

    var grid = getQuantizeGrid();
    return Math.round(beat / grid) * grid;
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
        setCellValue(step, noteCol, 0, 'note', midiToNoteName(pitch));
        setCellValue(step, noteCol, 0, 'amp', 'FF');
        invalidatePatternCache(getCurrentPatternIndex());
        renderTrackerGrid(true);
    }
}

function zoomPianoRoll(factor) {
    pianoRoll.pixelsPerBeat = Math.max(10, Math.min(200, pianoRoll.pixelsPerBeat * factor));
    scheduleRenderPianoRoll();
}

function hidePianoRollContextMenu() {
    var menu = document.getElementById('piano-roll-context-menu');
    if (menu) menu.classList.remove('visible');
}

function getSelectedPianoNoteIndices() {
    if (pianoSelection.selectedNotes.length > 0) return pianoSelection.selectedNotes.slice();
    if (pianoRoll.dragNoteIndex >= 0) return [pianoRoll.dragNoteIndex];
    return [];
}

function insertPianoNoteAt(pattern, beat, pitch) {
    if (!pattern || pattern.type !== 'piano') return;

    var quantize = pianoRoll.quantize || 0.25;
    var totalNotes = pianoRoll.octaves * 12;
    var snappedBeat = Math.max(0, Math.round(beat / quantize) * quantize);

    if (pitch < pianoRoll.lowestNote || pitch >= pianoRoll.lowestNote + totalNotes) return;

    pushUndo('piano-edit', captureStateForUndo('piano-edit'));

    var newNote = {
        type: 'note',
        pitch: pitch,
        startBeat: snappedBeat,
        duration: quantize,
        velocity: 0.8
    };

    if (!pattern.notes) pattern.notes = [];
    pattern.notes.push(newNote);
    pianoSelection.selectedNotes = [pattern.notes.length - 1];
    pianoRoll.lastClickBeat = snappedBeat;
    pianoRoll.lastClickPitch = pitch;

    markPatternNoteVizDirtyForPattern(pattern);
    scheduleRenderPianoRoll();
}

function handlePianoRollDblClick(e) {
    if (e.button !== 0) return;
    uiFocus = 'piano';

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var pt = getPianoRollPoint(e, true);
    var totalNotes = pianoRoll.octaves * 12;
    var beat = pt.x / pianoRoll.pixelsPerBeat;
    var row = Math.floor(pt.y / pianoRoll.noteHeight);
    var pitch = pianoRoll.lowestNote + (totalNotes - row - 1);

    insertPianoNoteAt(pattern, beat, pitch);
}

function quantizePianoNotes(grid) {
    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return;

    var indices = getSelectedPianoNoteIndices();
    if (indices.length === 0) {
        consoleLog('No notes selected');
        return;
    }

    var quantize = Math.max(0.0001, grid || 0.25);
    pushUndo('piano-edit', captureStateForUndo('piano-edit'));

    var maxEnd = pattern.beats || 0;
    for (var i = 0; i < indices.length; i++) {
        var idx = indices[i];
        var note = pattern.notes[idx];
        if (!note || !isNoteEvent(note)) continue;

        var start = note.startBeat || 0;
        var end = start + (note.duration || quantize);
        var qStart = Math.round(start / quantize) * quantize;
        var qEnd = Math.round(end / quantize) * quantize;

        if (qEnd <= qStart + 0.0001) qEnd = qStart + quantize;

        note.startBeat = Math.max(0, qStart);
        note.duration = Math.max(quantize, qEnd - note.startBeat);

        var noteEnd = note.startBeat + note.duration;
        if (noteEnd > maxEnd) maxEnd = noteEnd;
    }

    if (maxEnd > pattern.beats) {
        pattern.beats = Math.ceil(maxEnd);
        pattern.steps = pattern.beats * (pattern.lpb || state.lpb);
    }

    markPatternNoteVizDirtyForPattern(pattern);
    scheduleRenderPianoRoll();
    consoleLog('Quantized ' + indices.length + ' note(s)');
}

function handlePianoRollContextAction(action, grid) {
    hidePianoRollContextMenu();
    uiFocus = 'piano';

    if (action === 'copy') {
        copySelection();
        return;
    }
    if (action === 'cut') {
        cutSelection();
        return;
    }
    if (action === 'paste') {
        pasteSelection();
        return;
    }
    if (action === 'delete') {
        deleteSelection();
        return;
    }
    if (action === 'quantize') {
        quantizePianoNotes(grid);
    }
}

// Track active MIDI preview notes per track
var activeMidiPreviews = {};

function previewMidiNote(midiNote, velocity) {
    if (!state.csoundReady) return;

    var freq = 440 * Math.pow(2, (midiNote - 69) / 12);
    var amp = velocity / 127;
    var trackKey = state.selectedTrack;

    // Get instrument from current pattern, or default to track+1
    var pattern = getCurrentPattern();
    var baseInstr = (pattern && pattern.instrument) ? pattern.instrument : (state.selectedTrack + 1);

    // Use unique fractional instance per MIDI note: instrNum.midiNote (e.g., 1.060 for middle C)
    var instrNum = baseInstr + '.' + midiNote.toString().padStart(3, '0');

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
var midiNoteStartBeats = {};  // Track note start beats for piano roll recording
var recordingPreviewBeats = 0;  // Live preview of pattern expansion during recording
var lastRecordingPreviewBeats = 0;  // Track changes to avoid excessive re-renders
var recordingPreviewTimer = null;  // Timer for non-playback recording preview updates

function applyRecordingPreviewToClip(pattern, clip) {
    if (!state.isRecording) return false;
    if (!pattern || !clip) return false;
    if (clip.loopCount !== undefined && clip.loopCount > 1.0001) return false;
    if (!recordingPreviewBeats || recordingPreviewBeats <= 0) return false;

    var baseLoopLen = getClipLoopLength(clip, pattern);
    if (recordingPreviewBeats <= baseLoopLen + 0.0001) return false;

    if ((pattern.beats || 0) < recordingPreviewBeats - 0.0001) {
        // Expand actual pattern length (also updates clip loopLength)
        applyPatternLengthWithBuffer(pattern, clip, recordingPreviewBeats);
    } else {
        clip.loopLength = recordingPreviewBeats;
        clip.loopCount = 1;
    }

    autoExtendTimeline();
    return true;
}

function startPianoRollRecordNote(pitch, velocity) {
    if (!state.isRecording) return false;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') return false;

    var quantizeBeats = pianoRoll.quantize || 0.25;
    var startBeat;

    if (state.isPlaying) {
        var clip = getSelectedClip();
        var relBeat = getPlaybackBeatNow() - (clip ? clip.startBeat : 0);
        startBeat = Math.round(relBeat / quantizeBeats) * quantizeBeats;
    } else {
        if (pattern.notes && pattern.notes.length > 0) {
            startBeat = Math.max.apply(null, pattern.notes.map(function(n) { return n.startBeat + n.duration; }));
        } else {
            startBeat = 0;
        }
        startBeat = Math.round(startBeat / quantizeBeats) * quantizeBeats;
    }

    startBeat = Math.max(0, startBeat);
    midiNoteStartBeats[pitch] = {
        beat: startBeat,
        velocity: velocity,
        startTime: performance.now()
    };
    return true;
}

function finishPianoRollRecordNote(pitch) {
    if (!state.isRecording) return false;

    var startInfo = midiNoteStartBeats[pitch];
    if (!startInfo) return false;

    var pattern = getCurrentPattern();
    if (!pattern || pattern.type !== 'piano') {
        delete midiNoteStartBeats[pitch];
        return false;
    }

    var quantizeBeats = pianoRoll.quantize || 0.25;
    var duration;

    if (state.isPlaying) {
        var clip = getSelectedClip();
        var currentRelativeBeat = getPlaybackBeatNow() - (clip ? clip.startBeat : 0);
        var endBeat = Math.round(currentRelativeBeat / quantizeBeats) * quantizeBeats;
        duration = Math.max(quantizeBeats, endBeat - startInfo.beat);
    } else {
        var elapsedMs = performance.now() - startInfo.startTime;
        var elapsedBeats = (elapsedMs / 1000) * (state.bpm / 60);
        duration = Math.max(quantizeBeats, Math.round(elapsedBeats / quantizeBeats) * quantizeBeats);
    }

    var noteEndBeat = startInfo.beat + duration;
    var clip = getSelectedClip();
    var baseBeats = getClipLoopLength(clip, pattern) || (pattern.beats || 0);
    if (noteEndBeat > baseBeats) {
        var newBeats = Math.ceil(noteEndBeat / 4) * 4;
        if (clip && (clip.loopCount === undefined || clip.loopCount <= 1.0001)) {
            if ((pattern.beats || 0) < newBeats - 0.0001) {
                applyPatternLengthWithBuffer(pattern, clip, newBeats);
            } else {
                clip.loopLength = newBeats;
                clip.loopCount = 1;
            }
        } else if ((pattern.beats || 0) < newBeats - 0.0001) {
            applyPatternLengthWithBuffer(pattern, clip, newBeats);
        }
        consoleLog('Extended pattern to ' + newBeats + ' beats');
        renderTimeline();
    }

    pushUndo('piano-edit', captureStateForUndo('piano-edit'));
    if (!pattern.notes) pattern.notes = [];
    pattern.notes.push({
        type: 'note',
        pitch: pitch,
        startBeat: startInfo.beat,
        duration: duration,
        velocity: (startInfo.velocity || 100) / 127
    });

    markPatternNoteVizDirtyForPattern(pattern);
    scheduleRenderPianoRoll();
    consoleLog('Recorded note ' + midiToNoteName(pitch) + ' at beat ' + startInfo.beat.toFixed(2));

    delete midiNoteStartBeats[pitch];
    return true;
}

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
        var pattern = getCurrentPattern();

        // Check if current pattern is a piano roll
        if (pattern && pattern.type === 'piano') {
            startPianoRollRecordNote(note, velocity);
        } else if (pattern && pattern.type !== 'piano') {
            // Record to tracker pattern
            var noteName = midiToNoteName(note);
            var ampHex = Math.round(velocity / 127 * 255).toString(16).toUpperCase().padStart(2, '0');
            var noteCol = state.focusedNoteCol || 0;
            var step = state.focusedStep;

            if (step < pattern.steps) {
                setCellValue(step, noteCol, 0, 'note', noteName);
                setCellValue(step, noteCol, 0, 'amp', ampHex);

                invalidatePatternCache(getCurrentPatternIndex());
                renderTrackerGrid(true);

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

    // Complete piano roll recording if we have a start beat tracked
    if (state.isRecording) {
        finishPianoRollRecordNote(note);
    }

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
            var fxIdx = mapping.fxColumn || 0;
            var hexVal = value.toString(16).toUpperCase().padStart(4, '0');
            setCellValue(step, noteCol, fxIdx, 'fx', hexVal);
            invalidatePatternCache(getCurrentPatternIndex());
            renderTrackerGrid(true);
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
                deleteSampleSelection();
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
    // Handle main view tabs (song/sample)
    var tabs = document.querySelectorAll('.editor-view-tab');
    tabs.forEach(function(t) {
        var tabView = t.getAttribute('data-view');
        t.classList.toggle('active', tabView === view);
    });

    // Main views: song-editor-view vs sample-editor-view (pattern editor hidden in sample view)
    var sampleView = document.getElementById('sample-editor-view');
    var songEditorView = document.getElementById('song-editor-view');
    var songInfoView = document.getElementById('song-info-view');
    var patternEditorArea = document.getElementById('pattern-editor-area');
    var editorSplitter = document.getElementById('editor-splitter');

    if (sampleView) sampleView.classList.toggle('hidden', view !== 'sample');
    if (songEditorView) songEditorView.classList.toggle('hidden', view !== 'song');
    if (songInfoView) songInfoView.classList.toggle('hidden', view !== 'info');
    if (patternEditorArea) patternEditorArea.classList.toggle('hidden', view === 'sample');
    if (editorSplitter) editorSplitter.classList.toggle('hidden', view === 'sample');

    if (view === 'song' || view === 'info') {
        clampPatternEditorToView();
        updatePatternToggleButton();
    }

    // Resize and render waveform when switching to sample view
    if (view === 'sample' && sampleEditor.audioBuffer) {
        setTimeout(function() {
            resizeCanvas();
            renderWaveform();
        }, 50);
    }
}

function initSongInfo() {
    var infoEl = document.getElementById('song-info-text');
    if (!infoEl) return;

    infoEl.value = state.songInfo || '';

    infoEl.addEventListener('input', function() {
        state.songInfo = this.value;
    });
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
    var canvasStyles = window.getComputedStyle(sampleEditor.canvas);
    var padX = parseFloat(canvasStyles.paddingLeft || 0) + parseFloat(canvasStyles.paddingRight || 0);
    var padY = parseFloat(canvasStyles.paddingTop || 0) + parseFloat(canvasStyles.paddingBottom || 0);
    var width = Math.max(1, container.clientWidth - padX);
    var height = Math.max(1, container.clientHeight - padY);

    sampleEditor.canvas.width = width;
    sampleEditor.canvas.height = height;
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
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale;
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
    var scale = getUiScale();
    var x = (e.clientX - rect.left) / scale;
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
    var scale = getUiScale();
    var mouseX = (e.clientX - rect.left) / scale;
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
async function deleteSampleSelection() {
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

function updateUiScale() {
    var scale = 2 / 3;
    document.documentElement.style.setProperty('--ui-scale', scale.toFixed(3));
    clampPatternEditorToView();
}

function getUiScale() {
    var scale = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--ui-scale'));
    if (!isFinite(scale) || scale <= 0) return 1;
    return scale;
}

function getScaledClientX(e) {
    return e.clientX / getUiScale();
}

function getScaledClientY(e) {
    return e.clientY / getUiScale();
}

function getScaledOffsetInElement(e, el) {
    var rect = el.getBoundingClientRect();
    var scale = getUiScale();
    return {
        x: (e.clientX - rect.left) / scale,
        y: (e.clientY - rect.top) / scale
    };
}

function positionMenuAtClient(menu, clientX, clientY) {
    if (!menu) return;
    var scale = getUiScale();
    var x = clientX / scale;
    var y = clientY / scale;

    menu.style.left = x + 'px';
    menu.style.top = y + 'px';

    var rect = menu.getBoundingClientRect();
    if (rect.right > window.innerWidth) {
        var overflowX = rect.right - window.innerWidth;
        menu.style.left = (x - overflowX / scale) + 'px';
    }
    if (rect.bottom > window.innerHeight) {
        var overflowY = rect.bottom - window.innerHeight;
        menu.style.top = (y - overflowY / scale) + 'px';
    }
}

// ============================================
// PATTERN EDITOR RESIZE / COLLAPSE
// ============================================

var patternResizeState = {
    active: false,
    startY: 0,
    startPatternHeight: 0,
    lastPatternHeight: null,
    minPatternHeight: 120,
    minSongHeight: 160,
    splitterHeight: 6
};

function clampPatternHeight(height) {
    var center = document.querySelector('.center-panel');
    var splitter = document.getElementById('editor-splitter');
    if (!center) return height;
    var totalHeight = center.clientHeight;
    var tabs = document.querySelector('.editor-view-tabs');
    var reserved = tabs ? tabs.offsetHeight : 0;
    var availableHeight = Math.max(0, totalHeight - reserved);
    var splitterHeight = splitter ? splitter.offsetHeight : patternResizeState.splitterHeight;
    var maxPattern = Math.max(patternResizeState.minPatternHeight, availableHeight - splitterHeight - patternResizeState.minSongHeight);
    return Math.max(patternResizeState.minPatternHeight, Math.min(maxPattern, height));
}

function setPatternCollapsed(collapsed) {
    var patternArea = document.getElementById('pattern-editor-area');
    var splitter = document.getElementById('editor-splitter');
    if (!patternArea || !splitter) return;

    if (collapsed) {
        if (!patternArea.classList.contains('collapsed')) {
            patternResizeState.lastPatternHeight = patternArea.offsetHeight || patternResizeState.lastPatternHeight || 280;
        }
        patternArea.classList.add('collapsed');
        patternArea.style.height = '0px';
    } else {
        patternArea.classList.remove('collapsed');
        var restoreHeight = patternResizeState.lastPatternHeight || 280;
        var clamped = clampPatternHeight(restoreHeight);
        patternArea.style.height = clamped + 'px';
        patternResizeState.lastPatternHeight = clamped;
    }
    updatePatternToggleButton();
}

function togglePatternCollapse() {
    var patternArea = document.getElementById('pattern-editor-area');
    if (!patternArea || patternArea.classList.contains('hidden')) return;
    var collapsed = patternArea.classList.contains('collapsed');
    setPatternCollapsed(!collapsed);
}

function updatePatternToggleButton() {
    var button = document.getElementById('pattern-toggle-btn');
    var patternArea = document.getElementById('pattern-editor-area');
    if (!button || !patternArea) return;
    var collapsed = patternArea.classList.contains('collapsed');
    button.textContent = collapsed ? 'Show Pattern' : 'Hide Pattern';
}

function clampPatternEditorToView() {
    var patternArea = document.getElementById('pattern-editor-area');
    if (!patternArea || patternArea.classList.contains('hidden') || patternArea.classList.contains('collapsed')) return;
    var currentHeight = patternArea.offsetHeight || 0;
    var clamped = clampPatternHeight(currentHeight);
    if (Math.abs(clamped - currentHeight) > 0.5) {
        patternArea.style.height = clamped + 'px';
        patternResizeState.lastPatternHeight = clamped;
    }
}

function initPatternResizer() {
    var splitter = document.getElementById('editor-splitter');
    var patternArea = document.getElementById('pattern-editor-area');
    var toggleBtn = document.getElementById('pattern-toggle-btn');
    if (!splitter || !patternArea) return;

    patternResizeState.lastPatternHeight = patternArea.offsetHeight || patternResizeState.lastPatternHeight;
    updatePatternToggleButton();

    splitter.addEventListener('mousedown', function(e) {
        if (e.button !== 0) return;
        if (patternArea.classList.contains('hidden')) return;
        e.preventDefault();

        setPatternCollapsed(false);

        patternResizeState.active = true;
        patternResizeState.startY = getScaledClientY(e);
        patternResizeState.startPatternHeight = patternArea.offsetHeight;
        patternResizeState.splitterHeight = splitter.offsetHeight || patternResizeState.splitterHeight;

        document.body.style.cursor = 'row-resize';
        document.addEventListener('mousemove', onPatternResizeMove);
        document.addEventListener('mouseup', onPatternResizeUp);
    });

    splitter.addEventListener('dblclick', function(e) {
        e.preventDefault();
        togglePatternCollapse();
    });

    if (toggleBtn) {
        toggleBtn.addEventListener('click', function(e) {
            e.preventDefault();
            togglePatternCollapse();
        });
    }
}

function onPatternResizeMove(e) {
    if (!patternResizeState.active) return;
    var patternArea = document.getElementById('pattern-editor-area');
    if (!patternArea) return;

    var deltaY = getScaledClientY(e) - patternResizeState.startY;
    var newHeight = patternResizeState.startPatternHeight - deltaY;
    newHeight = clampPatternHeight(newHeight);

    patternArea.style.height = newHeight + 'px';
    patternResizeState.lastPatternHeight = newHeight;
}

function onPatternResizeUp() {
    if (!patternResizeState.active) return;
    patternResizeState.active = false;
    document.body.style.cursor = '';
    document.removeEventListener('mousemove', onPatternResizeMove);
    document.removeEventListener('mouseup', onPatternResizeUp);
}

// ============================================
// INITIALIZATION
// ============================================

function init() {
    cacheDOMReferences();
    updateUiScale();
    window.addEventListener('resize', updateUiScale);

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
    initSongInfo();
    initPatternResizer();
    attachCodeEditorShortcuts();
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

        // Click on ruler to set playback position
        var rulerEl = document.getElementById('timeline-ruler');
        if (rulerEl) {
            rulerEl.addEventListener('click', function(e) {
                var timelineContainer = document.getElementById('timeline-tracks');
                if (!timelineContainer) return;
                var beat = getTimelineBeatFromClientX(e.clientX, timelineContainer);
                state.currentBeat = beat;
                var cursorTrack = state.selectedTrack >= 0 ? state.selectedTrack : 0;
                updateTimelineCursor(beat, cursorTrack);
                var playhead = document.getElementById('timeline-playhead');
                if (playhead) {
                    playhead.style.display = 'block';
                    playhead.style.left = (beat * timelinePixelsPerBeat) + 'px';
                }
                updateTimelinePlayhead();
            });
        }

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
                middleMouseZoom.startX = getScaledClientX(e);
                middleMouseZoom.startZoom = timelinePixelsPerBeat;
            }
        });
        document.addEventListener('mousemove', function(e) {
            if (middleMouseZoom.active) {
                var delta = getScaledClientX(e) - middleMouseZoom.startX;
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

    // Piano roll context menu
    var pianoContextMenu = document.getElementById('piano-roll-context-menu');
    if (pianoContextMenu) {
        pianoContextMenu.addEventListener('click', function(e) {
            var item = e.target.closest('.context-menu-item');
            if (!item) return;
            var action = item.getAttribute('data-action');
            if (!action) return;
            if (item.classList.contains('has-submenu')) {
                item.classList.toggle('open');
                return;
            }
            if (action === 'quantize') {
                var grid = parseFloat(item.getAttribute('data-grid'));
                if (!isNaN(grid)) {
                    handlePianoRollContextAction(action, grid);
                }
                return;
            }
            handlePianoRollContextAction(action);
        });
    }

    // Hide context menus on click elsewhere
    document.addEventListener('click', function(e) {
        if (!e.target.closest('#timeline-context-menu')) {
            hideTimelineContextMenu();
        }
        if (!e.target.closest('#piano-roll-context-menu')) {
            hidePianoRollContextMenu();
        }
        if (!e.target.closest('#code-editor-context-menu')) {
            hideCodeEditorContextMenu();
        }
    });

    document.getElementById('btn-compile').addEventListener('click', compileInstruments);

    // ============================================
    // DROPDOWN MENUS
    // ============================================
    // Toggle dropdowns on click
    document.querySelectorAll('.dropdown-toggle').forEach(function(toggle) {
        toggle.addEventListener('click', function(e) {
            e.stopPropagation();
            var dropdown = this.parentElement;
            var wasOpen = dropdown.classList.contains('open');

            // Close all dropdowns
            document.querySelectorAll('.dropdown').forEach(function(d) {
                d.classList.remove('open');
            });

            // Toggle this one
            if (!wasOpen) {
                dropdown.classList.add('open');
            }
        });
    });

    // Close dropdowns when clicking outside
    document.addEventListener('click', function(e) {
        if (!e.target.closest('.dropdown')) {
            document.querySelectorAll('.dropdown').forEach(function(d) {
                d.classList.remove('open');
            });
        }
    });

    // File menu items
    var menuNew = document.getElementById('menu-new');
    if (menuNew) {
        menuNew.addEventListener('click', function() {
            if (confirm('Create a new song? Unsaved changes will be lost.')) {
                location.reload();
            }
        });
    }

    var menuSave = document.getElementById('menu-save');
    if (menuSave) {
        menuSave.addEventListener('click', saveSong);
    }

    var menuSaveAs = document.getElementById('menu-save-as');
    if (menuSaveAs) {
        menuSaveAs.addEventListener('click', function() {
            var name = prompt('Enter song name:', 'mysong');
            if (name) {
                saveSongAs(name);
            }
        });
    }

    var menuLoad = document.getElementById('menu-load');
    if (menuLoad) {
        menuLoad.addEventListener('click', function() {
            document.getElementById('file-input').click();
        });
    }

    var menuExportCsd = document.getElementById('menu-export-csd');
    if (menuExportCsd) {
        menuExportCsd.addEventListener('click', exportCSD);
    }

    // Edit menu items
    var menuUndo = document.getElementById('menu-undo');
    if (menuUndo) {
        menuUndo.addEventListener('click', undo);
    }

    var menuRedo = document.getElementById('menu-redo');
    if (menuRedo) {
        menuRedo.addEventListener('click', redo);
    }

    var menuCut = document.getElementById('menu-cut');
    if (menuCut) {
        menuCut.addEventListener('click', cutSelection);
    }

    var menuCopy = document.getElementById('menu-copy');
    if (menuCopy) {
        menuCopy.addEventListener('click', copySelection);
    }

    var menuPaste = document.getElementById('menu-paste');
    if (menuPaste) {
        menuPaste.addEventListener('click', pasteSelection);
    }

    var menuSelectAll = document.getElementById('menu-select-all');
    if (menuSelectAll) {
        menuSelectAll.addEventListener('click', selectAll);
    }

    // Demo buttons - load 1.cst, 2.cst, 3.cst, 4.cst
    var demoBtns = document.querySelectorAll('.demo-btn');
    demoBtns.forEach(function(btn) {
        btn.addEventListener('click', function() {
            var demoNum = this.getAttribute('data-demo');
            loadDemo(demoNum);
            // Close dropdown
            document.querySelectorAll('.dropdown').forEach(function(d) {
                d.classList.remove('open');
            });
        });
    });

    document.getElementById('btn-toggle-console').addEventListener('click', function() {
        var consoleEl = document.getElementById('console');
        var isHidden = consoleEl.style.display === 'none';
        consoleEl.style.display = isHidden ? 'block' : 'none';
        this.textContent = isHidden ? 'Hide' : 'Show';
    });

    // Mobile: Toggle code editor panel
    var btnToggleEditor = document.getElementById('btn-toggle-editor');
    if (btnToggleEditor) {
        btnToggleEditor.addEventListener('click', function() {
            var editorContainer = document.getElementById('editor-container');
            if (editorContainer) {
                editorContainer.classList.toggle('collapsed');
            }
        });
    }

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

    // Code editor context menu
    document.getElementById('code-editor').addEventListener('contextmenu', handleCodeEditorContextMenu);
    document.getElementById('code-editor-context-menu').addEventListener('click', function(e) {
        var action = e.target.getAttribute('data-action');
        if (action) handleCodeEditorContextAction(action);
    });

    consoleLog('Keys: z-]/q-]=notes, Arrows=nav, Tab=OFF, `=rec, Ctrl+C/X/V=copy/cut/paste');

    // Initialize Csound 7
    initCsound();
}

if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
} else {
    init();
}
