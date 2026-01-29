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

// Default instruments for each of the 16 tracks + 16 placeholder instruments (17-32)
var defaultInstruments = [
    `instr 1
imeow init 4
print imeow
endin`,
    `instr 2
endin`,
    `instr 3
endin`,
    `instr 4
endin`,
    `instr 5
endin`,
    `instr 6
endin`,
    `instr 7
endin`,
    `instr 8
endin`,
    `instr 9
endin`,
    `instr 10
endin`,
    `instr 11
endin`,
    `instr 12
endin`,
    `instr 13
endin`,
    `instr 14
endin`,
    `instr 15
endin`,
    `instr 16
endin`,
    // Placeholder instruments (17-32) - no tracks, accessible via "More" button
    `instr 17
endin`,
    `instr 18
endin`,
    `instr 19
endin`,
    `instr 20
endin`,
    `instr 21
endin`,
    `instr 22
endin`,
    `instr 23
endin`,
    `instr 24
endin`,
    `instr 25
endin`,
    `instr 26
endin`,
    `instr 27
endin`,
    `instr 28
endin`,
    `instr 29
endin`,
    `instr 30
endin`,
    `instr 31
endin`,
    `instr 32
endin`
];

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

// Tracker state
var state = {
    csoundReady: false,
    isPlaying: false,
    isRecording: false,
    currentStep: 0,
    bpm: 120,
    lpb: 4,
    editStep: 1,
    patterns: [],
    sequence: [0],
    currentSequenceIndex: 0,
    tracks: [],
    trackMutes: new Array(16).fill(false),
    trackSolos: new Array(16).fill(false),
    instruments: defaultInstruments.slice(),
    currentInstrument: 0,
    opcodes: '',
    samples: [],
    playInterval: null,
    baseOctave: 3,
    focusedTrack: 0,
    focusedColumn: 0,
    focusedStep: 0,
    focusedType: 'note',
    activeNotes: new Array(16).fill(null).map(() => ({}))
};

// DOM cache
var domCache = {};

// Pattern grid cache
var patternGridCache = {};
var currentGridPatternIndex = -1;

// Playback timing
var pendingVisualUpdate = null;
var lastPlayedStep = -1;
var lastPlayedSeqIndex = -1;

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
    startTrack: -1,
    startStep: -1,
    startAbsCol: -1,  // Absolute column index (0 = note0, 1 = amp0, 2 = note1, 3 = amp1, ... then fx columns)
    endTrack: -1,
    endStep: -1,
    endAbsCol: -1,
    // Keep type/col for compatibility
    startCol: -1,
    startType: null,
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
    for (var i = 0; i < 16; i++) {
        state.tracks.push({
            noteColumns: 1,
            fxColumns: 1,
            name: 'Track ' + (i + 1)
        });
    }
}

function createEmptyPattern(steps) {
    var pattern = {
        steps: steps,
        data: new Array(16)
    };
    for (var track = 0; track < 16; track++) {
        pattern.data[track] = new Array(steps);
        for (var step = 0; step < steps; step++) {
            pattern.data[track][step] = {
                notes: [{ note: '', amp: '' }],
                fx: ['']
            };
        }
    }
    return pattern;
}

function initPatterns() {
    state.patterns = [createEmptyPattern(64)];
    state.sequence = [0];
    state.currentSequenceIndex = 0;
}

function getCurrentPattern() {
    var patternIndex = state.sequence[state.currentSequenceIndex];
    return state.patterns[patternIndex];
}

function getCurrentPatternIndex() {
    return state.sequence[state.currentSequenceIndex];
}

// ============================================
// SEQUENCE SIDEBAR
// ============================================

function renderSequenceSidebar() {
    var list = document.getElementById('sequence-list');
    list.innerHTML = '';

    for (var i = 0; i < state.sequence.length; i++) {
        var item = document.createElement('div');
        item.className = 'sequence-item';
        item.setAttribute('data-seq-index', i);
        item.textContent = (state.sequence[i] + 1);

        if (i === state.currentSequenceIndex) {
            item.classList.add('selected');
        }

        item.draggable = true;
        item.addEventListener('click', handleSequenceClick);
        item.addEventListener('dragstart', handleSequenceDragStart);
        item.addEventListener('dragover', handleSequenceDragOver);
        item.addEventListener('dragleave', handleSequenceDragLeave);
        item.addEventListener('drop', handleSequenceDrop);
        item.addEventListener('dragend', handleSequenceDragEnd);

        list.appendChild(item);
    }

    var poolList = document.getElementById('pattern-pool-list');
    poolList.innerHTML = '';

    for (var i = 0; i < state.patterns.length; i++) {
        var poolItem = document.createElement('div');
        poolItem.className = 'pool-item';
        poolItem.setAttribute('data-pattern-index', i);
        poolItem.textContent = 'P' + (i + 1) + ' (' + state.patterns[i].steps + ')';
        poolItem.draggable = true;
        poolItem.addEventListener('dragstart', handlePoolDragStart);
        poolList.appendChild(poolItem);
    }
}

var draggedSeqIndex = null;
var draggedPatternIndex = null;

function handleSequenceClick(e) {
    var index = parseInt(e.target.getAttribute('data-seq-index'));
    state.currentSequenceIndex = index;
    state.currentStep = 0;

    // If playing, jump to this pattern in the playback
    if (state.isPlaying && audioCtx) {
        // Reset timing to start playing from this pattern
        playbackStartTime = audioCtx.currentTime;
        nextStepTime = audioCtx.currentTime;
        lastPlayedStep = -1;
        lastPlayedSeqIndex = -1;
    }

    document.getElementById('step-count').value = getCurrentPattern().steps;
    renderSequenceSidebar();
    renderTrackerGrid();
}

function handleSequenceDragStart(e) {
    draggedSeqIndex = parseInt(e.target.getAttribute('data-seq-index'));
    e.target.style.opacity = '0.5';
}

function handleSequenceDragOver(e) {
    e.preventDefault();
    e.target.classList.add('drag-over');
}

function handleSequenceDragLeave(e) {
    e.target.classList.remove('drag-over');
}

function handleSequenceDrop(e) {
    e.preventDefault();
    e.target.classList.remove('drag-over');

    var targetIndex = parseInt(e.target.getAttribute('data-seq-index'));

    if (draggedPatternIndex !== null) {
        state.sequence.splice(targetIndex + 1, 0, draggedPatternIndex);
        draggedPatternIndex = null;
    } else if (draggedSeqIndex !== null && draggedSeqIndex !== targetIndex) {
        var item = state.sequence.splice(draggedSeqIndex, 1)[0];
        state.sequence.splice(targetIndex, 0, item);
        if (state.currentSequenceIndex === draggedSeqIndex) {
            state.currentSequenceIndex = targetIndex;
        } else if (draggedSeqIndex < state.currentSequenceIndex && targetIndex >= state.currentSequenceIndex) {
            state.currentSequenceIndex--;
        } else if (draggedSeqIndex > state.currentSequenceIndex && targetIndex <= state.currentSequenceIndex) {
            state.currentSequenceIndex++;
        }
    }

    draggedSeqIndex = null;
    currentGridPatternIndex = -1;
    renderSequenceSidebar();
    renderTrackerGrid();
}

function handleSequenceDragEnd(e) {
    e.target.style.opacity = '1';
    draggedSeqIndex = null;
}

function handlePoolDragStart(e) {
    draggedPatternIndex = parseInt(e.target.getAttribute('data-pattern-index'));
    e.target.classList.add('dragging');
}

// ============================================
// PATTERN MANAGEMENT
// ============================================

function addPattern() {
    var steps = parseInt(document.getElementById('step-count').value) || 64;
    var newPatternIndex = state.patterns.length;
    state.patterns.push(createEmptyPattern(steps));
    state.sequence.push(newPatternIndex);
    state.currentSequenceIndex = state.sequence.length - 1;
    currentGridPatternIndex = -1;
    renderSequenceSidebar();
    renderTrackerGrid(true);
    consoleLog('Added pattern ' + (newPatternIndex + 1));
}

function clonePattern() {
    var currentPattern = getCurrentPattern();
    var cloned = JSON.parse(JSON.stringify(currentPattern));
    var newPatternIndex = state.patterns.length;
    state.patterns.push(cloned);
    state.sequence.splice(state.currentSequenceIndex + 1, 0, newPatternIndex);
    state.currentSequenceIndex++;
    currentGridPatternIndex = -1;
    renderSequenceSidebar();
    renderTrackerGrid(true);
    consoleLog('Cloned pattern to ' + (newPatternIndex + 1));
}

function deleteSequenceEntry() {
    if (state.sequence.length <= 1) {
        consoleLog('Cannot delete last sequence entry');
        return;
    }
    state.sequence.splice(state.currentSequenceIndex, 1);
    if (state.currentSequenceIndex >= state.sequence.length) {
        state.currentSequenceIndex = state.sequence.length - 1;
    }
    document.getElementById('step-count').value = getCurrentPattern().steps;
    currentGridPatternIndex = -1;
    renderSequenceSidebar();
    renderTrackerGrid();
    consoleLog('Deleted sequence entry');
}

function applyStepCount() {
    var newSteps = parseInt(document.getElementById('step-count').value) || 64;
    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    var oldSteps = pattern.steps;

    if (newSteps === oldSteps) return;

    pattern.steps = newSteps;

    for (var track = 0; track < 16; track++) {
        if (newSteps > oldSteps) {
            for (var step = oldSteps; step < newSteps; step++) {
                pattern.data[track][step] = {
                    notes: [{ note: '', amp: '' }],
                    fx: ['']
                };
            }
        } else {
            pattern.data[track].length = newSteps;
        }
    }

    invalidatePatternCache(patternIndex);
    renderSequenceSidebar();
    renderTrackerGrid(true);
    consoleLog('Pattern steps set to ' + newSteps);
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

    for (var trackIdx = 0; trackIdx < 16; trackIdx++) {
        var track = document.createElement('div');
        track.className = 'track';
        track.setAttribute('data-track', trackIdx);

        if (state.trackMutes[trackIdx]) track.classList.add('muted');

        // Track header
        var header = document.createElement('div');
        header.className = 'track-header';
        header.innerHTML =
            '<div class="track-title">' +
                '<span class="track-title-text">' + state.tracks[trackIdx].name + '</span>' +
                '<div class="track-controls">' +
                    '<button class="btn-mute" data-track="' + trackIdx + '" title="Mute">M</button>' +
                    '<button class="btn-solo" data-track="' + trackIdx + '" title="Solo">S</button>' +
                '</div>' +
            '</div>' +
            '<div class="column-controls">' +
                '<div class="column-group">' +
                    '<span>N:</span>' +
                    '<button class="btn-note-minus" data-track="' + trackIdx + '">-</button>' +
                    '<button class="btn-note-plus" data-track="' + trackIdx + '">+</button>' +
                '</div>' +
                '<div class="column-group">' +
                    '<span>FX:</span>' +
                    '<button class="btn-fx-minus" data-track="' + trackIdx + '">-</button>' +
                    '<button class="btn-fx-plus" data-track="' + trackIdx + '">+</button>' +
                '</div>' +
            '</div>';
        track.appendChild(header);

        // Track rows container
        var rows = document.createElement('div');
        rows.className = 'track-rows';

        // Column labels
        var labelsRow = document.createElement('div');
        labelsRow.className = 'column-labels';

        if (trackIdx === 0) {
            var labelRowNum = document.createElement('div');
            labelRowNum.className = 'row-number';
            labelsRow.appendChild(labelRowNum);
        }

        var labelNoteCols = document.createElement('div');
        labelNoteCols.className = 'note-columns';
        for (var nc = 0; nc < state.tracks[trackIdx].noteColumns; nc++) {
            var labelNoteCol = document.createElement('div');
            labelNoteCol.className = 'note-column';
            labelNoteCol.innerHTML = '<div class="cell note-label">p4.' + (nc+1) + '</div><div class="cell amp-label">p5.' + (nc+1) + '</div>';
            labelNoteCols.appendChild(labelNoteCol);
        }
        labelsRow.appendChild(labelNoteCols);

        var labelFxCols = document.createElement('div');
        labelFxCols.className = 'fx-columns';
        for (var fc = 0; fc < state.tracks[trackIdx].fxColumns; fc++) {
            var labelFxCol = document.createElement('div');
            labelFxCol.className = 'fx-column';
            labelFxCol.innerHTML = '<div class="cell fx-label">p' + (6+fc) + '</div>';
            labelFxCols.appendChild(labelFxCol);
        }
        labelsRow.appendChild(labelFxCols);
        rows.appendChild(labelsRow);

        // Ensure pattern data has enough columns
        for (var step = 0; step < pattern.steps; step++) {
            while (pattern.data[trackIdx][step].notes.length < state.tracks[trackIdx].noteColumns) {
                pattern.data[trackIdx][step].notes.push({ note: '', amp: '' });
            }
            while (pattern.data[trackIdx][step].fx.length < state.tracks[trackIdx].fxColumns) {
                pattern.data[trackIdx][step].fx.push('');
            }
        }

        // Data rows
        for (var step = 0; step < pattern.steps; step++) {
            var row = createDataRow(trackIdx, step, pattern);
            rows.appendChild(row);
        }

        track.appendChild(rows);
        container.appendChild(track);
    }

    return container;
}

function createDataRow(trackIdx, step, pattern) {
    var row = document.createElement('div');
    row.className = 'track-row';
    row.setAttribute('data-step', step);

    // Row number (only on first track)
    if (trackIdx === 0) {
        var rowNum = document.createElement('div');
        rowNum.className = 'row-number';
        rowNum.textContent = step.toString().padStart(3, '0');
        row.appendChild(rowNum);
    }

    var stepData = pattern.data[trackIdx][step];

    // Note columns
    var noteColumnsEl = document.createElement('div');
    noteColumnsEl.className = 'note-columns';

    for (var nc = 0; nc < state.tracks[trackIdx].noteColumns; nc++) {
        var noteCol = document.createElement('div');
        noteCol.className = 'note-column';

        var noteData = stepData.notes[nc] || { note: '', amp: '' };

        // Note cell
        var noteCell = document.createElement('div');
        noteCell.className = 'cell note';
        noteCell.setAttribute('data-track', trackIdx);
        noteCell.setAttribute('data-step', step);
        noteCell.setAttribute('data-col', nc);
        noteCell.setAttribute('data-type', 'note');
        noteCell.textContent = noteData.note || '---';
        if (noteData.note === NOTE_OFF) {
            noteCell.classList.add('note-off');
        }
        noteCol.appendChild(noteCell);

        // Amp cell
        var ampCell = document.createElement('div');
        ampCell.className = 'cell amp';
        ampCell.setAttribute('data-track', trackIdx);
        ampCell.setAttribute('data-step', step);
        ampCell.setAttribute('data-col', nc);
        ampCell.setAttribute('data-type', 'amp');
        ampCell.textContent = noteData.amp || '--';
        noteCol.appendChild(ampCell);

        noteColumnsEl.appendChild(noteCol);
    }
    row.appendChild(noteColumnsEl);

    // FX columns
    var fxColumnsEl = document.createElement('div');
    fxColumnsEl.className = 'fx-columns';

    for (var fc = 0; fc < state.tracks[trackIdx].fxColumns; fc++) {
        var fxCol = document.createElement('div');
        fxCol.className = 'fx-column';

        var fxCell = document.createElement('div');
        fxCell.className = 'cell fx';
        fxCell.setAttribute('data-track', trackIdx);
        fxCell.setAttribute('data-step', step);
        fxCell.setAttribute('data-col', fc);
        fxCell.setAttribute('data-type', 'fx');
        // Display FX value as hex
        var fxVal = stepData.fx[fc];
        if (fxVal && fxVal !== '' && fxVal !== '--') {
            var numVal = parseInt(fxVal, 16);
            if (!isNaN(numVal)) {
                fxCell.textContent = numVal.toString(16).toUpperCase().padStart(2, '0');
            } else {
                fxCell.textContent = fxVal.toUpperCase();
            }
        } else {
            fxCell.textContent = '--';
        }
        fxCol.appendChild(fxCell);

        fxColumnsEl.appendChild(fxCol);
    }
    row.appendChild(fxColumnsEl);

    return row;
}

function renderTrackerGrid(forceRebuild) {
    var grid = domCache.grid;
    var patternIndex = getCurrentPatternIndex();

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

    var absCol = toAbsoluteCol(info.track, info.type, info.col);

    selection.active = true;
    selection.startTrack = info.track;
    selection.startStep = info.step;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.startAbsCol = absCol;
    selection.endTrack = info.track;
    selection.endStep = info.step;
    selection.endCol = info.col;
    selection.endType = info.type;
    selection.endAbsCol = absCol;

    state.focusedTrack = info.track;
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

    var absCol = toAbsoluteCol(info.track, info.type, info.col);

    // Track if anything changed
    var changed = false;

    // Update track, step, and column for rectangular selection
    if (selection.endTrack !== info.track || selection.endStep !== info.step || selection.endAbsCol !== absCol) {
        selection.endTrack = info.track;
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
        state.trackMutes[trackIdx] = !state.trackMutes[trackIdx];
        target.classList.toggle('active', state.trackMutes[trackIdx]);
        document.querySelector('.track[data-track="' + trackIdx + '"]').classList.toggle('muted', state.trackMutes[trackIdx]);
    } else if (target.classList.contains('btn-solo')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        state.trackSolos[trackIdx] = !state.trackSolos[trackIdx];
        target.classList.toggle('active', state.trackSolos[trackIdx]);
    } else if (target.classList.contains('btn-note-plus')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        if (state.tracks[trackIdx].noteColumns < 8) {
            state.tracks[trackIdx].noteColumns++;
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
    } else if (target.classList.contains('btn-note-minus')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        if (state.tracks[trackIdx].noteColumns > 1) {
            state.tracks[trackIdx].noteColumns--;
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
    } else if (target.classList.contains('btn-fx-plus')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        if (state.tracks[trackIdx].fxColumns < 8) {
            state.tracks[trackIdx].fxColumns++;
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
    } else if (target.classList.contains('btn-fx-minus')) {
        var trackIdx = parseInt(target.getAttribute('data-track'));
        if (state.tracks[trackIdx].fxColumns > 1) {
            state.tracks[trackIdx].fxColumns--;
            invalidatePatternCache();
            renderTrackerGrid(true);
        }
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
    var keyLower = e.key.toLowerCase();
    if (keyboardMap.hasOwnProperty(keyLower) && !e.repeat && !e.ctrlKey && !e.altKey) {
        // Determine which track/column to use for the preview
        var previewTrack = state.focusedTrack >= 0 ? state.focusedTrack : 0;
        var previewCol = state.focusedColumn >= 0 ? state.focusedColumn : 0;

        // Play the note preview
        playNotePreview(keyLower, previewTrack, previewCol);
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

        // Piano keys for note entry (record into grid, but don't handle preview here - that's in the global handler)
        var key = e.key.toLowerCase();
        if (keyboardMap.hasOwnProperty(key) && selection.startType === 'note') {
            e.preventDefault();
            var semitone = keyboardMap[key];
            var noteName = semitoneToNoteName(semitone, state.baseOctave);
            // Only enter note into grid, don't play preview (keydown/keyup handles preview)
            enterNoteInSelectionNoPreview(noteName);
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
    if (element.classList && element.classList.contains('cell') && element.hasAttribute('data-track')) {
        return element;
    }
    if (element.closest) {
        var cell = element.closest('.cell');
        if (cell && cell.hasAttribute('data-track')) {
            return cell;
        }
    }
    return null;
}

function getCellInfo(cell) {
    if (!cell) return null;

    var track = parseInt(cell.getAttribute('data-track'));
    var step = parseInt(cell.getAttribute('data-step'));
    var col = parseInt(cell.getAttribute('data-col'));
    var type = cell.getAttribute('data-type');

    if (isNaN(track) || isNaN(step) || isNaN(col) || !type) {
        return null;
    }

    return { track: track, step: step, col: col, type: type };
}

function findCellElement(track, step, col, type) {
    var container = patternGridCache[currentGridPatternIndex];
    if (!container) return null;

    return container.querySelector(
        '.cell[data-track="' + track + '"][data-step="' + step + '"][data-col="' + col + '"][data-type="' + type + '"]'
    );
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

// Get type order for determining selection range
// Order: note, amp, fx (visual left to right within a note column, then fx)
function getTypeOrder(type) {
    if (type === 'note') return 0;
    if (type === 'amp') return 1;
    if (type === 'fx') return 2;
    return 0;
}

// Convert (type, col) to absolute column index for a track
// Layout: note0, amp0, note1, amp1, ..., fx0, fx1, ...
function toAbsoluteCol(track, type, col) {
    var noteColumns = state.tracks[track].noteColumns;
    if (type === 'note') {
        return col * 2;
    } else if (type === 'amp') {
        return col * 2 + 1;
    } else if (type === 'fx') {
        return noteColumns * 2 + col;
    }
    return 0;
}

// Convert absolute column index to (type, col) for a track
function fromAbsoluteCol(track, absCol) {
    var noteColumns = state.tracks[track].noteColumns;
    var noteAmpCols = noteColumns * 2;

    if (absCol < noteAmpCols) {
        var noteIdx = Math.floor(absCol / 2);
        var isAmp = absCol % 2 === 1;
        return { type: isAmp ? 'amp' : 'note', col: noteIdx };
    } else {
        return { type: 'fx', col: absCol - noteAmpCols };
    }
}

// Get total number of columns in a track
function getTotalColumns(track) {
    return state.tracks[track].noteColumns * 2 + state.tracks[track].fxColumns;
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
    var minTrack = Math.min(selection.startTrack, selection.endTrack);
    var maxTrack = Math.max(selection.startTrack, selection.endTrack);
    var minAbsCol = Math.min(selection.startAbsCol, selection.endAbsCol);
    var maxAbsCol = Math.max(selection.startAbsCol, selection.endAbsCol);

    // Simple rectangular selection: iterate over all cells in the rectangle
    for (var step = minStep; step <= maxStep; step++) {
        for (var track = minTrack; track <= maxTrack; track++) {
            var totalCols = getTotalColumns(track);
            var colStart = (track === minTrack) ? minAbsCol : 0;
            var colEnd = (track === maxTrack) ? maxAbsCol : (totalCols - 1);

            // For single-track selection, use exact column range
            // For multi-track, select from start col to end of first track,
            // all cols for middle tracks, start to end col for last track
            if (minTrack === maxTrack) {
                colStart = minAbsCol;
                colEnd = maxAbsCol;
            }

            for (var absCol = colStart; absCol <= colEnd && absCol < totalCols; absCol++) {
                var colInfo = fromAbsoluteCol(track, absCol);
                var cell = container.querySelector(
                    '.cell[data-track="' + track + '"][data-step="' + step + '"][data-col="' + colInfo.col + '"][data-type="' + colInfo.type + '"]'
                );
                if (cell) {
                    cell.classList.add('selected');
                    selectedCells.push(cell);
                }
            }
        }
    }
}

function navigateSelection(colDelta, stepDelta) {
    var pattern = getCurrentPattern();
    if (!pattern) return;

    // If no active selection, create one at current focused position or (0,0,0)
    if (!selection.active || selection.startAbsCol < 0) {
        var track = state.focusedTrack >= 0 ? state.focusedTrack : 0;
        var step = state.focusedStep >= 0 ? state.focusedStep : 0;
        var type = state.focusedType || 'note';
        var col = state.focusedColumn >= 0 ? state.focusedColumn : 0;
        var absCol = toAbsoluteCol(track, type, col);

        selection.active = true;
        selection.startTrack = track;
        selection.startStep = step;
        selection.startAbsCol = absCol;
        selection.startType = type;
        selection.startCol = col;
        selection.endTrack = track;
        selection.endStep = step;
        selection.endAbsCol = absCol;
        selection.endType = type;
        selection.endCol = col;
    }

    var track = selection.startTrack;
    var absCol = selection.startAbsCol + colDelta;
    var step = selection.startStep + stepDelta;

    // Handle column overflow to next/previous track
    while (absCol < 0 && track > 0) {
        track--;
        absCol = getTotalColumns(track) + absCol;
    }
    while (absCol >= getTotalColumns(track) && track < 15) {
        absCol = absCol - getTotalColumns(track);
        track++;
    }

    // Clamp to valid range
    if (track < 0 || track >= 16) return;
    if (absCol < 0) absCol = 0;
    if (absCol >= getTotalColumns(track)) absCol = getTotalColumns(track) - 1;
    if (step < 0 || step >= pattern.steps) return;

    // Update selection
    selection.startTrack = track;
    selection.startStep = step;
    selection.startAbsCol = absCol;
    selection.endTrack = track;
    selection.endStep = step;
    selection.endAbsCol = absCol;

    // Update type/col for compatibility
    var colInfo = fromAbsoluteCol(track, absCol);
    selection.startType = colInfo.type;
    selection.startCol = colInfo.col;
    selection.endType = colInfo.type;
    selection.endCol = colInfo.col;

    state.focusedTrack = track;
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

    var absCol = toAbsoluteCol(info.track, info.type, info.col);

    selection.active = true;
    selection.startTrack = info.track;
    selection.startStep = info.step;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.startAbsCol = absCol;
    selection.endTrack = info.track;
    selection.endStep = info.step;
    selection.endCol = info.col;
    selection.endType = info.type;
    selection.endAbsCol = absCol;

    state.focusedTrack = info.track;
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
                value = numVal.toString(16).toUpperCase().padStart(2, '0');
            }
        }

        setCellValue(info.track, info.step, info.col, info.type, value);
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
                var nextCell = findCellElement(info.track, info.step + state.editStep, info.col, info.type);
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

function setCellValue(track, step, col, type, value) {
    var patternIndex = getCurrentPatternIndex();
    var pattern = getCurrentPattern();
    var stepData = pattern.data[track][step];

    if (type === 'note') {
        stepData.notes[col].note = value;
    } else if (type === 'amp') {
        stepData.notes[col].amp = value;
    } else if (type === 'fx') {
        stepData.fx[col] = value;
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
    } else if (type === 'fx') {
        // Display FX values as hex (00-FFFF)
        if (!value || value === '' || value === '--') {
            cell.textContent = '--';
        } else {
            // If it's a number, convert to hex
            var numVal = parseInt(value, 16);
            if (!isNaN(numVal)) {
                cell.textContent = numVal.toString(16).toUpperCase().padStart(2, '0');
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

    setCellValue(info.track, info.step, info.col, 'note', noteName);
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

    // Use fractional instrument number with semitone for unique instances (allows chords)
    // Format: instrNum.semitone (e.g., 1.00, 1.01, 1.12 for different keys on track 1)
    var instrNum = (track + 1) + '.' + semitone.toString().padStart(2, '0');

    // Turn off any existing note for this key first
    if (pressedKeys[key]) {
        var oldInstrNum = pressedKeys[key].instrNum;
        csound.inputMessage('i -' + oldInstrNum + ' 0 0').catch(function(err) {});
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

    // Turn off the note
    var offMsg = 'i -' + keyInfo.instrNum + ' 0 0';
    csound.inputMessage(offMsg).catch(function(err) {});

    // Remove from pressed keys
    delete pressedKeys[key];
}

// Track hex input buffer for FX columns
var fxInputBuffer = '';
var fxInputTimeout = null;

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

    // Format as hex with leading zeros (minimum 2 digits)
    var hexValue = value.toString(16).toUpperCase().padStart(2, '0');

    setCellValue(info.track, info.step, info.col, 'fx', hexValue);
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

    // Get all selected FX cells sorted by step
    var fxCells = [];
    for (var i = 0; i < selectedCells.length; i++) {
        var info = getCellInfo(selectedCells[i]);
        if (info && info.type === 'fx') {
            var stepData = pattern.data[info.track][info.step];
            var fxStr = stepData.fx[info.col];
            var value = null;
            if (fxStr && fxStr !== '' && fxStr !== '--') {
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

            // Clamp to 0-255 (hex 00-FF)
            interpolatedValue = Math.max(0, Math.min(255, interpolatedValue));

            // Set the value
            var hexValue = interpolatedValue.toString(16).toUpperCase().padStart(2, '0');
            var stepData = pattern.data[cell.info.track][cell.info.step];
            stepData.fx[cell.info.col] = hexValue;
            updateCellDisplay(cell.cell, 'fx', hexValue);
        }
    }

    markPatternDirty(patternIndex);
    consoleLog('Interpolated FX: ' + startValue.toString(16).toUpperCase() + ' -> ' + endValue.toString(16).toUpperCase());
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

        var stepData = pattern.data[info.track][info.step];

        if (info.type === 'note') {
            stepData.notes[info.col].note = '';
            updateCellDisplay(cell, 'note', '');
        } else if (info.type === 'amp') {
            stepData.notes[info.col].amp = '';
            updateCellDisplay(cell, 'amp', '');
        } else if (info.type === 'fx') {
            stepData.fx[info.col] = '';
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
    var minTrack = Math.min(selection.startTrack, selection.endTrack);
    var maxTrack = Math.max(selection.startTrack, selection.endTrack);

    // Copy ALL data (all note columns + all fx columns) for each track/step
    var data = [];
    var maxNoteColumns = 0;
    var maxFxColumns = 0;

    for (var step = minStep; step <= maxStep; step++) {
        var row = [];
        for (var track = minTrack; track <= maxTrack; track++) {
            var stepData = pattern.data[track][step];

            // Deep copy all notes and fx
            var notesCopy = [];
            for (var nc = 0; nc < stepData.notes.length; nc++) {
                notesCopy.push({
                    note: stepData.notes[nc].note,
                    amp: stepData.notes[nc].amp
                });
            }

            var fxCopy = [];
            for (var fc = 0; fc < stepData.fx.length; fc++) {
                fxCopy.push(stepData.fx[fc]);
            }

            row.push({
                notes: notesCopy,
                fx: fxCopy
            });

            // Track max columns used
            if (notesCopy.length > maxNoteColumns) maxNoteColumns = notesCopy.length;
            if (fxCopy.length > maxFxColumns) maxFxColumns = fxCopy.length;
        }
        data.push(row);
    }

    clipboard = {
        type: 'all',
        data: data,
        isRange: true,
        width: maxTrack - minTrack + 1,
        height: maxStep - minStep + 1,
        maxNoteColumns: maxNoteColumns,
        maxFxColumns: maxFxColumns
    };

    consoleLog('Copied ' + clipboard.width + 'x' + clipboard.height + ' steps (N:' + maxNoteColumns + ' FX:' + maxFxColumns + ')');
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

    // Handle 'all' type clipboard (full step data with all columns)
    if (clipboard.type === 'all') {
        var needsRebuild = false;

        // First pass: ensure all target tracks have enough columns
        for (var colIdx = 0; colIdx < clipboard.width; colIdx++) {
            var targetTrack = startInfo.track + colIdx;
            if (targetTrack >= 16) break;

            // Add note columns if needed
            if (state.tracks[targetTrack].noteColumns < clipboard.maxNoteColumns) {
                state.tracks[targetTrack].noteColumns = clipboard.maxNoteColumns;
                needsRebuild = true;
            }

            // Add fx columns if needed
            if (state.tracks[targetTrack].fxColumns < clipboard.maxFxColumns) {
                state.tracks[targetTrack].fxColumns = clipboard.maxFxColumns;
                needsRebuild = true;
            }
        }

        // Rebuild grid if we added columns
        if (needsRebuild) {
            invalidatePatternCache();
            renderTrackerGrid(true);
        }

        // Second pass: paste the data
        var count = 0;
        for (var rowIdx = 0; rowIdx < clipboard.height; rowIdx++) {
            var targetStep = startInfo.step + rowIdx;
            if (targetStep >= pattern.steps) break;

            for (var colIdx = 0; colIdx < clipboard.width; colIdx++) {
                var targetTrack = startInfo.track + colIdx;
                if (targetTrack >= 16) break;

                var cellData = clipboard.data[rowIdx][colIdx];
                var stepData = pattern.data[targetTrack][targetStep];

                // Ensure stepData has enough note slots
                while (stepData.notes.length < cellData.notes.length) {
                    stepData.notes.push({ note: '', amp: '' });
                }

                // Ensure stepData has enough fx slots
                while (stepData.fx.length < cellData.fx.length) {
                    stepData.fx.push('');
                }

                // Copy all notes
                for (var nc = 0; nc < cellData.notes.length; nc++) {
                    stepData.notes[nc].note = cellData.notes[nc].note;
                    stepData.notes[nc].amp = cellData.notes[nc].amp;

                    var noteCell = findCellElement(targetTrack, targetStep, nc, 'note');
                    var ampCell = findCellElement(targetTrack, targetStep, nc, 'amp');
                    if (noteCell) updateCellDisplay(noteCell, 'note', cellData.notes[nc].note);
                    if (ampCell) updateCellDisplay(ampCell, 'amp', cellData.notes[nc].amp);
                }

                // Copy all fx
                for (var fc = 0; fc < cellData.fx.length; fc++) {
                    stepData.fx[fc] = cellData.fx[fc];

                    var fxCell = findCellElement(targetTrack, targetStep, fc, 'fx');
                    if (fxCell) updateCellDisplay(fxCell, 'fx', cellData.fx[fc]);
                }

                count++;
            }
        }

        consoleLog('Pasted ' + count + ' steps');
        markPatternDirty(patternIndex);
        return;
    }

    // Legacy handling for old clipboard types (single cell)
    if (!clipboard.isRange) {
        var stepData = pattern.data[startInfo.track][startInfo.step];

        if (clipboard.type === 'note') {
            stepData.notes[startInfo.col].note = clipboard.data.note;
            stepData.notes[startInfo.col].amp = clipboard.data.amp;

            var noteCell = findCellElement(startInfo.track, startInfo.step, startInfo.col, 'note');
            var ampCell = findCellElement(startInfo.track, startInfo.step, startInfo.col, 'amp');
            if (noteCell) updateCellDisplay(noteCell, 'note', clipboard.data.note);
            if (ampCell) updateCellDisplay(ampCell, 'amp', clipboard.data.amp);
        } else {
            stepData.fx[startInfo.col] = clipboard.data;
            updateCellDisplay(startCell, 'fx', clipboard.data);
        }

        consoleLog('Pasted');
    }

    markPatternDirty(patternIndex);
}

// ============================================
// NOTE HELPERS
// ============================================

function parseNote(noteStr) {
    if (!noteStr || noteStr === '---' || noteStr === '' || noteStr === NOTE_OFF) return null;

    var freq = parseFloat(noteStr);
    if (!isNaN(freq) && freq > 0) return freq;

    var match = noteStr.match(/^([A-Ga-g])([#b]?)(\d+)$/);
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
    var val = parseFloat(ampStr);
    if (isNaN(val)) return 0.5;
    if (val > 1) return val / 100;
    return val;
}

function semitoneToNoteName(semitone, octave) {
    var noteIdx = semitone % 12;
    var noteOctave = octave + Math.floor(semitone / 12);
    return noteNames[noteIdx] + noteOctave;
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
    var trackIdx = state.focusedTrack;
    var colIdx = state.focusedColumn;

    if (trackIdx < 0) trackIdx = 0;
    if (trackIdx >= 16) trackIdx = 0;
    if (colIdx < 0) colIdx = 0;

    var stepData = pattern.data[trackIdx][state.focusedStep];
    stepData.notes[colIdx].note = noteName;
    if (!stepData.notes[colIdx].amp) {
        stepData.notes[colIdx].amp = '0.7';
    }

    markPatternDirty(patternIndex);

    // Update display
    var noteCell = findCellElement(trackIdx, state.focusedStep, colIdx, 'note');
    var ampCell = findCellElement(trackIdx, state.focusedStep, colIdx, 'amp');
    if (noteCell) updateCellDisplay(noteCell, 'note', noteName);
    if (ampCell && ampCell.textContent === '--') updateCellDisplay(ampCell, 'amp', '0.7');

    // Note: Preview is handled by keydown/keyup handlers for proper note-on/note-off

    // Move down by edit step (skip if editStep is 0)
    if (state.editStep > 0) {
        state.focusedStep = Math.min(state.focusedStep + state.editStep, pattern.steps - 1);

        var nextCell = findCellElement(trackIdx, state.focusedStep, colIdx, 'note');
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
    var anySolo = state.trackSolos.some(function(s) { return s; });
    if (anySolo) {
        return state.trackSolos[trackIdx];
    }
    return !state.trackMutes[trackIdx];
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

    var seqItems = document.querySelectorAll('.sequence-item');
    for (var i = 0; i < seqItems.length; i++) {
        seqItems[i].classList.remove('playing');
        if (parseInt(seqItems[i].getAttribute('data-seq-index')) === state.currentSequenceIndex) {
            seqItems[i].classList.add('playing');
        }
    }

    // Always follow playhead
    if (rows.length > 0) {
        var container = document.querySelector('.tracker-container');
        var firstRow = rows[0];
        var rowRect = firstRow.getBoundingClientRect();
        var containerRect = container.getBoundingClientRect();

        if (rowRect.top < containerRect.top || rowRect.bottom > containerRect.bottom) {
            firstRow.scrollIntoView({ block: 'center', behavior: 'auto' });
        }
    }
}

// Calculate current visual position from AudioContext time
// This is separate from state.currentStep which is scheduled ahead
function getCurrentVisualPosition() {
    if (!audioCtx || !state.isPlaying) {
        return { step: state.currentStep, seqIndex: state.currentSequenceIndex };
    }

    var stepDuration = 60 / (state.bpm * state.lpb);
    var elapsedTime = audioCtx.currentTime - playbackStartTime;
    var totalSteps = Math.floor(elapsedTime / stepDuration);

    // Calculate position accounting for pattern/sequence boundaries
    var seqIndex = 0;
    var step = totalSteps;

    while (seqIndex < state.sequence.length) {
        var patternIdx = state.sequence[seqIndex];
        var pattern = state.patterns[patternIdx];
        if (step < pattern.steps) {
            break;
        }
        step -= pattern.steps;
        seqIndex++;
        if (seqIndex >= state.sequence.length) {
            // Loop back
            seqIndex = 0;
            // Adjust playbackStartTime to prevent overflow on long playback
            var totalPatternSteps = 0;
            for (var i = 0; i < state.sequence.length; i++) {
                totalPatternSteps += state.patterns[state.sequence[i]].steps;
            }
            playbackStartTime += totalPatternSteps * stepDuration;
            step = totalSteps % totalPatternSteps;
        }
    }

    return { step: step, seqIndex: seqIndex };
}

function visualUpdateLoop() {
    if (!state.isPlaying) {
        pendingVisualUpdate = null;
        return;
    }

    // Get visual position from AudioContext time (not scheduler position)
    var visualPos = getCurrentVisualPosition();

    if (lastPlayedStep !== visualPos.step || lastPlayedSeqIndex !== visualPos.seqIndex) {
        if (lastPlayedSeqIndex !== visualPos.seqIndex) {
            // Temporarily set state for rendering
            var savedSeqIndex = state.currentSequenceIndex;
            state.currentSequenceIndex = visualPos.seqIndex;
            document.getElementById('step-count').value = getCurrentPattern().steps;
            renderSequenceSidebar();
            renderTrackerGrid();
            state.currentSequenceIndex = savedSeqIndex;
        }

        updatePlayhead(visualPos.step);
        lastPlayedStep = visualPos.step;
        lastPlayedSeqIndex = visualPos.seqIndex;
    }

    pendingVisualUpdate = requestAnimationFrame(visualUpdateLoop);
}

// Calculate how many steps until next note or NOTE_OFF in a track/column
// Scans ahead across patterns in sequence to find next NOTE_OFF or new note
// Returns step count if found, or -1 if no termination found (indefinite hold)
function getNoteDurationSteps(trackIdx, noteCol, startSeqIdx, startStep) {
    var seqIdx = startSeqIdx;
    var step = startStep + 1;
    var stepsCount = 1;
    var maxSteps = 256; // Safety limit
    var foundEnd = false;

    while (stepsCount < maxSteps) {
        var patternIdx = state.sequence[seqIdx];
        var pattern = state.patterns[patternIdx];

        if (step >= pattern.steps) {
            step = 0;
            seqIdx++;
            if (seqIdx >= state.sequence.length) {
                seqIdx = 0;
            }
            // Looped back to start without finding note-off
            if (seqIdx === startSeqIdx && step <= startStep) {
                break;
            }
            continue;
        }

        var stepData = pattern.data[trackIdx][step];
        if (stepData && stepData.notes[noteCol]) {
            var noteValue = stepData.notes[noteCol].note;
            if (noteValue === NOTE_OFF || parseNote(noteValue) !== null) {
                foundEnd = true;
                break;
            }
        }

        stepsCount++;
        step++;
    }

    // No NOTE_OFF or new note found - return -1 for indefinite hold
    return foundEnd ? stepsCount : -1;
}

// Schedule a single step at the given AudioContext time
// p2 is calculated as offset from current time for precise scheduling
function scheduleStep(scheduledTime) {
    if (!state.csoundReady || !state.isPlaying) return;

    var pattern = getCurrentPattern();
    var stepDuration = 60 / (state.bpm * state.lpb);

    // Calculate p2: how far in the future to schedule this note
    var p2 = Math.max(0, scheduledTime - audioCtx.currentTime);

    for (var trackIdx = 0; trackIdx < 16; trackIdx++) {
        if (!isTrackAudible(trackIdx)) continue;

        var stepData = pattern.data[trackIdx][state.currentStep];
        if (!stepData) continue;

        var numNoteCols = state.tracks[trackIdx].noteColumns;
        var noteTriggeredThisStep = false;

        for (var nc = 0; nc < numNoteCols; nc++) {
            if (!stepData.notes[nc]) {
                stepData.notes[nc] = { note: '', amp: '' };
            }
            var noteData = stepData.notes[nc];

            var instrNumStr = (trackIdx + 1) + '.' + nc.toString().padStart(2, '0');

            // Empty cell - note sustains, skip
            if (!noteData.note || noteData.note === '') {
                continue;
            }

            // NOTE_OFF - schedule note-off at the precise time
            if (noteData.note === NOTE_OFF) {
                try {
                    csound.inputMessage('i -' + instrNumStr + ' ' + p2.toFixed(4) + ' 0');
                } catch (err) {}
                noteTriggeredThisStep = true;
                continue;
            }

            var freq = parseNote(noteData.note);
            if (freq !== null) {
                var amp = parseAmplitude(noteData.amp);

                // Calculate p3 duration from BPM
                var durationSteps = getNoteDurationSteps(trackIdx, nc, state.currentSequenceIndex, state.currentStep);
                var duration = (durationSteps === -1) ? -1 : durationSteps * stepDuration;

                var pfields = [instrNumStr, p2.toFixed(4), (duration === -1) ? -1 : duration.toFixed(4), freq.toFixed(4), amp.toFixed(4)];

                // FX columns sent with note events (actual values)
                for (var fc = 0; fc < stepData.fx.length; fc++) {
                    var fxStr = stepData.fx[fc];
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                    }
                    pfields.push(fxVal);
                }

                var noteMsg = 'i ' + pfields.join(' ');
                try {
                    csound.inputMessage(noteMsg);
                } catch (err) {}
                noteTriggeredThisStep = true;
            }
        }

        // FX-only automation: if no note was triggered but there's FX data, send automation event
        // Uses -1 for freq to indicate this is an automation update, not a new note
        if (!noteTriggeredThisStep) {
            var hasFxData = false;
            for (var fc = 0; fc < stepData.fx.length; fc++) {
                var fxStr = stepData.fx[fc];
                if (fxStr && fxStr !== '' && fxStr !== '--') {
                    hasFxData = true;
                    break;
                }
            }

            if (hasFxData) {
                // Send automation event for each active note column (use .00 for primary)
                var instrNumStr = (trackIdx + 1) + '.00';
                var pfields = [instrNumStr, p2.toFixed(4), 0, -1, 0];  // p3=0, p4=-1 (automation flag), p5=0

                for (var fc = 0; fc < stepData.fx.length; fc++) {
                    var fxStr = stepData.fx[fc];
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                    }
                    pfields.push(fxVal);
                }

                var autoMsg = 'i ' + pfields.join(' ');
                try {
                    csound.inputMessage(autoMsg);
                } catch (err) {}
            }
        }
    }
}

// Advance to the next step, handling pattern/sequence boundaries
function advanceStep() {
    var pattern = getCurrentPattern();
    state.currentStep++;

    if (state.currentStep >= pattern.steps) {
        state.currentStep = 0;
        state.currentSequenceIndex++;

        if (state.currentSequenceIndex >= state.sequence.length) {
            state.currentSequenceIndex = 0;
        }
    }
}

// Lookahead scheduler - uses Web Audio clock for sample-accurate timing
// Schedules notes ahead of time to prevent timing jitter from main thread
function scheduler() {
    if (!state.isPlaying || !audioCtx) return;

    var stepDuration = 60 / (state.bpm * state.lpb);

    // Schedule all steps that fall within our lookahead window
    while (nextStepTime < audioCtx.currentTime + scheduleAheadTime) {
        scheduleStep(nextStepTime);
        advanceStep();
        nextStepTime += stepDuration;
    }

    // Schedule next check
    schedulerTimerId = setTimeout(scheduler, lookahead);
}

function startPlayback() {
    if (!state.csoundReady || state.isPlaying) return;

    // Check for AudioContext - fall back to less precise timing if unavailable
    if (!audioCtx) {
        consoleLog('Warning: AudioContext not available, timing may be imprecise');
    }

    state.isPlaying = true;
    state.currentStep = 0;
    lastPlayedStep = -1;
    lastPlayedSeqIndex = -1;

    prerenderAllPatterns();

    // Initialize precise timing using Web Audio clock
    if (audioCtx) {
        playbackStartTime = audioCtx.currentTime;
        nextStepTime = audioCtx.currentTime;
        // Start lookahead scheduler (runs every 25ms, schedules 100ms ahead)
        scheduler();
    } else {
        // Fallback to setInterval if no AudioContext (less precise)
        var stepDuration = (60 / (state.bpm * state.lpb)) * 1000;
        state.playInterval = setInterval(function() {
            scheduleStep(0);
            advanceStep();
        }, stepDuration);
    }

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

    // Turn off all held notes on all tracks/columns
    killAllNotes();

    var rows = document.querySelectorAll('.track-row.playing');
    for (var i = 0; i < rows.length; i++) {
        rows[i].classList.remove('playing');
    }

    var seqItems = document.querySelectorAll('.sequence-item.playing');
    for (var i = 0; i < seqItems.length; i++) {
        seqItems[i].classList.remove('playing');
    }

    document.getElementById('btn-play').disabled = false;
    // Keep stop button enabled for "panic" functionality (second click kills all notes)
    consoleLog('Stopped');
    setStatus('Stopped');
}

// ============================================
// SAVE/LOAD
// ============================================

function saveSong() {
    saveCurrentInstrument();
    saveOpcodes();

    var songData = {
        version: 2,
        bpm: state.bpm,
        lpb: state.lpb,
        patterns: state.patterns,
        sequence: state.sequence,
        tracks: state.tracks,
        instruments: state.instruments,
        opcodes: state.opcodes
    };

    var json = JSON.stringify(songData);
    var blob = new Blob([json], { type: 'application/octet-stream' });
    var url = URL.createObjectURL(blob);

    var a = document.createElement('a');
    a.href = url;
    a.download = 'song.cst';
    a.click();

    URL.revokeObjectURL(url);
    consoleLog('Song saved');
}

function loadSong(file) {
    var reader = new FileReader();
    reader.onload = function(e) {
        try {
            var songData = JSON.parse(e.target.result);

            state.bpm = songData.bpm || 120;
            state.lpb = songData.lpb || 4;
            state.patterns = songData.patterns || [createEmptyPattern(64)];
            state.sequence = songData.sequence || [0];
            state.tracks = songData.tracks || [];
            state.instruments = songData.instruments || defaultInstruments.slice();
            state.opcodes = songData.opcodes || '';
            state.currentSequenceIndex = 0;
            state.currentStep = 0;
            state.currentInstrument = 0;

            document.getElementById('bpm').value = state.bpm;
            document.getElementById('lpb').value = state.lpb;
            document.getElementById('step-count').value = getCurrentPattern().steps;

            initInstrumentTabs();
            document.getElementById('opcodes-editor').value = state.opcodes;

            invalidatePatternCache();
            prerenderAllPatterns();

            renderSequenceSidebar();
            renderTrackerGrid(true);

            if (state.csoundReady) {
                compileInstruments();
            }

            consoleLog('Song loaded');
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

        state.bpm = songData.bpm || 120;
        state.lpb = songData.lpb || 4;
        state.patterns = songData.patterns || [createEmptyPattern(64)];
        state.sequence = songData.sequence || [0];
        state.tracks = songData.tracks || [];
        state.instruments = songData.instruments || defaultInstruments.slice();
        state.opcodes = songData.opcodes || '';
        state.currentSequenceIndex = 0;
        state.currentStep = 0;
        state.currentInstrument = 0;

        document.getElementById('bpm').value = state.bpm;
        document.getElementById('lpb').value = state.lpb;
        document.getElementById('step-count').value = getCurrentPattern().steps;

        initInstrumentTabs();
        document.getElementById('opcodes-editor').value = state.opcodes;

        invalidatePatternCache();
        prerenderAllPatterns();

        renderSequenceSidebar();
        renderTrackerGrid(true);

        if (state.csoundReady) {
            compileInstruments();
        }

        consoleLog('Demo ' + demoNum + ' loaded');
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

    var csd = '<CsoundSynthesizer>\n<CsOptions>\n-odac -d\n</CsOptions>\n<CsInstruments>\n';
    csd += 'sr = 44100\nksmps = 32\nnchnls = 2\n0dbfs = 1\n\n';
    csd += 'gisine ftgen 1, 0, 16384, 10, 1\n\n';

    if (state.opcodes && state.opcodes.trim()) {
        csd += '; User Defined Opcodes\n' + state.opcodes + '\n\n';
    }

    csd += state.instruments.join('\n\n');
    csd += '\n</CsInstruments>\n<CsScore>\n';

    var stepDuration = 60 / (state.bpm * state.lpb);
    var events = [];
    var activeNotes = new Array(16).fill(null).map(function() { return {}; });

    var totalSteps = 0;
    for (var seqIdx = 0; seqIdx < state.sequence.length; seqIdx++) {
        totalSteps += state.patterns[state.sequence[seqIdx]].steps;
    }
    var totalDuration = totalSteps * stepDuration;

    var currentTime = 0;
    for (var seqIdx = 0; seqIdx < state.sequence.length; seqIdx++) {
        var patternIdx = state.sequence[seqIdx];
        var pattern = state.patterns[patternIdx];

        for (var step = 0; step < pattern.steps; step++) {
            var stepTime = currentTime + (step * stepDuration);

            for (var trackIdx = 0; trackIdx < 16; trackIdx++) {
                var stepData = pattern.data[trackIdx][step];
                if (!stepData) continue;

                for (var nc = 0; nc < stepData.notes.length; nc++) {
                    var noteData = stepData.notes[nc];

                    if (noteData.note === NOTE_OFF) {
                        if (activeNotes[trackIdx][nc]) {
                            var note = activeNotes[trackIdx][nc];
                            var duration = stepTime - note.start;

                            var pfields = [note.instr, note.start.toFixed(4), duration.toFixed(4), note.freq.toFixed(4), note.amp.toFixed(4)];
                            for (var fc = 0; fc < note.fx.length; fc++) {
                                // FX values are hex strings
                                var fxStr = note.fx[fc];
                                var fxVal = 0;
                                if (fxStr && fxStr !== '' && fxStr !== '--') {
                                    fxVal = parseInt(fxStr, 16);
                                    if (isNaN(fxVal)) fxVal = 0;
                                }
                                pfields.push(fxVal);
                            }
                            events.push('i ' + pfields.join(' '));

                            activeNotes[trackIdx][nc] = null;
                        }
                        continue;
                    }

                    var freq = parseNote(noteData.note);
                    if (freq !== null) {
                        if (activeNotes[trackIdx][nc]) {
                            var prevNote = activeNotes[trackIdx][nc];
                            var prevDuration = stepTime - prevNote.start;

                            var pfields = [prevNote.instr, prevNote.start.toFixed(4), prevDuration.toFixed(4), prevNote.freq.toFixed(4), prevNote.amp.toFixed(4)];
                            for (var fc = 0; fc < prevNote.fx.length; fc++) {
                                // FX values are hex strings
                                var fxStr = prevNote.fx[fc];
                                var fxVal = 0;
                                if (fxStr && fxStr !== '' && fxStr !== '--') {
                                    fxVal = parseInt(fxStr, 16);
                                    if (isNaN(fxVal)) fxVal = 0;
                                }
                                pfields.push(fxVal);
                            }
                            events.push('i ' + pfields.join(' '));
                        }

                        var amp = parseAmplitude(noteData.amp);

                        activeNotes[trackIdx][nc] = {
                            start: stepTime,
                            instr: trackIdx + 1,
                            freq: freq,
                            amp: amp,
                            fx: stepData.fx.slice()
                        };
                    }
                }
            }
        }

        currentTime += pattern.steps * stepDuration;
    }

    // Finalize remaining notes
    for (var trackIdx = 0; trackIdx < 16; trackIdx++) {
        for (var nc in activeNotes[trackIdx]) {
            if (activeNotes[trackIdx][nc]) {
                var note = activeNotes[trackIdx][nc];
                var duration = totalDuration - note.start;
                if (duration < stepDuration) duration = stepDuration;

                var pfields = [note.instr, note.start.toFixed(4), duration.toFixed(4), note.freq.toFixed(4), note.amp.toFixed(4)];
                for (var fc = 0; fc < note.fx.length; fc++) {
                    // FX values are hex strings
                    var fxStr = note.fx[fc];
                    var fxVal = 0;
                    if (fxStr && fxStr !== '' && fxStr !== '--') {
                        fxVal = parseInt(fxStr, 16);
                        if (isNaN(fxVal)) fxVal = 0;
                    }
                    pfields.push(fxVal);
                }
                events.push('i ' + pfields.join(' '));
            }
        }
    }

    events.sort(function(a, b) {
        var timeA = parseFloat(a.split(' ')[2]);
        var timeB = parseFloat(b.split(' ')[2]);
        return timeA - timeB;
    });

    csd += events.join('\n');
    csd += '\ne\n</CsScore>\n</CsoundSynthesizer>\n';

    var blob = new Blob([csd], { type: 'text/plain' });
    var url = URL.createObjectURL(blob);

    var a = document.createElement('a');
    a.href = url;
    a.download = 'composition.csd';
    a.click();

    URL.revokeObjectURL(url);
    consoleLog('CSD exported (' + events.length + ' events)');
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

var showingExtraInstruments = false;

function initInstrumentTabs() {
    var container = document.getElementById('instrument-tabs');
    container.innerHTML = '';

    // Show instruments 1-16 (tracks)
    for (var i = 0; i < 16; i++) {
        var tab = document.createElement('button');
        tab.className = 'instr-tab' + (i === 0 ? ' active' : '');
        tab.setAttribute('data-instr', i);
        tab.textContent = (i + 1);
        tab.addEventListener('click', handleInstrumentTabClick);
        container.appendChild(tab);
    }

    // Add "More" button for placeholder instruments 17-32
    var moreBtn = document.createElement('button');
    moreBtn.className = 'instr-tab instr-more-btn';
    moreBtn.textContent = '...';
    moreBtn.title = 'Show instruments 17-32 (no tracks)';
    moreBtn.addEventListener('click', toggleExtraInstruments);
    container.appendChild(moreBtn);

    document.getElementById('code-editor').value = state.instruments[0];
    state.currentInstrument = 0;
}

function toggleExtraInstruments() {
    showingExtraInstruments = !showingExtraInstruments;
    var container = document.getElementById('instrument-tabs');
    container.innerHTML = '';

    if (showingExtraInstruments) {
        // Show instruments 17-32 (placeholders)
        for (var i = 16; i < 32; i++) {
            var tab = document.createElement('button');
            tab.className = 'instr-tab' + (i === state.currentInstrument ? ' active' : '');
            tab.setAttribute('data-instr', i);
            tab.textContent = (i + 1);
            tab.addEventListener('click', handleInstrumentTabClick);
            container.appendChild(tab);
        }

        // Add "Back" button
        var backBtn = document.createElement('button');
        backBtn.className = 'instr-tab instr-more-btn';
        backBtn.textContent = '<';
        backBtn.title = 'Show instruments 1-16 (tracks)';
        backBtn.addEventListener('click', toggleExtraInstruments);
        container.appendChild(backBtn);
    } else {
        // Show instruments 1-16 (tracks)
        for (var i = 0; i < 16; i++) {
            var tab = document.createElement('button');
            tab.className = 'instr-tab' + (i === state.currentInstrument ? ' active' : '');
            tab.setAttribute('data-instr', i);
            tab.textContent = (i + 1);
            tab.addEventListener('click', handleInstrumentTabClick);
            container.appendChild(tab);
        }

        // Add "More" button
        var moreBtn = document.createElement('button');
        moreBtn.className = 'instr-tab instr-more-btn';
        moreBtn.textContent = '...';
        moreBtn.title = 'Show instruments 17-32 (no tracks)';
        moreBtn.addEventListener('click', toggleExtraInstruments);
        container.appendChild(moreBtn);
    }
}

function handleInstrumentTabClick(e) {
    var idx = parseInt(e.target.getAttribute('data-instr'));

    saveCurrentInstrument();

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
    document.getElementById('btn-load-sample').addEventListener('click', function() {
        document.getElementById('sample-file-input').click();
    });

    // Allow multiple file selection
    var fileInput = document.getElementById('sample-file-input');
    fileInput.setAttribute('multiple', 'true');

    fileInput.addEventListener('change', function(e) {
        if (e.target.files.length > 0) {
            loadMultipleSampleFiles(Array.from(e.target.files));
        }
    });

    // Set up drag-and-drop for sample list area and sample tab
    var dropTargets = [
        document.getElementById('sample-list'),
        document.getElementById('tab-samples')
    ];

    dropTargets.forEach(function(target) {
        if (!target) return;

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
                // Recursively get all files from entries (including folders)
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
                loadMultipleSampleFiles(files);
            } else {
                consoleLog('No audio files found in drop');
            }
        });
    });
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

async function loadMultipleSampleFiles(files) {
    if (!state.csoundReady || !csound) {
        consoleLog('Error: Csound not ready');
        return;
    }

    // Sort files alphabetically for consistent ordering
    files.sort(function(a, b) {
        return a.name.localeCompare(b.name);
    });

    var startTableNum = parseInt(document.getElementById('sample-table-num').value) || 100;
    consoleLog('Loading ' + files.length + ' sample(s) starting at ftable ' + startTableNum + '...');

    for (var i = 0; i < files.length; i++) {
        var file = files[i];
        var tableNum = startTableNum + i;
        await loadSampleFileToTable(file, tableNum);
    }

    // Update the table number input to next available
    document.getElementById('sample-table-num').value = startTableNum + files.length;
    consoleLog('Finished loading ' + files.length + ' sample(s)');
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
    var tableNum = parseInt(document.getElementById('sample-table-num').value) || 100;
    await loadSampleFileToTable(file, tableNum);
    document.getElementById('sample-table-num').value = tableNum + 1;
}

async function loadSampleFileToTable(file, tableNum) {
    if (!state.csoundReady || !csound) {
        consoleLog('Error: Csound not ready');
        return;
    }

    var existing = state.samples.find(function(s) { return s.tableNum === tableNum; });
    if (existing) {
        state.samples = state.samples.filter(function(s) { return s.tableNum !== tableNum; });
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
            renderSampleList();

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

function renderSampleList() {
    var list = document.getElementById('sample-list');
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

        // Delete button
        item.querySelector('.sample-delete-btn').addEventListener('click', function(e) {
            e.stopPropagation();
            var tbl = parseInt(this.getAttribute('data-table'));
            state.samples = state.samples.filter(function(s) { return s.tableNum !== tbl; });
            renderSampleList();
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
    var tabs = document.querySelectorAll('.editor-view-tab');
    tabs.forEach(function(t) {
        t.classList.toggle('active', t.getAttribute('data-view') === view);
    });

    var patternView = document.getElementById('pattern-editor-view');
    var sampleView = document.getElementById('sample-editor-view');

    if (patternView) patternView.classList.toggle('hidden', view !== 'pattern');
    if (sampleView) sampleView.classList.toggle('hidden', view !== 'sample');

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
    var baseTableNum = parseInt(document.getElementById('sample-table-num').value) || 100;

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
            createdCount++;
        } catch (err) {
            consoleLog('Error creating slice ' + (i + 1) + ': ' + err.message);
        }
    }

    // Update the sample table number for next import
    document.getElementById('sample-table-num').value = baseTableNum + createdCount;

    renderSampleList();
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

async function compileInstruments() {
    if (!state.csoundReady) {
        consoleLog('Error: Csound not ready');
        return;
    }

    saveCurrentInstrument();
    saveOpcodes();

    // Compile UDOs first if any
    if (state.opcodes && state.opcodes.trim()) {
        try {
            await csound.compileOrc(state.opcodes);
            consoleLog('Compiled UDOs');
        } catch (err) {
            consoleLog('UDO compile error: ' + err.message);
            return;
        }
    }

    // Compile each instrument block separately
    var compiledCount = 0;
    var errorCount = 0;

    for (var i = 0; i < state.instruments.length; i++) {
        var instrCode = state.instruments[i];
        if (!instrCode || !instrCode.trim()) continue;

        try {
            await csound.compileOrc(instrCode);
            compiledCount++;
        } catch (err) {
            consoleLog('Instr ' + (i + 1) + ' error: ' + err.message);
            errorCount++;
        }
    }

    // Compile panic instrument - uses turnoff2 to kill ALL instances of ALL instruments
    var panicInstr = 'instr 999\n';
    for (var i = 1; i <= 32; i++) {
        panicInstr += '  turnoff2 ' + i + ', 0, 0\n';
    }
    panicInstr += '  turnoff\nendin\n';

    try {
        await csound.compileOrc(panicInstr);
    } catch (err) {
        consoleLog('Panic instr error: ' + err.message);
    }

    // Reload sample ftables after recompilation using GEN01
    for (var i = 0; i < state.samples.length; i++) {
        var sample = state.samples[i];
        if (sample.fileName) {
            try {
                var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + sample.fileName + '" 0 0 0';
                await csound.readScore(ftableScore);
            } catch (err) {
                consoleLog('Ftable ' + sample.tableNum + ' error: ' + err.message);
            }
        }
    }

    if (errorCount > 0) {
        consoleLog('Compiled ' + compiledCount + ' instruments (' + errorCount + ' errors)');
        setStatus('Compiled with errors');
    } else {
        consoleLog('Compiled ' + compiledCount + ' instruments');
        setStatus('Compiled');
    }
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

        // Panic instrument - uses turnoff2 to kill ALL instances of ALL instruments
        // Mode 0 = turn off all instances, Release 0 = immediate stop
        orchestra += 'instr 999\n';
        for (var i = 1; i <= 32; i++) {
            orchestra += '  turnoff2 ' + i + ', 0, 0\n';
        }
        orchestra += '  turnoff\n';
        orchestra += 'endin\n\n';

        // Enable realtime audio output
        await csound.setOption('-odac');
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

        // Compile user instruments
        await compileInstruments();

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
    renderSequenceSidebar();
    renderTrackerGrid();

    initMainTabs();
    initInstrumentTabs();
    initSampleLoader();
    initSampleEditor();
    initContextMenu();
    renderSampleList();

    document.getElementById('step-count').value = getCurrentPattern().steps;

    // Button events
    document.getElementById('btn-play').addEventListener('click', startPlayback);
    document.getElementById('btn-stop').addEventListener('click', stopPlayback);
    document.getElementById('btn-record').addEventListener('click', toggleRecording);
    document.getElementById('btn-add-pattern').addEventListener('click', addPattern);
    document.getElementById('btn-clone-pattern').addEventListener('click', clonePattern);
    document.getElementById('btn-del-pattern').addEventListener('click', deleteSequenceEntry);
    document.getElementById('btn-apply-steps').addEventListener('click', applyStepCount);
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

    document.getElementById('lpb').addEventListener('change', function(e) {
        state.lpb = parseInt(e.target.value) || 4;
        if (state.isPlaying) {
            stopPlayback();
            startPlayback();
        }
    });

    document.getElementById('edit-step').addEventListener('change', function(e) {
        state.editStep = parseInt(e.target.value) || 1;
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
