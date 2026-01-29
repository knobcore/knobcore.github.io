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

// Default instruments for each of the 16 tracks
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
endin`
];

// Piano keyboard mapping
var keyboardMap = {
    'z': 0,  's': 1,  'x': 2,  'd': 3,  'c': 4,  'v': 5,
    'g': 6,  'b': 7,  'h': 8,  'n': 9,  'j': 10, 'm': 11,
    'q': 12, '2': 13, 'w': 14, '3': 15, 'e': 16, 'r': 17,
    '5': 18, 't': 19, '6': 20, 'y': 21, '7': 22, 'u': 23,
    'i': 24, '9': 25, 'o': 26, '0': 27, 'p': 28
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

// Clipboard
var clipboard = {
    type: null,
    data: null,
    isRange: false,
    width: 0,
    height: 0
};

// Selection state
var selection = {
    active: false,
    startTrack: -1,
    startStep: -1,
    startCol: -1,
    startType: null,
    endTrack: -1,
    endStep: -1,
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

    // Click for buttons
    grid.addEventListener('click', onGridClick);

    // Double click for editing
    grid.addEventListener('dblclick', onGridDblClick);

    // Global keyboard
    document.addEventListener('keydown', onDocumentKeyDown);
    document.addEventListener('keyup', onDocumentKeyUp);
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

    selection.active = true;
    selection.startTrack = info.track;
    selection.startStep = info.step;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.endTrack = info.track;
    selection.endStep = info.step;
    selection.endCol = info.col;
    selection.endType = info.type;

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

    // Track if anything changed
    var changed = false;

    // Always update step and track
    if (selection.endTrack !== info.track || selection.endStep !== info.step) {
        selection.endTrack = info.track;
        selection.endStep = info.step;
        changed = true;
    }

    // Only update column selection if still within the SAME track
    // This allows flexible column selection within a track, but locks it when crossing tracks
    if (info.track === selection.startTrack) {
        if (selection.endType !== info.type || selection.endCol !== info.col) {
            selection.endType = info.type;
            selection.endCol = info.col;
            changed = true;
        }
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

        // Arrow navigation
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

function highlightSelection() {
    // Clear old highlights
    for (var i = 0; i < selectedCells.length; i++) {
        selectedCells[i].classList.remove('selected');
    }
    selectedCells = [];

    if (!selection.active) return;

    var minStep = Math.min(selection.startStep, selection.endStep);
    var maxStep = Math.max(selection.startStep, selection.endStep);
    var minTrack = Math.min(selection.startTrack, selection.endTrack);
    var maxTrack = Math.max(selection.startTrack, selection.endTrack);

    var container = patternGridCache[currentGridPatternIndex];
    if (!container) return;

    // Check if this is a single cell selection (no drag, same position)
    var isSingleCell = (selection.startStep === selection.endStep &&
                        selection.startTrack === selection.endTrack &&
                        selection.startType === selection.endType &&
                        selection.startCol === selection.endCol);

    if (isSingleCell) {
        // Single cell: only select that specific cell
        var cell = container.querySelector(
            '.cell[data-track="' + minTrack + '"][data-step="' + minStep + '"][data-col="' + selection.startCol + '"][data-type="' + selection.startType + '"]'
        );
        if (cell) {
            cell.classList.add('selected');
            selectedCells.push(cell);
        }
    } else {
        // Range selection: select cells based on type and column ranges
        var startTypeOrder = getTypeOrder(selection.startType);
        var endTypeOrder = getTypeOrder(selection.endType);
        var minTypeOrder = Math.min(startTypeOrder, endTypeOrder);
        var maxTypeOrder = Math.max(startTypeOrder, endTypeOrder);

        // Determine column ranges for note/amp (they share col indices) and fx
        var noteAmpMinCol, noteAmpMaxCol, fxMinCol, fxMaxCol;
        var selectNotes = false, selectAmps = false, selectFx = false;

        // Check which types are in range
        if (minTypeOrder <= 0 && maxTypeOrder >= 0) selectNotes = true;
        if (minTypeOrder <= 1 && maxTypeOrder >= 1) selectAmps = true;
        if (minTypeOrder <= 2 && maxTypeOrder >= 2) selectFx = true;

        // Calculate column ranges based on what's selected
        if (selection.startType === 'fx' && selection.endType === 'fx') {
            // Only fx columns
            fxMinCol = Math.min(selection.startCol, selection.endCol);
            fxMaxCol = Math.max(selection.startCol, selection.endCol);
            noteAmpMinCol = noteAmpMaxCol = -1;
        } else if (selection.startType !== 'fx' && selection.endType !== 'fx') {
            // Only note/amp columns
            noteAmpMinCol = Math.min(selection.startCol, selection.endCol);
            noteAmpMaxCol = Math.max(selection.startCol, selection.endCol);
            fxMinCol = fxMaxCol = -1;
        } else {
            // Mixed: crossing from note/amp to fx or vice versa
            // Select the specific columns on each side
            if (selection.startType === 'fx') {
                fxMinCol = 0;
                fxMaxCol = selection.startCol;
                noteAmpMinCol = selection.endCol;
                noteAmpMaxCol = 99; // Will be clamped by actual track columns
            } else {
                noteAmpMinCol = selection.startCol;
                noteAmpMaxCol = 99; // Will be clamped by actual track columns
                fxMinCol = 0;
                fxMaxCol = selection.endCol;
            }
        }

        // Check if selecting across multiple tracks
        var isMultiTrack = (minTrack !== maxTrack);

        for (var step = minStep; step <= maxStep; step++) {
            for (var track = minTrack; track <= maxTrack; track++) {
                var trackNoteColumns = state.tracks[track].noteColumns;
                var trackFxColumns = state.tracks[track].fxColumns;

                // Select note cells
                if (selectNotes) {
                    // Multi-track: select ALL note columns in each track
                    // Single track: use the specific column range
                    var actualNoteMin = isMultiTrack ? 0 : Math.max(0, noteAmpMinCol);
                    var actualNoteMax = isMultiTrack ? (trackNoteColumns - 1) : Math.min(trackNoteColumns - 1, noteAmpMaxCol);
                    for (var col = actualNoteMin; col <= actualNoteMax; col++) {
                        var cell = container.querySelector(
                            '.cell[data-track="' + track + '"][data-step="' + step + '"][data-col="' + col + '"][data-type="note"]'
                        );
                        if (cell) {
                            cell.classList.add('selected');
                            selectedCells.push(cell);
                        }
                    }
                }

                // Select amp cells
                if (selectAmps) {
                    var actualAmpMin = isMultiTrack ? 0 : Math.max(0, noteAmpMinCol);
                    var actualAmpMax = isMultiTrack ? (trackNoteColumns - 1) : Math.min(trackNoteColumns - 1, noteAmpMaxCol);
                    for (var col = actualAmpMin; col <= actualAmpMax; col++) {
                        var cell = container.querySelector(
                            '.cell[data-track="' + track + '"][data-step="' + step + '"][data-col="' + col + '"][data-type="amp"]'
                        );
                        if (cell) {
                            cell.classList.add('selected');
                            selectedCells.push(cell);
                        }
                    }
                }

                // Select fx cells
                if (selectFx) {
                    var actualFxMin = isMultiTrack ? 0 : Math.max(0, fxMinCol);
                    var actualFxMax = isMultiTrack ? (trackFxColumns - 1) : Math.min(trackFxColumns - 1, fxMaxCol);
                    for (var col = actualFxMin; col <= actualFxMax; col++) {
                        var cell = container.querySelector(
                            '.cell[data-track="' + track + '"][data-step="' + step + '"][data-col="' + col + '"][data-type="fx"]'
                        );
                        if (cell) {
                            cell.classList.add('selected');
                            selectedCells.push(cell);
                        }
                    }
                }
            }
        }
    }
}

function navigateSelection(trackDelta, stepDelta) {
    if (!selection.active) return;

    var newTrack = selection.startTrack + trackDelta;
    var newStep = selection.startStep + stepDelta;
    var pattern = getCurrentPattern();

    if (newTrack < 0 || newTrack >= 16) return;
    if (newStep < 0 || newStep >= pattern.steps) return;

    selection.startTrack = newTrack;
    selection.startStep = newStep;
    selection.endTrack = newTrack;
    selection.endStep = newStep;

    state.focusedTrack = newTrack;
    state.focusedStep = newStep;

    highlightSelection();

    // Scroll into view
    if (selectedCells.length > 0) {
        selectedCells[0].scrollIntoView({ block: 'nearest', behavior: 'auto' });
    }
}

function selectCell(cell) {
    var info = getCellInfo(cell);
    if (!info) return;

    selection.active = true;
    selection.startTrack = info.track;
    selection.startStep = info.step;
    selection.startCol = info.col;
    selection.startType = info.type;
    selection.endTrack = info.track;
    selection.endStep = info.step;
    selection.endCol = info.col;
    selection.endType = info.type;

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
        if (cell) {
            var info = getCellInfo(cell);
            if (info) {
                // Move down
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

    // Move down by edit step
    navigateSelection(0, state.editStep);
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
        // Move down by edit step after input is complete
        navigateSelection(0, state.editStep);
    }, 500);
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

    // Move down
    state.focusedStep = Math.min(state.focusedStep + state.editStep, pattern.steps - 1);

    var nextCell = findCellElement(trackIdx, state.focusedStep, colIdx, 'note');
    if (nextCell) {
        selectCell(nextCell);
        nextCell.scrollIntoView({ block: 'nearest', behavior: 'auto' });
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
                continue;
            }

            var freq = parseNote(noteData.note);
            if (freq !== null) {
                var amp = parseAmplitude(noteData.amp);

                // Calculate p3 duration from BPM
                var durationSteps = getNoteDurationSteps(trackIdx, nc, state.currentSequenceIndex, state.currentStep);
                var duration = (durationSteps === -1) ? -1 : durationSteps * stepDuration;

                var pfields = [instrNumStr, p2.toFixed(4), (duration === -1) ? -1 : duration.toFixed(4), freq.toFixed(4), amp.toFixed(4)];

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

function initInstrumentTabs() {
    var container = document.getElementById('instrument-tabs');
    container.innerHTML = '';

    for (var i = 0; i < 16; i++) {
        var tab = document.createElement('button');
        tab.className = 'instr-tab' + (i === 0 ? ' active' : '');
        tab.setAttribute('data-instr', i);
        tab.textContent = (i + 1);
        tab.addEventListener('click', handleInstrumentTabClick);
        container.appendChild(tab);
    }

    document.getElementById('code-editor').value = state.instruments[0];
    state.currentInstrument = 0;
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

    document.getElementById('sample-file-input').addEventListener('change', function(e) {
        if (e.target.files.length > 0) {
            loadSampleFile(e.target.files[0]);
        }
    });
}

async function loadSampleFile(file) {
    if (!state.csoundReady || !csound) {
        consoleLog('Error: Csound not ready');
        return;
    }

    var tableNum = parseInt(document.getElementById('sample-table-num').value) || 100;

    var existing = state.samples.find(function(s) { return s.tableNum === tableNum; });
    if (existing) {
        state.samples = state.samples.filter(function(s) { return s.tableNum !== tableNum; });
    }

    var reader = new FileReader();
    reader.onload = async function(e) {
        try {
            // Write file to Csound's virtual filesystem
            var fileName = '/' + file.name.replace(/[^a-zA-Z0-9._-]/g, '_');
            var data = new Uint8Array(e.target.result);
            await csound.fs.writeFile(fileName, data);
            consoleLog('Wrote file to Csound fs: ' + fileName);

            // Create ftable using GEN01 (deferred load)
            // f tableNum 0 0 1 "filename" 0 0 0
            var ftableScore = 'f ' + tableNum + ' 0 0 1 "' + fileName + '" 0 0 0';
            await csound.readScore(ftableScore);
            consoleLog('Created ftable ' + tableNum + ' from ' + fileName);

            state.samples.push({
                name: file.name,
                tableNum: tableNum,
                fileName: fileName,
                data: e.target.result
            });

            renderSampleList();
            consoleLog('Loaded sample: ' + file.name + ' -> ftable ' + tableNum);

            document.getElementById('sample-table-num').value = tableNum + 1;
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
            '<span class="sample-name">' + sample.name + '</span>' +
            '<span class="sample-table">ft' + sample.tableNum + '</span>' +
            '<button data-table="' + sample.tableNum + '">X</button>';

        item.querySelector('button').addEventListener('click', function() {
            var tbl = parseInt(this.getAttribute('data-table'));
            state.samples = state.samples.filter(function(s) { return s.tableNum !== tbl; });
            renderSampleList();
        });

        list.appendChild(item);
    });
}

async function compileInstruments() {
    if (!state.csoundReady) {
        consoleLog('Error: Csound not ready');
        return;
    }

    saveCurrentInstrument();
    saveOpcodes();

    var orchestra =
        'sr = 44100\n' +
        'ksmps = 32\n' +
        'nchnls = 2\n' +
        '0dbfs = 1\n\n' +
        'gisine ftgen 1, 0, 16384, 10, .1\n\n';

    if (state.opcodes && state.opcodes.trim()) {
        orchestra += '; User Defined Opcodes\n' + state.opcodes + '\n\n';
    }

    orchestra += state.instruments.join('\n\n');

    // Panic instrument - uses turnoff2 to kill ALL instances of ALL instruments
    orchestra += '\n\ninstr 999\n';
    for (var i = 1; i <= 16; i++) {
        orchestra += '  turnoff2 ' + i + ', 0, 0\n';
    }
    orchestra += '  turnoff\nendin\n';

    try {
        await csound.compileOrc(orchestra);

        // Reload sample ftables after recompilation
        for (var i = 0; i < state.samples.length; i++) {
            var sample = state.samples[i];
            if (sample.fileName) {
                var ftableScore = 'f ' + sample.tableNum + ' 0 0 1 "' + sample.fileName + '" 0 0 0';
                await csound.readScore(ftableScore);
            }
        }

        consoleLog('Compiled');
        setStatus('Compiled');
    } catch (err) {
        consoleLog('Compile error: ' + err.message);
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
        const { Csound } = await import('csound.js');

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

        // Compile initial blank instruments
        var orchestra =
            'sr = 44100\n' +
            'ksmps = 32\n' +
            'nchnls = 2\n' +
            '0dbfs = 1\n\n' +
            'gisine ftgen 1, 0, 16384, 10, 1\n\n';

        for (var i = 1; i <= 16; i++) {
            orchestra += 'instr ' + i + '\nendin\n\n';
        }

        // Panic instrument - uses turnoff2 to kill ALL instances of ALL instruments
        // Mode 0 = turn off all instances, Release 0 = immediate stop
        orchestra += 'instr 999\n';
        for (var i = 1; i <= 16; i++) {
            orchestra += '  turnoff2 ' + i + ', 0, 0\n';
        }
        orchestra += '  turnoff\n';
        orchestra += 'endin\n\n';

        // Enable realtime audio output
        await csound.setOption('-odac');
        // Enable full message output (don't suppress displays)
        await csound.setOption('-m7');  // Full message level (amps + range + warnings)

        await csound.compileOrc(orchestra);
        consoleLog('Blank instruments initialized (1-16)');

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

    consoleLog('Keys: z-m/q-u=notes, Tab=OFF, `=rec, Ctrl+C/X/V=copy/cut/paste');

    // Initialize Csound 7
    initCsound();
}

if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
} else {
    init();
}
