CSOUND MOD TRACKER
==================

A web-based mod tracker that triggers Csound instruments instead of samples.
Uses Csound WASM from knobcore.github.io

RUNNING THE TRACKER
-------------------

Simply open index.html in your web browser!

The Csound library will load automatically from the local files:
  - csound.js (wrapper)
  - CsoundObj.js (WASM engine)

No server required - just double-click index.html.

HOW TO USE
----------

1. Wait for "Csound ready!" message in the status bar
2. Click "Start Csound" to initialize audio
3. Enter notes in the tracker grid:
   - Note format: C4, D#3, Ab5, etc. OR direct frequencies (440, 880)
   - Amplitude: 0-1 (decimal) or 0-99 (percentage)
   - FX columns: additional p-fields (p6, p7, p8...) for instrument parameters
4. Click "Play" to start playback
5. Click "Stop" to stop

TRACK STRUCTURE
---------------
- 16 tracks, each linked to Csound instrument 1-16
- Each track has:
  - Note columns (p4 = frequency)
  - Amplitude columns (p5 = amplitude)
  - FX columns (p6, p7, p8... = additional parameters)
- Use +/- buttons above each track to add/remove columns
- Red border separates note/amp columns from FX columns

PATTERN CONTROLS
----------------
- Pattern: Select active pattern
- + Pattern: Add a new pattern
- Steps: Set the number of steps (rows) in current pattern
- Apply Steps: Apply the step count change

INSTRUMENT EDITOR
-----------------
The right panel contains a Csound orchestra code editor.
- Select an instrument (1-16) from the dropdown
- Edit the Csound code
- Click "Compile Instruments" to apply changes

Each instrument receives:
  p1 = instrument number
  p2 = start time (always 0 for tracker)
  p3 = duration (based on BPM)
  p4 = frequency (from note column)
  p5 = amplitude (from amp column)
  p6, p7, p8... = values from FX columns

KEYBOARD NAVIGATION
-------------------
- Arrow Up/Down: Move between rows in same column
- Enter: Move to next row
- Tab: Move to next cell

FILES
-----
  index.html      - Main HTML page
  styles.css      - CSS styles
  tracker.js      - Tracker engine
  csound.js       - Csound wrapper (from knobcore.github.io)
  CsoundObj.js    - Csound WASM engine (from knobcore.github.io)

TROUBLESHOOTING
---------------

If Csound doesn't load:
  - Check browser console (F12) for errors
  - Make sure CsoundObj.js is present
  - Try refreshing the page

No sound:
  - Click "Start Csound" first
  - Click inside the page (browser autoplay policy)
  - Make sure you have notes entered in the pattern
  - Check amplitude values are not 0
