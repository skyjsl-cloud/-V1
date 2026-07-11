/* ===========================================================
   Sudoku — local generator + solver (no external API)
   =========================================================== */

const DIFFICULTY = {
  easy:   { givens: 44, mistakes: 3 },
  medium: { givens: 32, mistakes: 3 },
  hard:   { givens: 27, mistakes: 3 },
};

const BEST_TIMES_KEY = 'sudoku-best-times';

function loadBestTimes() {
  try {
    const raw = localStorage.getItem(BEST_TIMES_KEY);
    return raw ? JSON.parse(raw) : {};
  } catch (e) {
    return {};
  }
}

function saveBestTime(difficulty, seconds) {
  const times = loadBestTimes();
  const prev = times[difficulty];
  if (prev === undefined || seconds < prev) {
    times[difficulty] = seconds;
    try { localStorage.setItem(BEST_TIMES_KEY, JSON.stringify(times)); } catch (e) {}
    return true; // new record
  }
  return false;
}

function formatTime(totalSeconds) {
  const m = Math.floor(totalSeconds / 60).toString().padStart(2, '0');
  const s = (totalSeconds % 60).toString().padStart(2, '0');
  return `${m}:${s}`;
}

function updateBestDisplay(difficulty) {
  const times = loadBestTimes();
  const best = times[difficulty];
  document.getElementById('bestVal').textContent = best !== undefined ? formatTime(best) : '--:--';
}

/* ---------- core solver / generator (bitmask backtracking) ---------- */

function emptyGrid() {
  return new Array(81).fill(0);
}

function rcbIndex(r, c) {
  return { row: r, col: c, box: Math.floor(r / 3) * 3 + Math.floor(c / 3) };
}

function shuffledDigits() {
  const arr = [1, 2, 3, 4, 5, 6, 7, 8, 9];
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

// Fills a full valid board using randomized backtracking.
function generateFullBoard() {
  const grid = emptyGrid();
  const rows = new Array(9).fill(0);
  const cols = new Array(9).fill(0);
  const boxes = new Array(9).fill(0);

  function bitFor(d) { return 1 << (d - 1); }

  function fill(pos) {
    if (pos === 81) return true;
    const r = Math.floor(pos / 9), c = pos % 9;
    const b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
    const digits = shuffledDigits();
    for (const d of digits) {
      const bit = bitFor(d);
      if (rows[r] & bit || cols[c] & bit || boxes[b] & bit) continue;
      grid[pos] = d;
      rows[r] |= bit; cols[c] |= bit; boxes[b] |= bit;
      if (fill(pos + 1)) return true;
      grid[pos] = 0;
      rows[r] &= ~bit; cols[c] &= ~bit; boxes[b] &= ~bit;
    }
    return false;
  }

  fill(0);
  return grid;
}

// Counts number of solutions up to `limit` (early exit). Used to verify uniqueness.
function countSolutions(grid, limit = 2) {
  const rows = new Array(9).fill(0);
  const cols = new Array(9).fill(0);
  const boxes = new Array(9).fill(0);
  const cells = [];

  for (let i = 0; i < 81; i++) {
    const r = Math.floor(i / 9), c = i % 9, b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
    if (grid[i] !== 0) {
      const bit = 1 << (grid[i] - 1);
      rows[r] |= bit; cols[c] |= bit; boxes[b] |= bit;
    } else {
      cells.push(i);
    }
  }

  let count = 0;

  function nextCell() {
    // choose the empty cell with fewest candidates (MRV heuristic)
    let best = -1, bestCount = 10, bestMask = 0;
    for (const i of cells) {
      if (grid[i] !== 0) continue;
      const r = Math.floor(i / 9), c = i % 9, b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
      const used = rows[r] | cols[c] | boxes[b];
      const avail = (~used) & 0x1FF;
      const n = popcount(avail);
      if (n < bestCount) { bestCount = n; best = i; bestMask = avail; if (n === 0) break; }
    }
    return { idx: best, mask: bestMask };
  }

  function popcount(x) {
    let c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
  }

  function solve() {
    const { idx, mask } = nextCell();
    if (idx === -1) { count++; return; }
    if (mask === 0) return;
    for (let d = 1; d <= 9; d++) {
      const bit = 1 << (d - 1);
      if (!(mask & bit)) continue;
      const r = Math.floor(idx / 9), c = idx % 9, b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
      grid[idx] = d;
      rows[r] |= bit; cols[c] |= bit; boxes[b] |= bit;
      solve();
      grid[idx] = 0;
      rows[r] &= ~bit; cols[c] &= ~bit; boxes[b] &= ~bit;
      if (count >= limit) return;
    }
  }

  solve();
  return count;
}

// Removes cells from a full board while keeping the solution unique,
// stopping once the target number of "givens" remains (or no more can be removed).
function makePuzzle(fullBoard, targetGivens) {
  const grid = fullBoard.slice();
  const order = [...Array(81).keys()];
  for (let i = order.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [order[i], order[j]] = [order[j], order[i]];
  }

  let givens = 81;
  for (const idx of order) {
    if (givens <= targetGivens) break;
    if (grid[idx] === 0) continue;
    const backup = grid[idx];
    grid[idx] = 0;
    const testGrid = grid.slice();
    const solutions = countSolutions(testGrid, 2);
    if (solutions === 1) {
      givens--;
    } else {
      grid[idx] = backup;
    }
  }
  return grid;
}

function generatePuzzle(difficulty) {
  const cfg = DIFFICULTY[difficulty];
  const full = generateFullBoard();
  const puzzle = makePuzzle(full, cfg.givens);
  return { puzzle, solution: full };
}

/* ---------------------------- game state ---------------------------- */

let state = {
  puzzle: [],
  solution: [],
  board: [],      // current values entered by player
  given: [],      // boolean: is this a starting clue
  notes: [],       // array of Set per cell
  selected: -1,
  mistakes: 0,
  difficulty: 'medium',
  timerId: null,
  seconds: 0,
  notesMode: false,
  won: false,
};

function newGame(difficulty) {
  clearInterval(state.timerId);
  const { puzzle, solution } = generatePuzzle(difficulty);
  state = {
    puzzle,
    solution,
    board: puzzle.slice(),
    given: puzzle.map(v => v !== 0),
    notes: Array.from({ length: 81 }, () => new Set()),
    selected: -1,
    mistakes: 0,
    difficulty,
    timerId: null,
    seconds: 0,
    notesMode: false,
    won: false,
  };
  document.getElementById('givenVal').textContent = puzzle.filter(v => v !== 0).length;
  document.getElementById('mistakeVal').textContent = `0 / ${DIFFICULTY[difficulty].mistakes}`;
  document.getElementById('mistakeVal').classList.remove('error');
  document.getElementById('winBanner').classList.remove('show');
  updateBestDisplay(difficulty);
  startTimer();
  renderBoard();
}

function startTimer() {
  state.seconds = 0;
  updateTimerDisplay();
  state.timerId = setInterval(() => {
    state.seconds++;
    updateTimerDisplay();
  }, 1000);
}

function updateTimerDisplay() {
  document.getElementById('timeVal').textContent = formatTime(state.seconds);
}

/* ------------------------------ render ------------------------------- */

function buildBoardSkeleton() {
  const board = document.getElementById('board');
  board.innerHTML = '';
  for (let i = 0; i < 81; i++) {
    const cell = document.createElement('div');
    cell.className = 'cell';
    cell.dataset.idx = i;
    const r = Math.floor(i / 9);
    if (r === 2 || r === 5) cell.classList.add('row-thick');
    cell.addEventListener('click', () => selectCell(i));
    board.appendChild(cell);
  }
}

function renderBoard() {
  const cells = document.querySelectorAll('.cell');
  const sel = state.selected;
  const selRow = sel >= 0 ? Math.floor(sel / 9) : -1;
  const selCol = sel >= 0 ? sel % 9 : -1;
  const selBox = sel >= 0 ? Math.floor(selRow / 3) * 3 + Math.floor(selCol / 3) : -1;
  const selVal = sel >= 0 ? state.board[sel] : 0;

  cells.forEach((cellEl, i) => {
    const r = Math.floor(i / 9), c = i % 9, b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
    const val = state.board[i];
    cellEl.classList.remove('given', 'selected', 'peer', 'same-value', 'error-cell');
    cellEl.innerHTML = '';

    if (state.given[i]) cellEl.classList.add('given');

    if (sel >= 0) {
      if (i === sel) cellEl.classList.add('selected');
      else if (r === selRow || c === selCol || b === selBox) cellEl.classList.add('peer');
      if (selVal !== 0 && val === selVal) cellEl.classList.add('same-value');
    }

    if (val !== 0) {
      if (!state.given[i] && val !== state.solution[i]) cellEl.classList.add('error-cell');
      cellEl.textContent = val;
    } else if (state.notes[i] && state.notes[i].size > 0) {
      const notesDiv = document.createElement('div');
      notesDiv.className = 'notes';
      for (let n = 1; n <= 9; n++) {
        const span = document.createElement('span');
        span.textContent = state.notes[i].has(n) ? n : '';
        notesDiv.appendChild(span);
      }
      cellEl.appendChild(notesDiv);
    }
  });
}

function selectCell(i) {
  if (state.won) return;
  state.selected = i;
  renderBoard();
}

/* ------------------------------ input -------------------------------- */

function inputDigit(d) {
  if (state.won) return;
  const i = state.selected;
  if (i < 0 || state.given[i]) return;

  if (state.notesMode) {
    if (state.board[i] !== 0) return;
    if (state.notes[i].has(d)) state.notes[i].delete(d);
    else state.notes[i].add(d);
    renderBoard();
    return;
  }

  state.board[i] = d;
  state.notes[i].clear();

  if (d !== state.solution[i]) {
    state.mistakes++;
    const mv = document.getElementById('mistakeVal');
    mv.textContent = `${state.mistakes} / ${DIFFICULTY[state.difficulty].mistakes}`;
    mv.classList.add('error');
  }

  renderBoard();
  checkWin();
}

function eraseCell() {
  if (state.won) return;
  const i = state.selected;
  if (i < 0 || state.given[i]) return;
  state.board[i] = 0;
  state.notes[i].clear();
  renderBoard();
}

function giveHint() {
  if (state.won) return;
  let i = state.selected;
  if (i < 0 || state.given[i] || state.board[i] === state.solution[i]) {
    i = state.board.findIndex((v, idx) => !state.given[idx] && v !== state.solution[idx]);
    if (i === -1) return;
    state.selected = i;
  }
  state.board[i] = state.solution[i];
  state.notes[i].clear();
  renderBoard();
  checkWin();
}

function checkWin() {
  const complete = state.board.every((v, i) => v === state.solution[i]);
  if (complete) {
    state.won = true;
    clearInterval(state.timerId);
    const timeStr = formatTime(state.seconds);
    const isRecord = saveBestTime(state.difficulty, state.seconds);
    updateBestDisplay(state.difficulty);

    const banner = document.getElementById('winBanner');
    banner.classList.add('show');
    banner.classList.toggle('record', isRecord);
    banner.innerHTML = isRecord
      ? `신기록! ${timeStr} · 실수 ${state.mistakes}회`
      : `퍼즐을 완성했습니다! ${timeStr} · 실수 ${state.mistakes}회`;
  }
}

/* ------------------------------ wiring -------------------------------- */

function buildNumpad() {
  const pad = document.getElementById('numpad');
  pad.innerHTML = '';
  for (let n = 1; n <= 9; n++) {
    const btn = document.createElement('button');
    btn.className = 'num-btn';
    btn.textContent = n;
    btn.addEventListener('click', () => inputDigit(n));
    pad.appendChild(btn);
  }
}

function initControls() {
  document.getElementById('eraseBtn').addEventListener('click', eraseCell);
  document.getElementById('hintBtn').addEventListener('click', giveHint);
  document.getElementById('newGameBtn').addEventListener('click', () => newGame(state.difficulty));

  const notesBtn = document.getElementById('notesBtn');
  notesBtn.addEventListener('click', () => {
    state.notesMode = !state.notesMode;
    notesBtn.classList.toggle('active-toggle', state.notesMode);
  });

  document.querySelectorAll('.diff-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.diff-btn').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      newGame(btn.dataset.diff);
    });
  });

  document.addEventListener('keydown', (e) => {
    if (e.key >= '1' && e.key <= '9') inputDigit(parseInt(e.key, 10));
    else if (e.key === 'Backspace' || e.key === 'Delete' || e.key === '0') eraseCell();
    else if (e.key.startsWith('Arrow') && state.selected >= 0) {
      const r = Math.floor(state.selected / 9), c = state.selected % 9;
      let nr = r, nc = c;
      if (e.key === 'ArrowUp') nr = Math.max(0, r - 1);
      if (e.key === 'ArrowDown') nr = Math.min(8, r + 1);
      if (e.key === 'ArrowLeft') nc = Math.max(0, c - 1);
      if (e.key === 'ArrowRight') nc = Math.min(8, c + 1);
      selectCell(nr * 9 + nc);
      e.preventDefault();
    }
  });
}

/* ------------------------------- boot ---------------------------------- */

buildBoardSkeleton();
buildNumpad();
initControls();
newGame('medium');
