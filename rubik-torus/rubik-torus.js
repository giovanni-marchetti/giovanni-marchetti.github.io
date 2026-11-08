/*
 * Rubik's torus: a playable widget for the personal page.
 *
 * Adapted from the standalone app torus_app/index.html: same puzzle, drawing
 * and controls, embedded in the page. Styles are scoped to .rt and use the
 * page's light theme; there is no keyboard shortcut for undo.
 */
(() => {
'use strict';

const widget = document.querySelector('#rubik-torus .rt');
if (!widget) return;

// The m x m torus T_m of "Rubik's Abstract Polytopes". Its facets are squares;
// each carries a 3 x 3 block of stickers: one centre, four from the edge
// pieces, four from the corner pieces. All stickers live on a 3m x 3m toroidal
// grid, with column i and row j (row 0 at the bottom, as in the paper's
// figures). The facet with grid coordinates (a, b) is H = (2a+1, 2b+1) in
// Z_{2m}^2, and the sticker (F, G) sits at F + G/2 (in facet units). Since the
// quarter-turn phi_H is the rotation by 90 degrees about H, the move mu_H is
// the counterclockwise quarter-turn of the 5 x 5 block of stickers centred on
// the centre sticker of H.

const MIN_M = 3, MAX_M = 5;
const MARGIN = 1.75;            // width of the faded periodic margin, in sticker units
const KEY = 'rubiks-torus-v1';
const TURN_MS = 190, SLIDE_MS = 170;

const $ = id => document.getElementById(id);
const canvas = $('rt-board');
const ctx = canvas.getContext('2d');
const stage = $('rt-stage');
const reduceMotion = matchMedia('(prefers-reduced-motion: reduce)');
const mod = (x, n) => ((x % n) + n) % n;
const easeOut = p => 1 - Math.pow(1 - p, 3);

// ---------------------------------------------------------------- state
let m = 3, N = 9;
let cells = null;              // Int16Array(N*N): cells[j*N + i] = home index of the sticker at (i, j)
let history = [];              // moves since the last reset or scramble: 2*facet + (clockwise ? 1 : 0)
let ox = 0, oy = 0;            // offset of the picture against the fundamental domain, in sticker units
const dir = 1;                // a plain click turns counterclockwise (mu_H); right-click or Shift-click clockwise
let initialM = 3;
const store = {};              // per-size states, so switching sizes keeps your progress

let pal = null, homeFacet = null;
let anim = null, slide = null, drag = null;
let hover = null, cursor = null, kbd = false;   // kbd: the keyboard cursor is in use
let S = 1, dpr = 1, raf = 0;
let GI = 0.02;                 // half gap between the stickers of one piece
const GP = 0.07;               // half gap between pieces
const R_OUT = 0.09, R_IN = 0.02; // corner radii of the stickers (the app uses 0.15 and 0.03)
let tok = {};

// ---------------------------------------------------------------- moves
function applyMove(c, a, b, d) {
  const cx = 3 * a + 1, cy = 3 * b + 1;
  const old = new Int16Array(25);
  for (let v = -2; v <= 2; v++) for (let u = -2; u <= 2; u++)
    old[(v + 2) * 5 + u + 2] = c[mod(cy + v, N) * N + mod(cx + u, N)];
  for (let v = -2; v <= 2; v++) for (let u = -2; u <= 2; u++) {
    // rho(u, v) = (-v, u) for mu_H, and its inverse (v, -u) for mu_H^{-1}
    const nu = d > 0 ? -v : v, nv = d > 0 ? u : -u;
    c[mod(cy + nv, N) * N + mod(cx + nu, N)] = old[(v + 2) * 5 + u + 2];
  }
}
function solvedCells(n) { const c = new Int16Array(n * n); for (let k = 0; k < n * n; k++) c[k] = k; return c; }
function isSolved() { for (let k = 0; k < cells.length; k++) if (cells[k] !== k) return false; return true; }

function turn(a, b, d) {
  applyMove(cells, a, b, d);
  history.push(2 * (b * m + a) + (d < 0 ? 1 : 0));
  startTurnAnim(a, b, d);
  afterMove();
}
function undo() {
  if (!history.length) return;
  const h = history.pop(), f = h >> 1, d = (h & 1) ? -1 : 1;
  const a = f % m, b = (f - a) / m;
  applyMove(cells, a, b, -d);
  startTurnAnim(a, b, -d);
  afterMove();
}
function scramble() {
  const steps = 25 * m * m;
  let last = -1;
  do {
    for (let t = 0; t < steps; t++) {
      let f, d;
      do { f = Math.floor(Math.random() * m * m); d = Math.random() < 0.5 ? 1 : -1; } while (2 * f + (d < 0) === (last ^ 1));
      applyMove(cells, f % m, Math.floor(f / m), d);
      last = 2 * f + (d < 0 ? 1 : 0);
    }
  } while (isSolved());
  history = [];
  anim = null;
  if (!reduceMotion.matches) { canvas.classList.remove('shuffle'); void canvas.offsetWidth; canvas.classList.add('shuffle'); }
  refreshStatus(); save(); requestDraw();
}
function reset() {
  cells = solvedCells(N);
  history = [];
  anim = null;
  startSlide(Math.round(ox / N) * N, Math.round(oy / N) * N);
  refreshStatus(); save(); requestDraw();
}
function afterMove() {
  refreshStatus(); save(); requestDraw();
}

// ---------------------------------------------------------------- colours
// Hue runs along the columns (cyclic, like the torus), lightness up the rows.
function oklabToLinearRgb(L, A, B) {
  const l = (L + 0.3963377774 * A + 0.2158037573 * B) ** 3;
  const mm = (L - 0.1055613458 * A - 0.0638541728 * B) ** 3;
  const s = (L - 0.0894841775 * A - 1.2914855480 * B) ** 3;
  return [
    4.0767416621 * l - 3.3077115913 * mm + 0.2309699292 * s,
    -1.2684380046 * l + 2.6097574011 * mm - 0.3413193965 * s,
    -0.0041960863 * l - 0.7034186147 * mm + 1.7076147010 * s,
  ];
}
function oklch(L, C, h) {
  const ca = Math.cos(h * Math.PI / 180), sa = Math.sin(h * Math.PI / 180);
  const ok = c => c.every(x => x >= -1e-5 && x <= 1 + 1e-5);
  let rgb = oklabToLinearRgb(L, C * ca, C * sa);
  if (!ok(rgb)) {
    let lo = 0, hi = C;
    for (let it = 0; it < 24; it++) { const mid = (lo + hi) / 2; if (ok(oklabToLinearRgb(L, mid * ca, mid * sa))) lo = mid; else hi = mid; }
    rgb = oklabToLinearRgb(L, lo * ca, lo * sa);
  }
  const enc = x => { x = Math.min(1, Math.max(0, x)); return x <= 0.0031308 ? 12.92 * x : 1.055 * Math.pow(x, 1 / 2.4) - 0.055; };
  return '#' + rgb.map(x => Math.round(255 * enc(x)).toString(16).padStart(2, '0')).join('');
}
function buildPalette() {
  const fill = [];
  for (let b = 0; b < m; b++) for (let a = 0; a < m; a++) {
    const L = 0.46 + 0.42 * b / (m - 1);
    fill[b * m + a] = oklch(L, 0.165, 22 + 360 * a / m);
  }
  pal = { fill };
  homeFacet = new Int16Array(N * N);
  for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) homeFacet[j * N + i] = Math.floor(j / 3) * m + Math.floor(i / 3);
}
function readTokens() {
  const cs = getComputedStyle(widget);
  const g = n => cs.getPropertyValue(n).trim();
  tok = { plastic: g('--rt-plastic') || '#15171b', veil: g('--rt-veil') || 'rgba(247,249,250,0.66)', frame: g('--rt-frame') || '#161a20', bg: g('--rt-bg') || '#f7f9fa' };
  requestDraw();
}

// ---------------------------------------------------------------- drawing
// Board coordinates: the fundamental domain is [0, N]^2, one unit per sticker,
// y pointing up. The canvas shows [-MARGIN, N + MARGIN]^2.
function visible(x, y, w, h) { return x + w > -MARGIN && x < N + MARGIN && y + h > -MARGIN && y < N + MARGIN; }

function stickerPath(x, y, rx, ry) {
  // rx, ry in {0, 1, 2}: position of the sticker inside its facet. The sides
  // facing the facet boundary belong to the same piece and get a thin gap.
  // The outer corners of a piece are rounded by R_OUT, the others by R_IN.
  const inL = rx === 0, inR = rx === 2, inB = ry === 0, inT = ry === 2;
  const l = x + (inL ? GI : GP), r = x + 1 - (inR ? GI : GP);
  const b = y + (inB ? GI : GP), t = y + 1 - (inT ? GI : GP);
  ctx.beginPath();
  if (ctx.roundRect) {
    ctx.roundRect(l, b, r - l, t - b, [
      !inL && !inB ? R_OUT : R_IN, !inR && !inB ? R_OUT : R_IN,
      !inR && !inT ? R_OUT : R_IN, !inL && !inT ? R_OUT : R_IN,
    ]);
  } else ctx.rect(l, b, r - l, t - b);
}

function setBoardTransform() { ctx.setTransform(dpr * S, 0, 0, -dpr * S, dpr * MARGIN * S, dpr * (MARGIN + N) * S); }

function draw(now) {
  if (!cells || !S) return;
  let theta = 0, A = null;
  if (anim) {
    const p = (now - anim.t0) / anim.dur;
    if (p >= 1) anim = null; else { A = anim; theta = -A.d * (Math.PI / 2) * (1 - easeOut(p)); }
  }
  if (slide) {
    const p = Math.min(1, (now - slide.t0) / slide.dur), e = easeOut(p);
    ox = slide.fx + (slide.tx - slide.fx) * e;
    oy = slide.fy + (slide.ty - slide.fy) * e;
    if (p >= 1) { ox = mod(slide.tx, N); oy = mod(slide.ty, N); slide = null; refreshStatus(); save(); }
  }

  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  setBoardTransform();
  ctx.fillStyle = tok.plastic;
  ctx.fillRect(-MARGIN, -MARGIN, N + 2 * MARGIN, N + 2 * MARGIN);

  const copies = [-N, 0, N];

  // stickers at rest
  for (let j = 0; j < N; j++) for (let i = 0; i < N; i++) {
    const k = j * N + i;
    if (A && A.mask[k]) continue;
    const id = cells[k], f = homeFacet[id];
    const x0 = mod(i + ox, N), y0 = mod(j + oy, N);
    for (const dx of copies) for (const dy of copies) {
      const x = x0 + dx, y = y0 + dy;
      if (!visible(x, y, 1, 1)) continue;
      stickerPath(x, y, i % 3, j % 3);
      ctx.fillStyle = pal.fill[f];
      ctx.fill();
    }
  }

  // the turning block, lifted above the board
  if (A) {
    const bx = mod(3 * A.a + 1.5 + ox, N), by = mod(3 * A.b + 1.5 + oy, N);
    const reach = 3.6;
    for (const dx of copies) for (const dy of copies) {
      const X = bx + dx, Y = by + dy;
      if (!visible(X - reach, Y - reach, 2 * reach, 2 * reach)) continue;
      ctx.save();
      ctx.translate(X, Y);
      ctx.rotate(theta);
      ctx.shadowColor = 'rgba(0, 0, 0, 0.4)';
      ctx.shadowBlur = 12 * dpr;
      ctx.shadowOffsetY = 3 * dpr;
      ctx.fillStyle = tok.plastic;
      ctx.beginPath();
      if (ctx.roundRect) ctx.roundRect(-2.5, -2.5, 5, 5, 0.22); else ctx.rect(-2.5, -2.5, 5, 5);
      ctx.fill();
      ctx.shadowColor = 'transparent';
      ctx.shadowBlur = 0;
      ctx.shadowOffsetY = 0;
      for (let v = -2; v <= 2; v++) for (let u = -2; u <= 2; u++) {
        const id = cells[mod(3 * A.b + 1 + v, N) * N + mod(3 * A.a + 1 + u, N)], f = homeFacet[id];
        stickerPath(u - 0.5, v - 0.5, mod(1 + u, 3), mod(1 + v, 3));
        ctx.fillStyle = pal.fill[f];
        ctx.fill();
      }
      ctx.restore();
    }
  }

  // the periodic margin: veiled, then faded out towards the canvas edge
  ctx.beginPath();
  ctx.rect(-MARGIN, -MARGIN, N + 2 * MARGIN, N + 2 * MARGIN);
  ctx.rect(0, 0, N, N);
  ctx.fillStyle = tok.veil;
  ctx.fill('evenodd');
  ctx.globalCompositeOperation = 'destination-out';
  const fades = [
    [-MARGIN, 0, 0, 0, -MARGIN, -MARGIN, MARGIN, N + 2 * MARGIN],
    [N + MARGIN, 0, N, 0, N, -MARGIN, MARGIN, N + 2 * MARGIN],
    [0, -MARGIN, 0, 0, -MARGIN, -MARGIN, N + 2 * MARGIN, MARGIN],
    [0, N + MARGIN, 0, N, -MARGIN, N, N + 2 * MARGIN, MARGIN],
  ];
  for (const [x0, y0, x1, y1, rx, ry, rw, rh] of fades) {
    const g = ctx.createLinearGradient(x0, y0, x1, y1);
    g.addColorStop(0, 'rgba(0, 0, 0, 1)');
    g.addColorStop(1, 'rgba(0, 0, 0, 0)');
    ctx.fillStyle = g;
    ctx.fillRect(rx, ry, rw, rh);
  }
  ctx.globalCompositeOperation = 'source-over';

  drawFrame();

  // the square under the pointer, or the keyboard cursor
  if (!drag || !drag.moved) {
    const mark = hover || (kbd && document.activeElement === canvas ? cursor : null);
    if (mark) drawMark(mark.a, mark.b, mark.d || dir);
  }
}

function arrowHead(x, y, tx, ty, h) {
  // a stealth arrowhead centred at (x, y), pointing along (tx, ty)
  const nx = -ty, ny = tx;
  ctx.beginPath();
  ctx.moveTo(x + tx * h * 0.6, y + ty * h * 0.6);
  ctx.lineTo(x - tx * h * 0.45 + nx * h * 0.42, y - ty * h * 0.45 + ny * h * 0.42);
  ctx.lineTo(x - tx * h * 0.18, y - ty * h * 0.18);
  ctx.lineTo(x - tx * h * 0.45 - nx * h * 0.42, y - ty * h * 0.45 - ny * h * 0.42);
  ctx.closePath();
  ctx.fill();
  ctx.stroke();
}

function drawFrame() {
  // The boundary of the fundamental domain, with the gluing arrows of the
  // paper's figure: a single line and arrowheads in the page background
  // color (--rt-frame), without halos. The line runs along the dark gap
  // between stickers; its width is about half of that gap plus 2px
  // (about 4px for the 3 x 3 torus).
  const px = 1 / S;
  ctx.lineJoin = 'round';
  ctx.strokeStyle = tok.frame;
  ctx.lineWidth = GP + 2 * px;
  ctx.strokeRect(0, 0, N, N);
  const h = Math.max(11, 0.5 * S) * px;
  ctx.fillStyle = tok.frame;
  ctx.strokeStyle = tok.frame;
  ctx.lineWidth = 0.5 * px;
  const heads = [
    [N / 2, 0, 1, 0], [N / 2, N, 1, 0],
    [0, N / 2 - 0.32 * h, 0, 1], [0, N / 2 + 0.32 * h, 0, 1],
    [N, N / 2 - 0.32 * h, 0, 1], [N, N / 2 + 0.32 * h, 0, 1],
  ];
  for (const [x, y, tx, ty] of heads) arrowHead(x, y, tx, ty, h);
}

function drawMark(a, b, d) {
  const px = 1 / S;
  const fx = mod(3 * a + ox, N), fy = mod(3 * b + oy, N);
  const copies = [-N, 0, N];
  for (const dx of copies) for (const dy of copies) {
    const X = fx + dx, Y = fy + dy;
    if (!visible(X - 1, Y - 1, 5, 5)) continue;
    // Like the frame: single lines in the page background color (--rt-frame).
    // the 5 x 5 block of stickers moved by the turn, with the frame's line width
    ctx.beginPath();
    if (ctx.roundRect) ctx.roundRect(X - 1, Y - 1, 5, 5, 0.25); else ctx.rect(X - 1, Y - 1, 5, 5);
    ctx.lineWidth = GP + 2 * px; ctx.strokeStyle = tok.frame; ctx.stroke();
    // (no outline of the square itself: the gaps inside the block stay black)
    // the direction of the turn, as in the paper's figure
    const cx = X + 1.5, cy = Y + 1.5, r = 0.62;
    const s0 = (d > 0 ? -40 : 220) * Math.PI / 180, e0 = s0 + d * 1.5 * Math.PI;
    const tx = -Math.sin(e0) * d, ty = Math.cos(e0) * d;
    const ex = cx + r * Math.cos(e0), ey = cy + r * Math.sin(e0);
    const w = Math.max(3, 0.12 * S) * px, hh = Math.max(11, 0.45 * S) * px;
    ctx.lineCap = 'round';
    ctx.beginPath();
    ctx.arc(cx, cy, r, s0, e0 - d * 0.25, d < 0);
    ctx.strokeStyle = tok.frame; ctx.lineWidth = w; ctx.stroke();
    ctx.fillStyle = tok.frame; ctx.strokeStyle = tok.frame; ctx.lineWidth = 0.5 * px;
    arrowHead(ex, ey, tx, ty, hh);
  }
}

function requestDraw() { if (!raf) raf = requestAnimationFrame(frame); }
function frame(now) { raf = 0; draw(now); if (anim || slide) requestDraw(); }

function startTurnAnim(a, b, d) {
  if (reduceMotion.matches) { anim = null; return; }
  const mask = new Uint8Array(N * N);
  for (let v = -2; v <= 2; v++) for (let u = -2; u <= 2; u++) mask[mod(3 * b + 1 + v, N) * N + mod(3 * a + 1 + u, N)] = 1;
  anim = { a, b, d, mask, t0: performance.now(), dur: TURN_MS };
}
function startSlide(tx, ty) {
  if (reduceMotion.matches || (tx === ox && ty === oy)) { ox = mod(tx, N); oy = mod(ty, N); slide = null; requestDraw(); return; }
  slide = { fx: ox, fy: oy, tx, ty, t0: performance.now(), dur: SLIDE_MS };
  requestDraw();
}

function layout() {
  const r = stage.getBoundingClientRect();
  const size = Math.max(160, Math.floor(Math.min(r.width, r.height)));
  dpr = Math.min(window.devicePixelRatio || 1, 3);
  S = size / (N + 2 * MARGIN);
  GI = Math.max(0.5 / S, 0.009);
  canvas.style.width = canvas.style.height = size + 'px';
  canvas.width = canvas.height = Math.round(size * dpr);
  requestDraw();
}

// ---------------------------------------------------------------- input
function boardPoint(e) {
  const r = canvas.getBoundingClientRect();
  return [(e.clientX - r.left) / S - MARGIN, MARGIN + N - (e.clientY - r.top) / S];
}
function facetAt(x, y) {
  if (x < -MARGIN || x > N + MARGIN || y < -MARGIN || y > N + MARGIN) return null;
  const i = Math.floor(mod(x - ox, N)), j = Math.floor(mod(y - oy, N));
  return { a: Math.floor(i / 3), b: Math.floor(j / 3) };
}
function setHover(f) {
  const same = (f && hover && f.a === hover.a && f.b === hover.b && f.d === hover.d) || (!f && !hover);
  hover = f;
  if (!same) { requestDraw(); }
}

canvas.addEventListener('contextmenu', e => e.preventDefault());
canvas.addEventListener('pointerdown', e => {
  if (e.button !== 0 && e.button !== 2) return;
  try { canvas.setPointerCapture(e.pointerId); } catch (err) { /* pointer no longer active */ }
  if (slide) { ox = slide.tx; oy = slide.ty; slide = null; }
  kbd = false;
  drag = { id: e.pointerId, x0: e.clientX, y0: e.clientY, ox0: ox, oy0: oy, moved: false };
});
canvas.addEventListener('pointermove', e => {
  if (drag && drag.id === e.pointerId) {
    const dx = e.clientX - drag.x0, dy = e.clientY - drag.y0;
    if (!drag.moved && Math.hypot(dx, dy) > 6) { drag.moved = true; canvas.classList.add('sliding'); setHover(null); }
    if (drag.moved) { ox = drag.ox0 + dx / S; oy = drag.oy0 - dy / S; requestDraw(); }
    return;
  }
  if (e.pointerType === 'mouse') {
    const f = facetAt(...boardPoint(e));
    if (f) f.d = e.shiftKey ? -dir : dir;
    setHover(f);
  }
});
function endDrag(e, cancelled) {
  if (!drag || drag.id !== e.pointerId) return;
  const d0 = drag;
  drag = null;
  canvas.classList.remove('sliding');
  if (d0.moved) { startSlide(Math.round(ox / 3) * 3, Math.round(oy / 3) * 3); return; }
  if (cancelled) return;
  const f = facetAt(...boardPoint(e));
  if (!f) return;
  const d = (e.button === 2 || e.shiftKey) ? -dir : dir;
  cursor = { a: f.a, b: f.b };
  turn(f.a, f.b, d);
  if (e.pointerType === 'mouse') setHover({ a: f.a, b: f.b, d: e.shiftKey ? -dir : dir });
}
canvas.addEventListener('pointerup', e => endDrag(e, false));
canvas.addEventListener('pointercancel', e => endDrag(e, true));
canvas.addEventListener('pointerleave', e => { if (!drag) setHover(null); });

canvas.addEventListener('focus', () => {
  if (!cursor) cursor = { a: Math.floor(m / 2), b: Math.floor(m / 2) };
  try { kbd = canvas.matches(':focus-visible'); } catch (err) { kbd = false; }
  requestDraw();
});
canvas.addEventListener('blur', () => { requestDraw(); });
canvas.addEventListener('keydown', e => {
  const k = e.key;
  const step = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, 1], ArrowDown: [0, -1] }[k];
  if (step) {
    e.preventDefault();
    if (!cursor) cursor = { a: 0, b: 0 };
    if (kbd) cursor = { a: mod(cursor.a + step[0], m), b: mod(cursor.b + step[1], m) };
    kbd = true;
    hover = null; requestDraw();
  } else if ((k === ' ' || k === 'Enter') && cursor) {
    e.preventDefault();
    kbd = true;
    turn(cursor.a, cursor.b, e.shiftKey ? -dir : dir);
  }
});
document.addEventListener('keydown', e => { if (e.key === 'Shift' && hover) setHover({ a: hover.a, b: hover.b, d: -dir }); });
document.addEventListener('keyup', e => { if (e.key === 'Shift' && hover) setHover({ a: hover.a, b: hover.b, d: dir }); });

// ---------------------------------------------------------------- controls
const sizeSeg = $('rt-size');
for (let k = MIN_M; k <= MAX_M; k++) {
  const bt = document.createElement('button');
  bt.type = 'button';
  bt.setAttribute('role', 'radio');
  bt.dataset.m = k;
  bt.textContent = k;
  bt.setAttribute('aria-label', k + ' by ' + k);
  bt.addEventListener('click', () => { if (k !== m) setSize(k); });
  sizeSeg.appendChild(bt);
}
$('rt-undo').addEventListener('click', undo);
$('rt-scramble').addEventListener('click', scramble);
$('rt-reset').addEventListener('click', reset);

function syncControls() {
  for (const bt of sizeSeg.querySelectorAll('button')) bt.setAttribute('aria-checked', String(+bt.dataset.m === m));
}

// Enables Undo and Reset only when they would change something.
function refreshStatus() {
  $('rt-undo').disabled = history.length === 0;
  $('rt-reset').disabled = isSolved() && history.length === 0 && mod(ox, N) === 0 && mod(oy, N) === 0;
}

function stash() {
  if (cells) store[m] = { cells, history, ox: mod(Math.round(ox / 3) * 3, N), oy: mod(Math.round(oy / 3) * 3, N) };
}
function setSize(k) {
  stash();
  m = k; N = 3 * m;
  const s = store[m];
  if (s) { cells = s.cells; history = s.history; ox = s.ox; oy = s.oy; }
  else { cells = solvedCells(N); history = []; ox = oy = 0; }
  anim = slide = null; hover = null; cursor = null;
  buildPalette();
  syncControls(); refreshStatus(); layout(); save();
}

// ---------------------------------------------------------------- persistence
function serialize() {
  stash();
  const out = { m, states: {} };
  for (const k in store) {
    const s = store[k];
    out.states[k] = { cells: Array.from(s.cells), history: s.history.slice(), ox: s.ox, oy: s.oy };
  }
  return out;
}
function save() { try { localStorage.setItem(KEY, JSON.stringify(serialize())); } catch (err) { /* storage unavailable */ } }
function load(data) {
  if (!data || typeof data !== 'object') return;
  if (Number.isInteger(data.m) && data.m >= MIN_M && data.m <= MAX_M) initialM = data.m;
  const states = data.states && typeof data.states === 'object' ? data.states : {};
  for (const key of Object.keys(states)) {
    const k = Number(key), s = states[key];
    if (!Number.isInteger(k) || k < MIN_M || k > MAX_M || !s || !Array.isArray(s.cells)) continue;
    const n = 9 * k * k;
    if (s.cells.length !== n) continue;
    const seen = new Uint8Array(n);
    let ok = true;
    for (const v of s.cells) { if (!Number.isInteger(v) || v < 0 || v >= n || seen[v]) { ok = false; break; } seen[v] = 1; }
    if (!ok) continue;
    const hist = Array.isArray(s.history) ? s.history.filter(h => Number.isInteger(h) && h >= 0 && h < 2 * k * k) : [];
    const off = v => (Number.isInteger(v) ? mod(v - mod(v, 3), 3 * k) : 0);
    store[k] = { cells: Int16Array.from(s.cells), history: hist, ox: off(s.ox), oy: off(s.oy) };
  }
}
function readLocal() { try { return JSON.parse(localStorage.getItem(KEY) || 'null'); } catch (err) { return null; } }

// ---------------------------------------------------------------- boot
load(readLocal());
readTokens();
setSize(initialM);
new ResizeObserver(layout).observe(stage);
if (document.fonts && document.fonts.ready) document.fonts.ready.then(requestDraw);
})();
