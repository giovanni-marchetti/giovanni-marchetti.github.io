/*
 * Neuromanifold viewer, for a flat neuromanifold (see index_new.html).
 *
 * A shallow network with three neurons, each reading its own input, no
 * biases and the monomial activation t^k computes
 *     f(x) = a1 (w1 x1)^k + a2 (w2 x2)^k + a3 (w3 x3)^k = c1 x1^k + c2 x2^k + c3 x3^k,
 * with ci = ai wi^k. As (ai, wi) and (t^-k ai, t wi) give the same function
 * for any t ≠ 0, the six weights make a neuromanifold of dimension 3 only,
 * and it is flat: the span of x1^k, x2^k, x3^k, in the space of polynomials
 * of degree k in (x1, x2, x3). These monomials are orthonormal for the
 * Bombieri–Weyl inner product, so (c1, c2, c3) are orthonormal coordinates on
 * it, and it is shown as R³, in a box that the viewer turns. Its axes hold the
 * functions of a single neuron; neuron i is off (ai = 0 or wi = 0) on the
 * plane ci = 0.
 *
 * Training is gradient descent on the weights, for the loss
 *     L = ||f − g||²_BW + λ ||(a, w)||² = Σ (ci − ci*)² + λ Σ (ai² + wi²),
 * with g = Σ ci* xi^k the target. It starts from random weights: each ai and
 * wi is drawn from the normal distribution of standard deviation σ, and the
 * initialization is the function they compute. Gradient flow keeps the
 * imbalance di = k ai² − wi² of each neuron constant (with weight decay, it
 * decays as exp(−4λt)), and that decides where the neuron goes (see endOf):
 * when wi² > k ai², wi never vanishes, ci can cross its plane ci = 0, and the
 * neuron always learns ci*; when k ai² > wi², ai keeps its sign, and for k ≥ 2
 * a neuron that starts with the sign opposite to ci*'s stops on its plane, at
 * wi = 0. With weight decay, the weights end up balanced, k ai² = wi², and
 * then λ (ai² + wi²) is λ κ |ci|^(2/(k+1)), which shrinks the coefficients,
 * and cuts off the small ones.
 *
 * Rendering is in Canvas 2D, in perspective. The planes ci = 0 are
 * translucent. They cut space into octants, and everything is drawn octant by
 * octant, from those farthest from the octant of the eye (the most planes
 * away) to it, with the pieces of the planes in between: along any line of
 * sight, the octants come in increasing distance from that of the eye, so
 * that order is exact.
 */
(() => {
'use strict';

const root = document.querySelector('#neuromanifold .nm');
if (!root) return;
const $ = id => document.getElementById(id);

// ---------------------------------------------------------------- settings
const N = 3;                       // the neurons, and the dimension of the neuromanifold
const DEGREES = [1, 2, 3, 4, 5];
// The colors of the neurons (of their axes and planes), checked as a set, with
// ACCENT, for color-blind separation.
const NEURON = ['#2a78d6', '#eb6834', '#1baf7a'];
const INK = '#161a20', MUTED = '#59616c', ACCENT = '#a8203a';
const CAM_D = 5.5;                 // the eye is this far from the center of the box, in half-sides of the box
const FILL = 0.95;                 // the ball around the box fills this share of the half-width of the view
const ORBIT_SPEED = 0.008;         // radians per pixel of drag
const KEY_STEP = 0.08;             // radians per arrow key
const CLICK_PX = 6;                // a press that moves less than this is a click
const GRAB_PX = 12;                // the target can be grabbed this far from its mark
const SNAP = 0.025;                // a coordinate of the target within SNAP · B of 0 snaps to 0, when dragged
const MAX_COEF = 100;
const PLANE_A = 0.09, PLANE_EDGE_A = 0.45;   // the planes ci = 0: their fill, and their border
const MARK = { target: 7.5, init: 6, run: 5 };   // radii, in CSS pixels
const HIDDEN_ALPHA = 0.6;          // the opacity of those marks behind a plane
const SIGMA_LO = -2, SIGMA_HI = 0.3; // the range of the scale σ of the random weights, in log10
// Training
const LR = 0.05;                   // the learning rate, as a share of the largest stable one (see startRun)
const PATH_EPS = 0.002;            // the path gets a point every PATH_EPS · B of movement
const MAX_PATH = 4000;             // points of the path at most
const MAX_STEPS = 1e7;             // gradient steps of a run at most
const RAMP = 1.02;                 // the steps per frame grow by this factor every frame, from one
const SPF_MAX = 20000;             // gradient steps per frame at most

// ---------------------------------------------------------------- state
let k = 2;
const target = Float64Array.of(0.9, 0.55, 0.3);      // c*, the coordinates of the target
// The random draw of the initial weights: ai = σ zA[i], wi = σ zW[i]. The
// first one is fixed, so that the page always opens on the same run; a click
// draws new ones.
const zA = Float64Array.of(0.63, -0.16, 1.03), zW = Float64Array.of(1.22, 0.4, 1.03);
let sigma = 0.1;                   // the scale of the initial weights
const init = new Float64Array(N);  // c(0), the function of the initial weights (see updateInit)
let lambda = 0;                    // the weight of the regularization
let showPlanes = true;
let gesture = null;                // the pointer gesture in the view, see initView
let visible = true;

// ---------------------------------------------------------------- the network
const sgn = x => (x > 0 ? 1 : x < 0 ? -1 : 0);

function powi(x, n) {
  let p = 1;
  for (let i = 0; i < n; i++) p *= x;
  return p;
}

// A standard normal sample (Box–Muller).
const gauss = () => Math.sqrt(-2 * Math.log(1 - Math.random())) * Math.cos(2 * Math.PI * Math.random());

// A new random draw of the initial weights.
function drawWeights() {
  for (let i = 0; i < N; i++) { zA[i] = gauss(); zW[i] = gauss(); }
  updateInit();
}

// The initial weights, at the scale σ.
function initialWeights(a, w) {
  for (let i = 0; i < N; i++) { a[i] = sigma * zA[i]; w[i] = sigma * zW[i]; }
}

// The initialization: the function of the initial weights (it depends on σ and k).
function updateInit() {
  for (let i = 0; i < N; i++) init[i] = sigma * zA[i] * powi(sigma * zW[i], k);
}

// The largest of the balanced weights of the coefficients up to |t|: the
// size of the weights of the target.
const balancedWeight = t => Math.pow(Math.sqrt(k) * Math.abs(t), 1 / (k + 1));

// Where a neuron with weights (a, w) ends without regularization, for the
// target coefficient t. Gradient flow keeps d = k a² − w², and c = a w^k
// moves monotonically to t while w ≠ 0, at the speed 2 w^(2k−2) (w² + k² a²)
// |c − t|. When d < 0, w² ≥ −d never vanishes, so c reaches t, crossing 0 if
// it must (a then changes sign). When d > 0, a² ≥ d / k does not vanish
// either, so a keeps its sign; for k ≥ 2, w = 0 is a line of critical points,
// which w never crosses, so c keeps its sign too, and if that is not the sign
// of t, c goes to 0, as w does. For k = 1, w can cross 0, and c reaches t.
// When d = 0 (balanced weights), c keeps its sign: it reaches t if it starts
// with the sign of t, and 0 otherwise.
function endOf(a, w, t) {
  const c = a * powi(w, k), d = k * a * a - w * w;
  if (t === 0 || (a === 0 && w === 0) || (k >= 2 && w === 0)) return 0;
  if (d < 0 || (d > 0 && k === 1)) return t;
  return sgn(c) === sgn(t) ? t : 0;
}

// Where a neuron settles when it learns the target coefficient t: the stable
// fixed point ≠ 0 of the balanced gradient flow, with the loss F there (its
// share of L). Without regularization, it is t itself. With it, on balanced
// weights, the loss is F(c) = (c − |t|)² + λ κ c^q on the side c > 0 (taking
// the sign of t), with q = 2/(k + 1), and the point is the larger root of F';
// there is none when the regularization cuts the neuron off (null). For k ≥ 2,
// the smaller root, cm (as a size), is unstable: below it, the regularization
// wins, and the neuron goes to 0.
function settle(t) {
  if (t === 0) return null;
  if (lambda === 0) return { c: t, F: 0, cm: 0 };
  const m = Math.abs(t), s = sgn(t);
  const q = 2 / (k + 1), b = lambda * (k + 1) / k * Math.pow(k, 1 / (k + 1));
  const F = c => (c - m) ** 2 + b * Math.pow(c, q);
  if (k === 1) return m > lambda ? { c: s * (m - lambda), F: F(m - lambda), cm: 0 } : null;   // soft thresholding
  // F' is convex on c > 0, with F'(0+) = +∞, F'(m) > 0, and least where F'' = 0
  const dF = c => 2 * (c - m) + b * q * Math.pow(c, q - 1);
  const c0 = Math.pow(b * q * (1 - q) / 2, 1 / (2 - q));
  if (!(c0 < m) || dF(c0) >= 0) return null;
  // the root of F' between lo and hi, where it goes up (or down) through 0
  const root = (lo, hi, up) => {
    for (let it = 0; it < 100; it++) {
      const mid = (lo + hi) / 2;
      if ((dF(mid) < 0) === up) lo = mid; else hi = mid;
    }
    return (lo + hi) / 2;
  };
  const c = root(c0, m, true);
  return { c: s * c, F: F(c), cm: root(0, c0, false) };
}

// The coefficient that a neuron starting at c0 ends at, for the target
// coefficient t. On balanced weights, ċ = −(k + 1) w^2k F'(c), so c moves
// monotonically to the nearest zero of F' that way: to where the neuron
// settles if c0 has the sign of t (and, with regularization, is above cm),
// and to 0 otherwise, as the flow never crosses 0.
function limitOf(c0, t) {
  return t === 0 ? 0 : settledLimit(c0, settle(t));
}

// The same, given st = settle(t) (null when the neuron is cut off).
const settledLimit = (c0, st) => (st && sgn(c0) === sgn(st.c) && Math.abs(c0) > st.cm ? st.c : 0);

// ---------------------------------------------------------------- linear algebra
// Rotates rows i and j of the row-major matrix A (with n columns) by angle th.
function rotateRows(A, n, i, j, th) {
  const c = Math.cos(th), s = Math.sin(th);
  for (let m = 0; m < n; m++) {
    const x = A[i * n + m], y = A[j * n + m];
    A[i * n + m] = c * x + s * y;
    A[j * n + m] = -s * x + c * y;
  }
}

// Gram–Schmidt on the rows of the n x n matrix A.
function orthonormalize(A, n) {
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < i; j++) {
      let d = 0;
      for (let m = 0; m < n; m++) d += A[i * n + m] * A[j * n + m];
      for (let m = 0; m < n; m++) A[i * n + m] -= d * A[j * n + m];
    }
    let s = 0;
    for (let m = 0; m < n; m++) s += A[i * n + m] * A[i * n + m];
    s = Math.sqrt(s);
    for (let m = 0; m < n; m++) A[i * n + m] /= s;
  }
  return A;
}

// ---------------------------------------------------------------- the view
// The box |ci| ≤ B, seen in perspective. cam is a rotation: its rows are the
// directions of screen right, up, and towards the viewer, in the coordinates
// c. A point c is at v = cam · c / B in view space, where the box is the cube
// of half-side 1 and the eye is at (0, 0, CAM_D), looking down the z axis.
const view = { canvas: null, ctx: null, dpr: 1, W: 1, H: 1, cx: 0, cy: 0, f: 1,
               cam: new Float64Array(9), B: 1, frozen: false, dirty: true, steps: 0 };

// Snaps up to 1, 1.25, 1.5, 2, 2.5, 3, 4, 5, 6 or 8 times a power of 10.
const NICE = [1, 1.25, 1.5, 2, 2.5, 3, 4, 5, 6, 8];
function niceCeil(x) {
  const e = Math.floor(Math.log10(x));
  for (let d = e; d <= e + 1; d++) for (const m of NICE) {
    const v = m * 10 ** d;
    if (v >= x * (1 - 1e-9)) return v;
  }
  return 10 ** (e + 1);
}

// The size of the box: it takes in the target, the initialization and the run.
function boxGoal() {
  let m = 0;
  for (let i = 0; i < N; i++) m = Math.max(m, Math.abs(target[i]), Math.abs(init[i]));
  const run = train.run;
  if (run) for (let i = 0; i < N; i++) m = Math.max(m, Math.abs(run.c[i]));
  return niceCeil(1.1 * Math.max(m, 1e-3));
}

// Eases the size of the box towards its goal (in log scale), unless a point is
// being dragged; returns true while it is still easing.
function easeBox() {
  if (view.frozen) return false;
  const goal = boxGoal();
  if (Math.abs(view.B - goal) <= 1e-3 * goal) {
    if (view.B !== goal) { view.B = goal; view.dirty = true; }
    return false;
  }
  view.B = Math.exp(Math.log(view.B) + 0.2 * (Math.log(goal) - Math.log(view.B)));
  view.dirty = true;
  return true;
}

// out[o], out[o + 1]: the point c on the screen (CSS pixels); out[o + 2]: its
// depth in view space (towards the eye).
function project(c, out, o) {
  const C = view.cam, s0 = 1 / view.B;
  const x = (C[0] * c[0] + C[1] * c[1] + C[2] * c[2]) * s0;
  const y = (C[3] * c[0] + C[4] * c[1] + C[5] * c[2]) * s0;
  const z = (C[6] * c[0] + C[7] * c[1] + C[8] * c[2]) * s0;
  const s = view.f / (CAM_D - z);
  out[o] = view.cx + s * x;
  out[o + 1] = view.cy - s * y;
  out[o + 2] = z;
}

// The point (or direction) v of view space, in the coordinates c.
function fromView(vx, vy, vz, out) {
  const C = view.cam, B = view.B;
  for (let i = 0; i < N; i++) out[i] = B * (C[i] * vx + C[3 + i] * vy + C[6 + i] * vz);
  return out;
}

// The line of sight through the screen point (x, y) is v(t) = (t ux, t uy, CAM_D − t).
const sight = (x, y) => [(x - view.cx) / view.f, -(y - view.cy) / view.f];

// The point of the line of sight through (x, y) at the depth z.
function atDepth(x, y, z, out) {
  const [ux, uy] = sight(x, y), t = CAM_D - z;
  return fromView(t * ux, t * uy, z, out);
}

function snapSmall(c) {
  for (let i = 0; i < N; i++) if (Math.abs(c[i]) < SNAP * view.B) c[i] = 0;
  return c;
}

function resetCam() {
  // c2 to the right, c3 up, c1 towards the viewer; then turned (c1 to the
  // left), and seen from above
  view.cam.set([0, 1, 0, 0, 0, 1, 1, 0, 0]);
  rotateRows(view.cam, 3, 0, 2, -0.62);
  rotateRows(view.cam, 3, 1, 2, -0.4);
  view.dirty = true;
}

function orbit(dx, dy) {
  rotateRows(view.cam, 3, 0, 2, dx * ORBIT_SPEED);
  rotateRows(view.cam, 3, 1, 2, -dy * ORBIT_SPEED);
  if (++view.steps % 64 === 0) orthonormalize(view.cam, 3);
  view.dirty = true;
}

function resizeView() {
  const cv = view.canvas, dpr = Math.min(window.devicePixelRatio || 1, 2);
  const W = Math.max(1, cv.clientWidth), H = Math.max(1, cv.clientHeight);
  Object.assign(view, { W, H, dpr, cx: W / 2, cy: H / 2 });
  // the ball of radius √3 around the box, seen from CAM_D, fits FILL of the view
  view.f = FILL * Math.min(W, H) / 2 * Math.sqrt(CAM_D * CAM_D - 3) / Math.sqrt(3);
  const w = Math.round(W * dpr), h = Math.round(H * dpr);
  if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
  view.dirty = true;
}

// ---------------------------------------------------------------- drawing
// The side of the plane ci = 0 that x is on; points on the plane are taken to
// be on the side of the eye, so that they are drawn over it.
const side = (x, s) => (x > 0 ? 1 : x < 0 ? -1 : s);

// The layer of the point c: the number of planes ci = 0 between its octant and
// that of the eye (with signs eye).
function layerOf(c, eye) {
  let f = 0;
  for (let i = 0; i < N; i++) if (side(c[i], eye[i]) !== eye[i]) f++;
  return f;
}

// Adds the polyline through the points P (coordinates c) to the layers, cut
// where it crosses the planes ci = 0, each piece in the layer of its octant.
function addPolyline(layers, P, style, eye) {
  const q = new Float64Array(3), a = new Float64Array(N), m = new Float64Array(N), ts = [];
  const lerp = (A, B, t, out) => { for (let i = 0; i < N; i++) out[i] = A[i] + t * (B[i] - A[i]); };
  let cur = null, curLayer = -1;
  const point = c => { project(c, q, 0); cur.xy.push(q[0], q[1]); };
  for (let j = 0; j + 1 < P.length; j++) {
    const A = P[j], B = P[j + 1];
    ts.length = 0;
    ts.push(0, 1);
    for (let i = 0; i < N; i++) {
      if (side(A[i], eye[i]) === side(B[i], eye[i])) continue;
      const t = A[i] / (A[i] - B[i]);
      if (t > 0 && t < 1) ts.push(t);
    }
    ts.sort((x, y) => x - y);
    for (let r = 0; r + 1 < ts.length; r++) {
      const t0 = ts[r], t1 = ts[r + 1];
      if (t1 - t0 < 1e-12) continue;
      lerp(A, B, (t0 + t1) / 2, m);
      const L = layerOf(m, eye);
      if (L !== curLayer) {
        cur = { style, xy: [] };
        layers[L].lines.push(cur);
        curLayer = L;
        lerp(A, B, t0, a);
        point(a);
      }
      lerp(A, B, t1, a);
      point(a);
    }
  }
}

const STYLE = {
  path: { color: ACCENT, width: 2, halo: 4.2 },
  axis: NEURON.map(color => ({ color, width: 1.6 })),
  axisNeg: NEURON.map(color => ({ color, width: 1.6, alpha: 0.45 })),
};

function render() {
  view.dirty = false;
  const g = view.ctx, B = view.B, C = view.cam;
  g.setTransform(view.dpr, 0, 0, view.dpr, 0, 0);
  g.fillStyle = '#ffffff';
  g.fillRect(0, 0, view.W, view.H);
  const eye = [C[6] >= 0 ? 1 : -1, C[7] >= 0 ? 1 : -1, C[8] >= 0 ? 1 : -1];
  const layers = [0, 1, 2, 3].map(() => ({ lines: [] }));
  const P = (x, y, z) => Float64Array.of(x, y, z);
  const e = i => { const v = new Float64Array(N); v[i] = 1; return v; };

  // the axes
  for (let i = 0; i < N; i++) {
    for (const h of [1, -1]) {
      addPolyline(layers, [P(0, 0, 0), e(i).map(x => x * h * B)], h > 0 ? STYLE.axis[i] : STYLE.axisNeg[i], eye);
    }
  }

  // the path of the run
  const run = train.run;
  if (run) addPolyline(layers, [...run.path, run.c], STYLE.path, eye);

  for (let f = 3; f >= 0; f--) {
    strokeLines(g, layers[f].lines);
    if (showPlanes && f > 0) drawPlanes(g, f, eye);
  }

  // The initialization, the run and the target are drawn over everything, so
  // that no plane ever hides them; they are faint where planes are in front
  // of them.
  const top = [[init, 'init'], [run && run.c, 'run'], [target, 'target']], q = new Float64Array(3);
  for (const [c, kind] of top) {
    if (!c) continue;
    project(c, q, 0);
    g.globalAlpha = showPlanes && layerOf(c, eye) > 0 ? HIDDEN_ALPHA : 1;
    drawMark(g, { kind, x: q[0], y: q[1] });
  }
  g.globalAlpha = 1;
  placeLabels();
}

function strokeLines(g, lines) {
  g.lineCap = g.lineJoin = 'round';
  for (const { style: s, xy } of lines) {
    if (xy.length < 4) continue;
    g.beginPath();
    g.moveTo(xy[0], xy[1]);
    for (let i = 2; i < xy.length; i += 2) g.lineTo(xy[i], xy[i + 1]);
    g.setLineDash(s.dash || []);
    if (s.halo) {
      g.globalAlpha = 0.9;
      g.strokeStyle = '#ffffff';
      g.lineWidth = s.halo;
      g.stroke();
    }
    g.globalAlpha = s.alpha ?? 1;
    g.strokeStyle = s.color;
    g.lineWidth = s.width;
    g.stroke();
  }
  g.globalAlpha = 1;
  g.setLineDash([]);
}

// The pieces of the planes ci = 0 in the level f: those with f planes, theirs
// included, between their far side and the eye. Each plane is cut by the
// other two into quarters.
function drawPlanes(g, f, eye) {
  const corner = new Float64Array(N), q = new Float64Array(3), B = view.B;
  for (let i = 0; i < N; i++) {
    const j = (i + 1) % N, l = (i + 2) % N;
    for (const sj of [-1, 1]) for (const sl of [-1, 1]) {
      if (1 + (sj !== eye[j]) + (sl !== eye[l]) !== f) continue;
      const pts = [[0, 0], [sj, 0], [sj, sl], [0, sl]].map(([u, v]) => {
        corner[i] = 0; corner[j] = u * B; corner[l] = v * B;
        project(corner, q, 0);
        return [q[0], q[1]];
      });
      g.beginPath();
      pts.forEach(([x, y], n) => (n ? g.lineTo(x, y) : g.moveTo(x, y)));
      g.closePath();
      g.globalAlpha = PLANE_A;
      g.fillStyle = NEURON[i];
      g.fill();
      g.beginPath();                              // its border, on the faces of the box
      g.moveTo(...pts[1]);
      g.lineTo(...pts[2]);
      g.lineTo(...pts[3]);
      g.globalAlpha = PLANE_EDGE_A;
      g.strokeStyle = NEURON[i];
      g.lineWidth = 1;
      g.stroke();
    }
  }
  g.globalAlpha = 1;
}

// Draws a mark, with the opacity already set on g.
function drawMark(g, { kind, x, y }) {
  const base = g.globalAlpha;
  const disk = (r, color) => { g.beginPath(); g.arc(x, y, r, 0, 2 * Math.PI); g.fillStyle = color; g.fill(); };
  const diamond = (r, color) => {
    g.beginPath();
    g.moveTo(x, y - r); g.lineTo(x + r, y); g.lineTo(x, y + r); g.lineTo(x - r, y);
    g.closePath();
    g.fillStyle = color;
    g.fill();
  };
  // the outline of a square of half-side h, on a white square that sets it off
  const square = (h, width, color) => {
    const o = h + width / 2 + 1.2;
    g.fillStyle = '#ffffff';
    g.fillRect(x - o, y - o, 2 * o, 2 * o);
    g.strokeStyle = color;
    g.lineWidth = width;
    g.strokeRect(x - h, y - h, 2 * h, 2 * h);
  };
  if (kind === 'target') { diamond(MARK.target, '#ffffff'); diamond(0.62 * MARK.target, ACCENT); }
  else if (kind === 'run') { disk(MARK.run, '#ffffff'); disk(0.66 * MARK.run, ACCENT); }
  else if (kind === 'init') square(0.62 * MARK.init, 1.8, INK);
}

// The labels of the axes, beyond their positive ends.
const labels = [];
function placeLabels() {
  const o = new Float64Array(3), q = new Float64Array(3), end = new Float64Array(N);
  project(end, o, 0);
  for (let i = 0; i < N; i++) {
    end.fill(0);
    end[i] = view.B;
    project(end, q, 0);
    let dx = q[0] - o[0], dy = q[1] - o[1];
    const len = Math.hypot(dx, dy) || 1;
    dx /= len; dy /= len;
    labels[i].style.transform = `translate(${q[0] + 15 * dx}px, ${q[1] + 15 * dy}px) translate(-50%, -50%)`;
  }
}

// c_i, the coordinate on the axis
function setLabels() {
  labels.forEach((el, i) => { el.innerHTML = `<i>c</i><sub>${i + 1}</sub>`; });
}

// ---------------------------------------------------------------- training
// Gradient descent on the weights (a, w), for L = Σ (ai wi^k − ci*)² + λ Σ (ai² + wi²),
// from the random initial weights. The largest stable rate for the
// Gauss–Newton part 2 (JᵀJ + λ) of the curvature of the loss is 1/(g + λ),
// where g bounds JᵀJ = wi^(2k−2) (wi² + k² ai²) along the run: we take the
// largest of its values at the start, at the end of each neuron that learns,
// and at the balanced weights of the target, with a margin. The learning rate
// is LR times that, small enough for the descent to follow the gradient flow
// closely. Should the loss ever go up, the step is undone and the rate halved.
// The run trains until each coefficient is where it ends: close to it, or,
// when that is 0 and the neuron dies without regularization and with k ≥ 2,
// so that it only nears 0 slowly (as a power of the time, not exponentially),
// within 1e-4 of the scale of the run. Without regularization, where it ends
// is known from the start (endOf); with it, once the imbalance of the neuron
// has decayed, from then on its weights are balanced (settledLimit).
const train = { run: null, plotDirty: true, hover: -1 };

const jtj = (a, w) => powi(w, 2 * k - 2) * (w * w + k * k * a * a);

// The weights (a, w), w > 0, with k a² − w² = d and a w^k = t (t ≠ 0): where
// w² + d = k t² / w^2k, whose left side grows with w and right side falls.
function endWeights(d, t) {
  const h = w => w * w + d - k * t * t / powi(w, 2 * k);
  let lo = 0, hi = Math.max(1, 2 * Math.sqrt(Math.abs(d)));
  while (h(hi) < 0) hi *= 2;
  for (let it = 0; it < 80; it++) {
    const mid = (lo + hi) / 2;
    if (h(mid) < 0) lo = mid; else hi = mid;
  }
  return [t / powi(hi, k), hi];
}

function startRun() {
  const a = new Float64Array(N), w = new Float64Array(N);
  updateInit();
  initialWeights(a, w);
  let scale = 0, tmax = 0, W = 0;
  for (let i = 0; i < N; i++) {
    scale = Math.max(scale, Math.abs(init[i]), Math.abs(target[i]));
    tmax = Math.max(tmax, Math.abs(target[i]));
    W = Math.max(W, Math.abs(a[i]), Math.abs(w[i]));
  }
  scale = scale || 1;
  const wT = balancedWeight(tmax);
  W = Math.max(W, wT);
  const lim = Float64Array.from(target, (t, i) => (lambda === 0 ? endOf(a[i], w[i], t) : NaN));
  let g = (k + 1) * powi(wT, 2 * k);
  for (let i = 0; i < N; i++) {
    g = Math.max(g, jtj(a[i], w[i]));
    if (lambda === 0 && lim[i] !== 0) {
      const [ae, we] = endWeights(k * a[i] * a[i] - w[i] * w[i], target[i]);
      g = Math.max(g, jtj(ae, we));
    }
  }
  const run = train.run = {
    a, w, c: Float64Array.from(init), start: Float64Array.from(init), target: Float64Array.from(target),
    aStart: Float64Array.from(a), wStart: Float64Array.from(w), W,
    step: 0, frames: 0, status: 'running', scale, lim,
    tol: lim.map(l => (l === 0 && lambda === 0 && k >= 2 ? 1e-4 : 1e-9) * scale),
    st: lambda > 0 ? Array.from(target, t => settle(t)) : null, dEps: 1e-8 * W * W,
    lr: Math.min(LR / (1.2 * g + lambda), 100),
    ga: new Float64Array(N), gw: new Float64Array(N), L: 0,
    a0: new Float64Array(N), w0: new Float64Array(N), c0: new Float64Array(N),
    path: [Float64Array.from(init)], hist: [], nextLog: 1, eps: PATH_EPS * view.B,
  };
  lossGrad(run);
  run.hist.push([0, run.L]);
  trainChanged();
}

// The coordinates, the loss and its gradient at the weights of the run.
function lossGrad(run) {
  const { a, w, c, ga, gw } = run;
  let L = 0;
  for (let i = 0; i < N; i++) {
    const p = powi(w[i], k - 1), wk = p * w[i], ci = c[i] = a[i] * wk, r = ci - target[i];
    L += r * r + lambda * (a[i] * a[i] + w[i] * w[i]);
    ga[i] = 2 * (r * wk + lambda * a[i]);
    gw[i] = 2 * (r * k * a[i] * p + lambda * w[i]);
  }
  run.L = L;
}

// Adds the current point to the path, if it moved enough since its last point.
function addPathPoint(run, force) {
  const P = run.path, last = P[P.length - 1];
  let d2 = 0;
  for (let i = 0; i < N; i++) d2 += (run.c[i] - last[i]) ** 2;
  if (d2 === 0 || (!force && d2 < run.eps * run.eps)) return;
  if (P.length >= MAX_PATH) run.path = P.filter((_, j) => j % 2 === 0);   // too many points: keep every other one
  run.path.push(Float64Array.from(run.c));
}

// One frame of training. The number of steps per frame grows geometrically,
// so that the first steps are seen one by one, and later ones go fast; while a
// point is dragged, the run goes as fast as it can. The run has converged when
// each coefficient is where it ends, or, failing that, when the function stops
// moving altogether (as from a coefficient so small that it would take ages
// to grow).
function advanceRun(fast) {
  const run = train.run, { a, w, c, a0, w0, c0, lim, tol } = run;
  const count = fast ? SPF_MAX : Math.min(SPF_MAX, Math.max(1, Math.floor(RAMP ** run.frames)));
  run.frames++;
  for (let s = 0; s < count && run.status === 'running'; s++) {
    const L = run.L;
    for (let i = 0; i < N; i++) {
      a0[i] = a[i]; w0[i] = w[i]; c0[i] = c[i];
      a[i] -= run.lr * run.ga[i];
      w[i] -= run.lr * run.gw[i];
    }
    lossGrad(run);
    if (!isFinite(run.L)) {
      a.set(a0); w.set(w0); lossGrad(run);
      run.status = 'diverged';
      break;
    }
    if (run.L > L * (1 + 1e-12)) {                // the loss went up: undo the step, and halve the rate
      a.set(a0); w.set(w0); lossGrad(run);
      run.lr /= 2;
      continue;
    }
    run.step++;
    if (run.step >= run.nextLog) {
      run.hist.push([run.step, run.L]);
      run.nextLog = Math.max(run.step + 1, Math.ceil(run.nextLog * 1.05));
    }
    addPathPoint(run, false);
    let move = 0, there = true;
    for (let i = 0; i < N; i++) {
      move = Math.max(move, Math.abs(c[i] - c0[i]));
      let l = lim[i];
      if (l !== l) {                              // not known yet: it is once the weights are balanced
        if (Math.abs(k * a[i] * a[i] - w[i] * w[i]) > run.dEps) { there = false; continue; }
        l = lim[i] = settledLimit(c[i], run.st[i]);
      }
      if (Math.abs(c[i] - l) > tol[i]) there = false;
    }
    if (there) run.status = 'converged';
    else if (move <= 1e-15 * run.scale) run.status = 'stalled';
    else if (run.step >= MAX_STEPS) run.status = 'limit';
  }
  if (run.status !== 'running') {
    addPathPoint(run, true);
    if (run.hist[run.hist.length - 1][0] !== run.step) run.hist.push([run.step, run.L]);
  }
  view.dirty = true;
  train.plotDirty = true;
}

// After a new run, or none: redraw what shows it.
function trainChanged() {
  view.dirty = true;
  train.plotDirty = true;
  train.hover = -1;
  requestDraw();
}

function clearRun() {
  train.run = null;
  trainChanged();
}

// ---------------------------------------------------------------- the loss plot
// The loss against the steps, both on log scales. Pointing at the plot reads
// off the loss at a step.
let plotX = null;
function drawLossPlot() {
  train.plotDirty = false;
  const cv = $('nm-loss'), dpr = Math.min(window.devicePixelRatio || 1, 2);
  const W = Math.max(1, Math.round(cv.clientWidth * dpr)), H = Math.max(1, Math.round(cv.clientHeight * dpr));
  if (cv.width !== W || cv.height !== H) { cv.width = W; cv.height = H; }
  const g = cv.getContext('2d'), run = train.run;
  g.clearRect(0, 0, W, H);
  plotX = null;
  if (!run) return;
  const lg = x => Math.log10(Math.max(x, 1e-300));
  const xs = run.hist.map(([s]) => Math.log10(s + 1)), ys = run.hist.map(([, L]) => lg(L));
  let yhi = Math.max(...ys), ylo = Math.min(...ys);
  ylo = Math.max(ylo, yhi - 10);
  if (yhi - ylo < 1) { ylo = (yhi + ylo) / 2 - 0.5; yhi = ylo + 1; }
  const xhi = Math.max(2, xs[xs.length - 1]), pad = 5 * dpr;
  const X = x => pad + (W - 2 * pad) * x / xhi, Y = y => H - pad - (H - 2 * pad) * (Math.max(y, ylo) - ylo) / (yhi - ylo);
  g.strokeStyle = ACCENT;
  g.lineWidth = 1.6 * dpr;
  g.lineJoin = 'round';
  g.beginPath();
  xs.forEach((x, i) => (i ? g.lineTo(X(x), Y(ys[i])) : g.moveTo(X(x), Y(ys[i]))));
  g.stroke();
  plotX = xs.map(x => X(x) / dpr);                // for the pointer, in CSS pixels

  const h = train.hover;
  if (h >= 0 && h < xs.length) {
    const x = X(xs[h]), y = Y(ys[h]);
    g.strokeStyle = 'rgba(23, 26, 33, 0.3)';
    g.lineWidth = dpr;
    g.beginPath();
    g.moveTo(x, pad);
    g.lineTo(x, H - pad);
    g.stroke();
    g.beginPath();
    g.arc(x, y, 3.5 * dpr, 0, 2 * Math.PI);
    g.fillStyle = '#ffffff';
    g.fill();
    g.beginPath();
    g.arc(x, y, 2.3 * dpr, 0, 2 * Math.PI);
    g.fillStyle = ACCENT;
    g.fill();
    const [step, L] = run.hist[h];
    g.font = `${11 * dpr}px sans-serif`;
    g.fillStyle = INK;
    g.textBaseline = 'top';
    const text = `step ${step.toLocaleString('en-US')}: ${sci(L)}`, tw = g.measureText(text).width;
    g.fillText(text, x + 6 * dpr + tw > W - pad ? x - 6 * dpr - tw : x + 6 * dpr, pad);
  }
}

function sci(x) {
  if (x === 0) return '0';
  if (x >= 0.01 && x < 1000) return String(Number(x.toPrecision(3)));
  const [m, e] = x.toExponential(2).split('e');
  return `${m}e${e.replace('+', '')}`;
}

// ---------------------------------------------------------------- the network
// A diagram of the network: the inputs xi, the neurons and the output f, with
// an edge for each weight, wi from xi to neuron i, and ai from it to f. An
// edge is more opaque the larger its weight, against the largest of the
// initial weights, of the current ones, and of the balanced weights of the
// largest coordinate of the target, and dashed when the weight is negative
// (wi can be negative too, now that the weights are random). A neuron fills with red as it activates: as |ci| grows to where
// it ends (or, for a neuron that dies, to |ci*|). It shows the weights of the
// run, or, with none, those of the initialization.
// every node is a circle of radius r, with the same gray outline
const NET = { xIn: 38, xHid: 112, xOut: 188, rows: [34, 79, 124], yOut: 79, r: 8, stroke: MUTED, strokeWidth: 1.4, head: 13 };
const NET_DASH = '5 3';
const net = { w: [], a: [], hid: [], head: null, sig: '' };

function initNet() {
  const svg = $('nm-net'), ns = 'http://www.w3.org/2000/svg';
  const el = (tag, attrs, parent = svg) => {
    const e = document.createElementNS(ns, tag);
    for (const [name, v] of Object.entries(attrs)) e.setAttribute(name, v);
    parent.append(e);
    return e;
  };
  // a label: a letter, in italics, with an index
  const label = (x, y, letter, index, attrs = {}) => {
    const t = el('text', { x, y, 'text-anchor': 'middle', ...attrs });
    el('tspan', { 'font-style': 'italic' }, t).textContent = letter;
    if (index) el('tspan', { 'font-size': '0.72em', dy: '0.3em' }, t).textContent = index;
    return t;
  };
  // an edge between two nodes, shortened to their rims: a faint line, always
  // there, under the line of the weight
  const edge = (x0, y0, r0, x1, y1, r1, i) => {
    const dx = x1 - x0, dy = y1 - y0, d = Math.hypot(dx, dy), ux = dx / d, uy = dy / d;
    const at = { x1: x0 + ux * r0, y1: y0 + uy * r0, x2: x1 - ux * r1, y2: y1 - uy * r1 };
    el('line', { ...at, stroke: '#e3e7eb', 'stroke-width': 1 });
    return el('line', { ...at, stroke: NEURON[i], 'stroke-width': 2.2, 'stroke-linecap': 'round', 'stroke-opacity': 0 });
  };
  const node = { r: NET.r, fill: '#ffffff', stroke: NET.stroke, 'stroke-width': NET.strokeWidth };
  net.head = el('text', { x: NET.xHid, y: NET.head, 'text-anchor': 'middle', class: 'nm-net-w' });
  NET.rows.forEach((y, i) => {
    net.w[i] = edge(NET.xIn, y, NET.r, NET.xHid, y, NET.r, i);
    net.a[i] = edge(NET.xHid, y, NET.r, NET.xOut, NET.yOut, NET.r, i);
    label((NET.xIn + NET.xHid) / 2, y - 6, 'w', String(i + 1), { class: 'nm-net-w' });
    // the label of ai beside the middle of its edge, away from the middle row
    const mx = (NET.xHid + NET.xOut) / 2, my = (y + NET.yOut) / 2, dx = NET.xOut - NET.xHid, dy = NET.yOut - y;
    const d = Math.hypot(dx, dy), s = i === 2 ? 1 : -1, off = 8;
    label(mx - s * off * dy / d, my + s * off * dx / d + (s > 0 ? 6 : 0), 'a', String(i + 1), { class: 'nm-net-w' });
    el('circle', { cx: NET.xIn, cy: y, ...node });
    label(NET.xIn - 20, y + 4, 'x', String(i + 1));
    net.hid[i] = el('circle', { cx: NET.xHid, cy: y, ...node });
  });
  el('circle', { cx: NET.xOut, cy: NET.yOut, ...node });
  label(NET.xOut, NET.yOut + 4, 'f', '', { 'font-size': '12px' });
}

// white, blended with ACCENT by the share s
function towardAccent(s) {
  const A = [0xa8, 0x20, 0x3a];
  return `rgb(${A.map(v => Math.round(255 + (v - 255) * s)).join(', ')})`;
}

function updateNet() {
  const run = train.run;
  let a = run && run.a, w = run && run.w, a0 = run && run.aStart, w0 = run && run.wStart;
  const c = run ? run.c : init, start = run ? run.start : init, goal = run ? run.target : target;
  if (!run) { a = a0 = new Float64Array(N); w = w0 = new Float64Array(N); initialWeights(a, w); }
  let M = 0, ref = 0;
  for (let i = 0; i < N; i++) {
    M = Math.max(M, Math.abs(start[i]), Math.abs(goal[i]));
    ref = Math.max(ref, Math.abs(a[i]), Math.abs(w[i]), Math.abs(a0[i]), Math.abs(w0[i]));
  }
  ref = Math.max(ref, balancedWeight(Math.max(...Array.from(goal, Math.abs))));
  const op = x => Math.min(1, Math.abs(x) / (ref || 1)).toFixed(3);
  const st = [], sig = [k];
  for (let i = 0; i < N; i++) {
    const l = run ? run.lim[i] : NaN;              // NaN while not known
    const end = (l === l && l !== 0 ? Math.abs(l) : Math.abs(goal[i])) || M || 1;
    st.push({ w: op(w[i]), a: op(a[i]), wNeg: w[i] < 0, aNeg: a[i] < 0, on: Math.min(1, Math.abs(c[i]) / end).toFixed(3) });
    sig.push(...Object.values(st[i]));
  }
  const s = sig.join();
  if (s === net.sig) return;
  net.sig = s;
  net.head.innerHTML = `σ(<tspan font-style="italic">t</tspan>) = <tspan font-style="italic">t</tspan><tspan font-size="0.75em" dy="-0.45em">${k}</tspan>`;
  st.forEach((v, i) => {
    net.w[i].setAttribute('stroke-opacity', v.w);
    net.w[i].setAttribute('stroke-dasharray', v.wNeg ? NET_DASH : 'none');
    net.a[i].setAttribute('stroke-opacity', v.a);
    net.a[i].setAttribute('stroke-dasharray', v.aNeg ? NET_DASH : 'none');
    net.hid[i].setAttribute('fill', towardAccent(+v.on));
  });
}

// ---------------------------------------------------------------- frame loop
let raf = 0;
function requestDraw() { if (!raf) raf = requestAnimationFrame(frame); }
function frame() {
  raf = 0;
  const run = train.run, training = !!(run && run.status === 'running' && visible);
  if (training) advanceRun(!!gesture && gesture.moved && gesture.kind === 'target');
  let more = training;
  if (easeBox()) more = true;
  if (view.dirty) render();
  if (train.plotDirty) drawLossPlot();
  updateNet();
  if (more) requestDraw();
}

// ---------------------------------------------------------------- changes
// The target and the initial weights, set from the view or the controls. New
// initial weights start a run; a new target, degree, scale or regularization
// starts the run again (from the same draw of the weights).
function setTarget(c) {
  for (let i = 0; i < N; i++) target[i] = clampCoef(c[i]);
  if (train.run) startRun();
  else { view.dirty = true; requestDraw(); }
}

// New random initial weights, and a run from them.
function newWeights() {
  drawWeights();
  startRun();
}

function setSigma(s) {
  sigma = s;
  syncSigma();
  startRun();
}

const clampCoef = x => (isFinite(x) ? Math.max(-MAX_COEF, Math.min(MAX_COEF, x)) : 0);

function fmt(x) {
  if (x === 0) return '0';
  if (Math.abs(x) >= 0.01) return String(Math.round(x * 1000) / 1000);
  return String(Number(x.toPrecision(2)));
}

// The slider of the scale shows σ, unless it is being moved.
function syncSigma() {
  const sigmaIn = $('nm-size');
  $('nm-size-out').textContent = fmt(sigma);
  if (document.activeElement !== sigmaIn) sigmaIn.value = Math.log10(sigma);
}

// ---------------------------------------------------------------- controls
function setDegree(d) {
  k = d;
  updateInit();
  if (train.run) startRun();
  else { view.dirty = true; requestDraw(); }
}

function initView() {
  const cv = view.canvas;
  const pos = e => { const r = cv.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
  const hover = (x, y) => { cv.style.cursor = markAt(x, y) ? 'move' : ''; };

  // A press on ◆ drags it, parallel to the screen, at its depth; a press
  // elsewhere turns the box when it moves. A click does nothing.
  cv.addEventListener('pointerdown', e => {
    if (gesture || (e.pointerType === 'mouse' && e.button !== 0)) return;
    const [x, y] = pos(e), hit = markAt(x, y);
    gesture = { id: e.pointerId, kind: hit || 'press', x0: x, y0: y, x, y, moved: false };
    if (hit) {
      const q = new Float64Array(3);
      project(target, q, 0);
      Object.assign(gesture, { dx: q[0] - x, dy: q[1] - y, z: q[2] });
      view.frozen = true;
    }
    cv.setPointerCapture(e.pointerId);
    view.dirty = true;
    requestDraw();
  });
  cv.addEventListener('pointermove', e => {
    const [x, y] = pos(e);
    if (!gesture) {
      if (e.pointerType !== 'touch') hover(x, y);
      return;
    }
    if (e.pointerId !== gesture.id) return;
    if (!gesture.moved && Math.hypot(x - gesture.x0, y - gesture.y0) < CLICK_PX) return;
    gesture.moved = true;
    if (gesture.kind === 'press' || gesture.kind === 'orbit') {
      gesture.kind = 'orbit';
      cv.classList.add('nm-grabbing');
      orbit(x - gesture.x, y - gesture.y);
      gesture.x = x;
      gesture.y = y;
      requestDraw();
      return;
    }
    setTarget(snapSmall(atDepth(x + gesture.dx, y + gesture.dy, gesture.z, new Float64Array(N))));
  });
  const end = e => {
    if (!gesture || e.pointerId !== gesture.id) return;
    const [x, y] = pos(e);
    gesture = null;
    view.frozen = false;
    cv.classList.remove('nm-grabbing');
    if (e.pointerType !== 'touch' && e.type === 'pointerup') hover(x, y);
    view.dirty = true;
    requestDraw();
  };
  cv.addEventListener('pointerup', end);
  cv.addEventListener('pointercancel', end);
  cv.addEventListener('keydown', e => {
    if (e.key === 'Enter' || e.key === ' ') {
      e.preventDefault();
      startRun();
      return;
    }
    const d = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[e.key];
    if (!d) return;
    e.preventDefault();
    const px = KEY_STEP / ORBIT_SPEED;
    orbit(d[0] * px, d[1] * px);
    requestDraw();
  });
  new ResizeObserver(() => { resizeView(); requestDraw(); }).observe(cv);
  resizeView();
}

// 'target' if ◆ is within GRAB_PX of the screen point (x, y), else null.
function markAt(x, y) {
  const q = new Float64Array(3);
  project(target, q, 0);
  return Math.hypot(q[0] - x, q[1] - y) < GRAB_PX ? 'target' : null;
}

function init_() {
  view.canvas = $('nm-view');
  view.ctx = view.canvas.getContext('2d');
  if (!view.ctx) {
    root.classList.add('nm-nocanvas');
    $('nm-status').textContent = 'This viewer needs a browser that can draw on a canvas.';
    return;
  }
  for (let i = 0; i < N; i++) labels.push($(`nm-lbl-${i + 1}`));
  resetCam();
  initView();
  initNet();

  const degreeIn = $('nm-degree'), degreeOut = $('nm-degree-out');
  degreeIn.min = DEGREES[0];
  degreeIn.max = DEGREES[DEGREES.length - 1];
  k = Math.round(parseFloat(degreeIn.value)) || k;  // as the browser may have restored it
  degreeOut.textContent = k;
  degreeIn.addEventListener('input', () => {
    const d = Math.round(parseFloat(degreeIn.value));
    degreeOut.textContent = d;
    if (d !== k) setDegree(d);
  });

  const sigmaIn = $('nm-size');
  sigmaIn.min = SIGMA_LO;
  sigmaIn.max = SIGMA_HI;
  sigmaIn.addEventListener('input', () => setSigma(10 ** parseFloat(sigmaIn.value)));

  const regIn = $('nm-reg'), regOut = $('nm-reg-out');
  lambda = parseFloat(regIn.value) || 0;          // as the browser may have restored it
  regOut.textContent = lambda.toFixed(2);
  regIn.addEventListener('input', () => {
    lambda = parseFloat(regIn.value) || 0;
    regOut.textContent = lambda.toFixed(2);
    if (train.run) startRun();
    else { view.dirty = true; requestDraw(); }
  });

  $('nm-target').addEventListener('click', () => {
    const c = new Float64Array(N);
    for (let i = 0; i < N; i++) c[i] = (Math.random() < 0.5 ? -1 : 1) * Math.round(100 * (0.2 + 0.8 * Math.random())) / 100;
    setTarget(c);
  });
  $('nm-weights').addEventListener('click', newWeights);
  $('nm-clear').addEventListener('click', clearRun);

  const planesIn = $('nm-planes');
  showPlanes = planesIn.checked;
  planesIn.addEventListener('change', () => { showPlanes = planesIn.checked; view.dirty = true; requestDraw(); });

  const loss = $('nm-loss');
  loss.addEventListener('pointermove', e => {
    if (!plotX) return;
    const x = e.clientX - loss.getBoundingClientRect().left;
    let best = -1, bd = Infinity;
    plotX.forEach((px, i) => { const d = Math.abs(px - x); if (d < bd) { bd = d; best = i; } });
    if (best !== train.hover) { train.hover = best; train.plotDirty = true; requestDraw(); }
  });
  loss.addEventListener('pointerleave', () => { train.hover = -1; train.plotDirty = true; requestDraw(); });
  new ResizeObserver(() => { train.plotDirty = true; requestDraw(); }).observe(loss);

  new IntersectionObserver(es => {
    visible = es.some(e => e.isIntersecting);
    if (visible) requestDraw();
  }).observe(root);

  setLabels();
  syncSigma();
  updateInit();
  view.B = boxGoal();
  startRun();
}

if (window.NM_DEBUG) {
  // setWeights(a, w) starts a run from the weights a, w (at the current σ)
  const setWeights = (a, w) => { for (let i = 0; i < N; i++) { zA[i] = a[i] / sigma; zW[i] = w[i] / sigma; } updateInit(); startRun(); };
  window.NM_DEBUG = { settle, limitOf, endOf, endWeights, powi, niceCeil, project, fromView, atDepth,
                      layerOf, addPolyline, markAt, startRun, advanceRun, lossGrad, setTarget, newWeights, setWeights, setSigma, setDegree,
                      orbit, resetCam, render, updateNet, net, view, train, target, init, zA, zW,
                      get k() { return k; }, get lambda() { return lambda; }, get sigma() { return sigma; } };
}
init_();
})();
