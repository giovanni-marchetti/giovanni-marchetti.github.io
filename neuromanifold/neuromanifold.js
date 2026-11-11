/*
 * Neuromanifold viewer for the personal page.
 *
 * A residual network with two layers of one neuron each, no biases and a
 * polynomial activation σ of degree d computes
 *     f(x) = σ(w2·h(x)) + h(x),   h(x) = σ(w1·x) + x,
 * a polynomial of degree d² in x; without its skip connections, it is the
 * plain network f(x) = σ(w2·σ(w1·x)). As (w1, w2) ranges over the disk
 * w1² + w2² ≤ R², f traces a surface, the neuromanifold, in the space of
 * polynomials of degree ≤ d² (of dimension d² + 1). That space carries the
 * Bombieri–Weyl inner product <x^i, x^j> = δ_ij / C(d², i), and the surface
 * is shown in a 3D view, by an orthogonal projection for it: a random one,
 * or the top three principal components of the surface (PCA), sampled with
 * its area element. Shift-drag rotates the projection through the hidden
 * dimensions. Features of the surface itself (singularities,
 * self-intersections) are there in every projection; artifacts of a
 * projection move as it rotates.
 * The surface is colored by the weights, as is the disk of weights.
 * Pointing at the disk of weights marks the function of those weights in
 * the view; clicking it trains the network from there, by gradient descent
 * on the squared Bombieri–Weyl distance to a target (a teacher network plus
 * noise), and the path of the training is drawn on the disk and in the view.
 *
 * Rendering uses WebGL 2, without libraries.
 */
(() => {
'use strict';

const root = document.querySelector('#neuromanifold .nm');
if (!root) return;
const $ = id => document.getElementById(id);

// ---------------------------------------------------------------- settings
const GRID = 121;                  // samples per side of the weight square; odd, so that w = 0 is sampled
const LINE_EVERY = 10;             // an iso-weight line every LINE_EVERY samples; divides GRID - 1
const MIN_DEG = 2, MAX_DEG = 5;
const MAX_COEF = 100;
const CAM_DIST = 4, FOV = 36 * Math.PI / 180;
const FILL = 0.9;                  // the picture fills this share of the view (of its half-width, from the center)
const MAX_ZOOM = 2.5;              // but it is never more than this times the size at which its ball fits the view
const ORBIT_SPEED = 0.008;         // radians per pixel of drag
const KEY_STEP = 0.08;             // radians per arrow key
const NV = GRID * GRID;
const MID = (GRID - 1) / 2;        // index of w = 0
const BG = [1, 1, 1];
const MARK_R = 6;                  // radius of the mark, in CSS pixels
const MARK_CORE = 0.5, MARK_RIM = 0.8;  // the mark: a dark core, a white ring from MARK_CORE to MARK_RIM, a dark rim
const INK = '#161a20', INK_GL = 'vec3(0.086, 0.102, 0.125)';
const ACCENT = '#a8203a', ACCENT_GL = 'vec3(0.659, 0.125, 0.227)';
const LINE_INK = 'rgba(23, 26, 33, ', LINE_A = 0.2, AXIS_A = 0.7;   // the grid lines, and the weight axes
// The marks in the view: the probe (a bull's-eye), the weights of the run (a
// dot) and the target of the training (a diamond), with their radii in CSS
// pixels.
const STYLE = { probe: 0, run: 1, target: 2 };
const MARK_SIZE = [MARK_R, 5, 7.5];
const HIDDEN_ALPHA = 0.5;          // the opacity of marks hidden behind the surface
// Training
const PATH_EPS = 0.004;            // the path gets a point every PATH_EPS · R of movement of the weights
const MAX_PATH = 4000;             // points of the path at most
const MAX_STEPS = 3e6;             // gradient steps of a run at most
const SPF_MAX = 2000;              // gradient steps per frame at most; the first frames take fewer
const REG = 0.1;                   // the regularization λ ||w||², when on, has λ = REG ρ²/R² (see regLambda)

// ---------------------------------------------------------------- state
let deg = 2;
const coef = new Float64Array(MAX_DEG + 1);   // σ(t) = Σ coef[k] t^k
coef[2] = 1;
let skip = true;                   // whether the network has its skip connections
let range = 1;
let showLines = true, xray = false;
let geo = null;                    // the sampled surface, see recompute()
let probe = null;                  // the weights { w1, w2 } marked in the view, or null
let showProbe = true;              // whether the probe is drawn (it follows the pointer either way)
let visible = true;

// ---------------------------------------------------------------- the network
// Returns a function (w1, w2, F, J1, J2) that writes the coefficients (lowest
// degree first) of f and of ∂f/∂w1, ∂f/∂w2 into arrays of length d² + 1, for
// σ of degree d ≥ 1 with coefficients c, with or without the skip connections:
// f = σ(w2 h) + s·h with h = σ(w1 x) + s·x, where s is 1 or 0. Then
//   ∂f/∂w1 = (w2·σ'(w2 h) + s) · σ'(w1 x) x,    ∂f/∂w2 = σ'(w2 h) · h.
function makeNetwork(c, d, skip) {
  const L = d * d + 1;
  const dc = new Float64Array(d);                 // coefficients of σ'
  for (let k = 1; k <= d; k++) dc[k - 1] = k * c[k];
  const h = new Float64Array(d + 1), u = new Float64Array(d + 1), dh = new Float64Array(d + 1);
  const g = new Float64Array(L), q = new Float64Array(L), tmp = new Float64Array(L);

  // out = Σ_{k ≤ cd} cf[k] u^k by Horner's rule, with u = w2·h of degree d.
  // Returns the degree of out.
  function compose(cf, cd, out) {
    out.fill(0);
    out[0] = cf[cd];
    let da = 0;
    for (let k = cd - 1; k >= 0; k--) {
      tmp.fill(0, 0, da + d + 1);
      for (let i = 0; i <= da; i++) {
        const a = out[i];
        if (a === 0) continue;
        for (let j = 0; j <= d; j++) tmp[i + j] += a * u[j];
      }
      da += d;
      for (let i = 0; i <= da; i++) out[i] = tmp[i];
      out[0] += cf[k];
    }
    return da;
  }

  return function (w1, w2, F, J1, J2) {
    // h = σ(w1 x) + s·x and dh = ∂h/∂w1 = σ'(w1 x)·x
    let p = 1;                                    // w1^k
    dh[0] = 0;
    for (let k = 0; k <= d; k++) {
      h[k] = c[k] * p;
      if (k < d) dh[k + 1] = (k + 1) * c[k + 1] * p;
      p *= w1;
    }
    if (skip) h[1] += 1;
    for (let k = 0; k <= d; k++) u[k] = w2 * h[k];

    const dg = compose(c, d, g);                  // σ(w2 h)
    F.fill(0);
    for (let i = 0; i <= dg; i++) F[i] = g[i];
    if (skip) for (let k = 0; k <= d; k++) F[k] += h[k];

    const dq = compose(dc, d - 1, q);             // σ'(w2 h)
    J1.fill(0);
    J2.fill(0);
    for (let i = 0; i <= dq; i++) {
      const a = q[i];
      if (a === 0) continue;
      for (let j = 0; j <= d; j++) {
        J1[i + j] += w2 * a * dh[j];
        J2[i + j] += a * h[j];
      }
    }
    if (skip) for (let j = 0; j <= d; j++) J1[j] += dh[j];
  };
}

// The dimension of the affine span of the neuromanifold. It is the rank of
// the coefficients of f - f(0,0), as polynomials in (w1, w2), and is computed
// from those polynomials: samples of them are too badly conditioned.
function affineSpan(c, d, skip) {
  const X = d * d + 1, A = d * d + 1, B = d + 1;   // degrees in x, w1, w2
  const at = (i, a, b) => (i * A + a) * B + b, size = X * A * B;
  // u = w2·h, with h = σ(w1 x) + s·x (s = 1 with the skip connections, 0 without)
  const uTerms = skip ? [[1, 0, 1, 1]] : [];      // [degree in x, in w1, in w2, coefficient]
  for (let k = 0; k <= d; k++) if (c[k] !== 0) uTerms.push([k, k, 1, c[k]]);
  // g = σ(u), by Horner's rule
  let g = new Float64Array(size), tmp = new Float64Array(size);
  g[0] = c[d];
  for (let k = d - 1; k >= 0; k--) {
    tmp.fill(0);
    for (let i = 0; i < X; i++) for (let a = 0; a < A; a++) for (let b = 0; b < B; b++) {
      const gv = g[at(i, a, b)];
      if (gv === 0) continue;
      for (const [ui, ua, ub, uv] of uTerms)
        if (i + ui < X && a + ua < A && b + ub < B) tmp[at(i + ui, a + ua, b + ub)] += gv * uv;
    }
    [g, tmp] = [tmp, g];
    g[0] += c[k];
  }
  // rows: the coefficients of x^i in f - f(0,0) (the skip connection adds
  // nothing to them but the terms c_k w1^k x^k of h), with columns the
  // monomials w1^a w2^b ≠ 1
  if (skip) for (let k = 1; k <= d; k++) g[at(k, k, 0)] += c[k];
  const cols = A * B - 1, M = [];
  for (let i = 0; i < X; i++) {
    const row = new Float64Array(cols);
    let big = 0;
    for (let m = 1; m <= cols; m++) { row[m - 1] = g[i * A * B + m]; big = Math.max(big, Math.abs(row[m - 1])); }
    if (big > 0) { for (let m = 0; m < cols; m++) row[m] /= big; M.push(row); }
  }
  // Gaussian elimination with partial pivoting, on rows scaled to max 1
  let rank = 0;
  for (let col = 0; col < cols && rank < M.length; col++) {
    let p = rank;
    for (let r = rank + 1; r < M.length; r++) if (Math.abs(M[r][col]) > Math.abs(M[p][col])) p = r;
    if (Math.abs(M[p][col]) < 1e-9) continue;
    [M[rank], M[p]] = [M[p], M[rank]];
    for (let r = rank + 1; r < M.length; r++) {
      const f = M[r][col] / M[rank][col];
      if (f !== 0) for (let m = col; m < cols; m++) M[r][m] -= f * M[rank][m];
    }
    rank++;
  }
  return rank;
}

function binomial(n, k) {
  let r = 1;
  for (let i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;
}

// ---------------------------------------------------------------- linear algebra
// Eigen-decomposition of the symmetric n x n matrix A (row-major) by cyclic
// Jacobi rotations. Returns the eigenvalues in decreasing order and the
// eigenvectors as the rows of an n x n matrix, in the same order.
function eigenSym(A, n) {
  const a = Float64Array.from(A);
  const v = new Float64Array(n * n);
  for (let i = 0; i < n; i++) v[i * n + i] = 1;
  let scale = 0;
  for (let i = 0; i < n * n; i++) scale += a[i] * a[i];
  for (let sweep = 0; sweep < 60; sweep++) {
    let off = 0;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) off += a[p * n + q] * a[p * n + q];
    if (off <= 1e-30 * scale) break;
    for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
      const apq = a[p * n + q];
      if (apq === 0) continue;
      const theta = (a[q * n + q] - a[p * n + p]) / (2 * apq);
      const t = (theta >= 0 ? 1 : -1) / (Math.abs(theta) + Math.sqrt(theta * theta + 1));
      const cs = 1 / Math.sqrt(t * t + 1), sn = t * cs;
      for (let k = 0; k < n; k++) {               // columns p, q
        const kp = a[k * n + p], kq = a[k * n + q];
        a[k * n + p] = cs * kp - sn * kq;
        a[k * n + q] = sn * kp + cs * kq;
      }
      for (let k = 0; k < n; k++) {               // rows p, q
        const pk = a[p * n + k], qk = a[q * n + k];
        a[p * n + k] = cs * pk - sn * qk;
        a[q * n + k] = sn * pk + cs * qk;
      }
      for (let k = 0; k < n; k++) {               // eigenvectors, as columns of v
        const kp = v[k * n + p], kq = v[k * n + q];
        v[k * n + p] = cs * kp - sn * kq;
        v[k * n + q] = sn * kp + cs * kq;
      }
    }
  }
  const order = [...Array(n).keys()].sort((i, j) => a[j * n + j] - a[i * n + i]);
  const values = new Float64Array(n), vectors = new Float64Array(n * n);
  order.forEach((col, r) => {
    values[r] = Math.max(a[col * n + col], 0);
    for (let k = 0; k < n; k++) vectors[r * n + k] = v[k * n + col];
  });
  return { values, vectors };
}

// Rotates rows i and j of the row-major matrix A (with n columns) by angle th.
function rotateRows(A, n, i, j, th) {
  const c = Math.cos(th), s = Math.sin(th);
  for (let k = 0; k < n; k++) {
    const x = A[i * n + k], y = A[j * n + k];
    A[i * n + k] = c * x + s * y;
    A[j * n + k] = -s * x + c * y;
  }
}

// Gram–Schmidt on the rows of the n x n matrix A.
function orthonormalize(A, n) {
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < i; j++) {
      let d = 0;
      for (let k = 0; k < n; k++) d += A[i * n + k] * A[j * n + k];
      for (let k = 0; k < n; k++) A[i * n + k] -= d * A[j * n + k];
    }
    let s = 0;
    for (let k = 0; k < n; k++) s += A[i * n + k] * A[i * n + k];
    s = Math.sqrt(s);
    if (s < 1e-12) {                              // degenerate: restart the row from a random vector
      for (let k = 0; k < n; k++) A[i * n + k] = gauss();
      i--;
      continue;
    }
    for (let k = 0; k < n; k++) A[i * n + k] /= s;
  }
  return A;
}

function gauss() {
  let u = 0;
  while (u === 0) u = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * Math.random());
}

function randomOrthogonal(n) {
  const A = new Float64Array(n * n);
  for (let i = 0; i < n * n; i++) A[i] = gauss();
  return orthonormalize(A, n);
}

function identity(n) {
  const A = new Float64Array(n * n);
  for (let i = 0; i < n; i++) A[i * n + i] = 1;
  return A;
}

// ---------------------------------------------------------------- colors
// Colors are made in OKLab, for even steps of lightness and hue.
const toSrgb = c => { c = Math.min(Math.max(c, 0), 1); return c <= 0.0031308 ? 12.92 * c : 1.055 * Math.pow(c, 1 / 2.4) - 0.055; };
function oklabToRgb8(L, A, B, out, o) {
  const l = (L + 0.3963377774 * A + 0.2158037573 * B) ** 3;
  const m = (L - 0.1055613458 * A - 0.0638541728 * B) ** 3;
  const s = (L - 0.0894841775 * A - 1.2914855480 * B) ** 3;
  out[o] = Math.round(255 * toSrgb(4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s));
  out[o + 1] = Math.round(255 * toSrgb(-1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s));
  out[o + 2] = Math.round(255 * toSrgb(-0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s));
}

// The color of the weights R·(x, y): hue for the direction, chroma for the size.
// Weights that give the same function (see sym in recompute) get the same
// color, with hues that still run through all hues: when (±w1, ±w2) do, the
// hue is four times the angle of (|w1|, |w2|); when (w1, w2) and (−w1, −w2)
// do, it is twice the angle of (w1, w2).
function weightColor(x, y, out, o, sym) {
  const rho = Math.min(1, Math.hypot(x, y));
  const th = sym === 'mirror' ? 4 * Math.atan2(Math.abs(y), Math.abs(x))
           : sym === 'antipodal' ? 2 * Math.atan2(y, x) : Math.atan2(y, x);
  oklabToRgb8(0.74 - 0.06 * rho, 0.13 * rho * Math.cos(th), 0.13 * rho * Math.sin(th), out, o);
}

// ---------------------------------------------------------------- the weight grid
// The grid square [-1, 1]² is mapped onto the unit disk (and then scaled by
// R) by (s, t) ↦ (s √(1 - t²/2), t √(1 - s²/2)), which keeps the axes.
const squareToDisk = (s, t) => [s * Math.sqrt(1 - t * t / 2), t * Math.sqrt(1 - s * s / 2)];
function diskToSquare(x, y) {
  const x2 = x * x, y2 = y * y, k = 2 * Math.SQRT2;
  const sq = z => Math.sqrt(Math.max(z, 0));
  return [0.5 * (sq(2 + x2 - y2 + k * x) - sq(2 + x2 - y2 - k * x)),
          0.5 * (sq(2 - x2 + y2 + k * y) - sq(2 - x2 + y2 - k * y))];
}

// The cells of the grid (index b·(GRID − 1) + a for the cell from vertex
// (a, b) to (a + 1, b + 1)) within two cells of the weights (w1, w2), and of
// their images under the symmetry sym (see recompute), which give the same
// function.
function cellsNear(w1, w2, sym) {
  const [s, t] = diskToSquare(w1 / range, w2 / range), C = GRID - 1;
  const a0 = Math.min(Math.max(Math.floor((s + 1) * MID), 0), C - 1);
  const b0 = Math.min(Math.max(Math.floor((t + 1) * MID), 0), C - 1);
  const cells = new Set();
  const around = (a, b) => {
    for (let j = b - 2; j <= b + 2; j++) for (let i = a - 2; i <= a + 2; i++)
      if (i >= 0 && j >= 0 && i < C && j < C) cells.add(j * C + i);
  };
  around(a0, b0);
  if (sym !== 'none') around(C - 1 - a0, C - 1 - b0);
  if (sym === 'mirror') { around(C - 1 - a0, b0); around(a0, C - 1 - b0); }
  return cells;
}

// ---------------------------------------------------------------- the surface
// Samples f over the disk of weights w1² + w2² ≤ R² and computes its principal
// components. geo = { d, D, n, nn, Y, C, trC, lambda, E, W1, W2, center, span, embed, net, bw, mu, scale, gmax, sym }:
//   Y      NV x nn, the samples in Bombieri–Weyl orthonormal coordinates,
//          centered and scaled to max |coordinate| = 1 (nn = max(n, 4): the
//          coordinates past n are 0);
//   C, E   the covariance (with the area element as weight) and its
//          eigenvectors, as rows, with eigenvalues lambda;
//   W1, W2 the weights of each sample;
//   center the center of the view, in the same coordinates as Y;
//   embed  (w1, w2, out) ↦ the coordinates of f for any weights, as in Y;
//   net    the network (see makeNetwork), for this σ and these skip connections;
//   bw     the factors 1/√C(D, i) from monomial to BW orthonormal coordinates;
//   mu, scale  the center and the scale of Y: Y = (BW coordinates − mu) / scale;
//   gmax   the largest eigenvalue of JᵀJ (BW metric) over the samples, a bound
//          for the curvature of the loss in the training (as its Gauss–Newton
//          part is 2 JᵀJ);
//   sym    the weights that give the same function as (w1, w2): (±w1, ±w2)
//          ('mirror'), or (−w1, −w2) ('antipodal'), or no others ('none').
function effectiveDegree() {
  for (let k = deg; k >= 0; k--) if (coef[k] !== 0) return k;
  return -1;
}

function recompute() {
  const d = effectiveDegree();
  if (d < 1) {
    geo = null;
    const f = d === 0 ? (skip ? 'σ is constant, so f(x) = 2σ(0) + x' : 'σ is constant, so f(x) = σ(0)')
                      : (skip ? 'σ is zero, so f(x) = x' : 'σ is zero, and so is f');
    setStatus(f + ' for all weights: the neuromanifold is a single point.');
    afterGeometry();
    return;
  }
  const D = d * d, n = D + 1, nn = Math.max(n, 4);
  const net = makeNetwork(Float64Array.from(coef), d, skip);   // a copy, as σ may be edited while geo is in use
  const bw = new Float64Array(n);                 // x^i ↦ x^i / sqrt(C(D, i)) is BW-orthonormal
  for (let i = 0; i < n; i++) bw[i] = 1 / Math.sqrt(binomial(D, i));
  const F = new Float64Array(n), J1 = new Float64Array(n), J2 = new Float64Array(n);
  const Y = new Float64Array(NV * nn), wt = new Float64Array(NV);
  const W1 = new Float64Array(NV), W2 = new Float64Array(NV);
  let W = 0, gmax = 0;
  for (let b = 0; b < GRID; b++) for (let a = 0; a < GRID; a++) {
    // The grid square [-1, 1]² is mapped onto the disk of radius R by
    // (s, t) ↦ R (s √(1 - t²/2), t √(1 - s²/2)), which keeps the axes.
    const v = b * GRID + a, s = (a - MID) / MID, t = (b - MID) / MID;
    const ct = Math.sqrt(1 - t * t / 2), cs = Math.sqrt(1 - s * s / 2);
    const w1 = W1[v] = range * s * ct, w2 = W2[v] = range * t * cs;
    const mapJac = Math.max(ct * cs - (s * t / 2) ** 2 / (ct * cs), 0);
    net(w1, w2, F, J1, J2);
    let g11 = 0, g12 = 0, g22 = 0;
    for (let i = 0; i < n; i++) {
      const s = bw[i], j1 = J1[i] * s, j2 = J2[i] * s;
      Y[v * nn + i] = F[i] * s;
      g11 += j1 * j1; g12 += j1 * j2; g22 += j2 * j2;
    }
    const det = Math.max(g11 * g22 - g12 * g12, 0), half = (g11 + g22) / 2;
    const lmax = half + Math.sqrt(Math.max(half * half - det, 0));
    if (lmax > gmax) gmax = lmax;
    // area element of the surface, with trapezoid weights on the grid
    wt[v] = Math.sqrt(det) * mapJac * (a === 0 || a === GRID - 1 ? 0.5 : 1) * (b === 0 || b === GRID - 1 ? 0.5 : 1);
    W += wt[v];
  }
  if (!(W > 0) || !isFinite(W)) { wt.fill(1); W = NV; }

  // Coefficients of f that do not depend on the weights at all (like the
  // coefficient of x when σ(0) = σ'(0) = 0) are set to exactly 0 after
  // centering, so that rounding does not make them look variable.
  const varies = new Uint8Array(nn);
  for (let i = 0; i < n; i++) for (let v = 1; v < NV; v++) if (Y[v * nn + i] !== Y[i]) { varies[i] = 1; break; }

  // center and scale
  const mu = new Float64Array(nn);
  for (let v = 0; v < NV; v++) { const w = wt[v] / W; for (let i = 0; i < n; i++) mu[i] += w * Y[v * nn + i]; }
  let scale = 0;
  for (let v = 0; v < NV; v++) for (let i = 0; i < n; i++) {
    const y = Y[v * nn + i] = varies[i] ? Y[v * nn + i] - mu[i] : 0;
    if (Math.abs(y) > scale) scale = Math.abs(y);
  }
  if (!isFinite(scale)) {
    geo = null;
    setStatus('The coefficients of f are too large to compute with. Choose smaller coefficients or a smaller range of weights.');
    afterGeometry();
    return;
  }
  if (!varies.includes(1) || scale < 1e-12 * (Math.abs(mu.reduce((x, y) => Math.max(x, Math.abs(y)), 0)) || 1)) {
    geo = null;
    setStatus('f does not depend on the weights for this σ: the neuromanifold is a single point.');
    afterGeometry();
    return;
  }
  for (let i = 0; i < NV * nn; i++) Y[i] /= scale;

  // covariance, weighted by the area element
  const C = new Float64Array(nn * nn);
  for (let v = 0; v < NV; v++) {
    const w = wt[v] / W, o = v * nn;
    for (let i = 0; i < n; i++) {
      const yi = Y[o + i] * w;
      if (yi === 0) continue;
      for (let j = 0; j <= i; j++) C[i * nn + j] += yi * Y[o + j];
    }
  }
  for (let i = 0; i < nn; i++) for (let j = 0; j < i; j++) C[j * nn + i] = C[i * nn + j];
  let trC = 0;
  for (let i = 0; i < nn; i++) trC += C[i * nn + i];

  const { values: lambda, vectors: E } = eigenSym(C, nn);
  // Fix the signs of the components: continuous while σ is edited, or else
  // with the largest entry positive.
  for (let r = 0; r < nn; r++) {
    let dot = 0, big = 0;
    if (geo && geo.nn === nn) for (let k = 0; k < nn; k++) dot += E[r * nn + k] * geo.E[r * nn + k];
    if (dot === 0) for (let k = 0; k < nn; k++) if (Math.abs(E[r * nn + k]) > Math.abs(big)) big = E[r * nn + k];
    if (dot < 0 || big < 0) for (let k = 0; k < nn; k++) E[r * nn + k] = -E[r * nn + k];
  }
  const span = affineSpan(coef, d, skip);

  // The view turns about the center of an approximate smallest ball around
  // the surface (Bădoiu–Clarkson iterations, on every 3rd sample).
  const center = new Float64Array(nn);
  for (let it = 1; it <= 60; it++) {
    let far = 0, best = -1;
    for (let v = 0; v < NV; v += 3) {
      let q = 0;
      for (let i = 0; i < n; i++) { const e = Y[v * nn + i] - center[i]; q += e * e; }
      if (q > best) { best = q; far = v; }
    }
    for (let i = 0; i < n; i++) center[i] += (Y[far * nn + i] - center[i]) / (it + 1);
  }

  // The coordinates of f for any weights, computed exactly as for the samples
  // (so that at a sample they agree with Y).
  const Fe = new Float64Array(n), Je1 = new Float64Array(n), Je2 = new Float64Array(n);
  const embed = (w1, w2, out) => {
    net(w1, w2, Fe, Je1, Je2);
    for (let i = 0; i < nn; i++) out[i] = i < n && varies[i] ? (Fe[i] * bw[i] - mu[i]) / scale : 0;
  };

  // Weights that give the same function (see weightColor): when σ is even,
  // (±w1, ±w2); without the skip connections, when σ is odd, (−w1, −w2), as
  // then σ(−w2 σ(−w1 x)) = σ(w2 σ(w1 x)).
  let even = true, odd = true, monomial = true;
  for (let k = 0; k <= d; k++) if (coef[k] !== 0) {
    if (k % 2) even = false; else odd = false;
    if (k < d) monomial = false;
  }
  const sym = even ? 'mirror' : odd && !skip ? 'antipodal' : 'none';

  geo = { d, D, n, nn, Y, C, trC, lambda, E, W1, W2, center, span, embed, net, bw, mu, scale, gmax, sym };

  // The status only speaks up when the leading coefficient of σ has been set
  // to 0. (Without the skip connections and with σ(t) = c·t^d a monomial, f(x)
  // = c^(d+1) (w2 w1^d)^d x^(d²): the neuromanifold is a segment, not a surface.)
  const segment = !skip && monomial && d > 1;
  let msg = '';
  if (d === 1) msg = 'The leading coefficient is 0, so σ is linear, and so is f: the neuromanifold lies in the 2-dimensional space of linear polynomials.';
  else if (d < deg) msg = `The leading coefficient is 0, so deg σ = ${d} and f is a polynomial of degree ${D}. The neuromanifold ${segment ? 'lies' : 'is a surface'} in the ${n}-dimensional space of such polynomials.`;
  if (msg && span < n) msg += ` It spans an affine subspace of dimension ${span}` + (span <= 3 ? ', so the principal components show it exactly.' : '.');
  setStatus(msg);
  afterGeometry();
}

function setStatus(text) { $('nm-status').textContent = text; }

function pct(x) {
  if (x >= 0.9995) return '100%';
  if (x < 0.0005) return x > 0 ? '<0.1%' : '0%';
  return (100 * x).toFixed(1) + '%';
}

// ---------------------------------------------------------------- the view
const VERT = `#version 300 es
in vec3 aPos;
in vec3 aNor;
in vec3 aCol;
uniform mat4 uProj;
uniform float uScale;
out vec3 vPos;
out vec3 vNor;
out vec3 vCol;
void main() {
  vec3 p = aPos * uScale - vec3(0.0, 0.0, ${CAM_DIST.toFixed(1)});
  vPos = p;
  vNor = aNor;
  vCol = aCol;
  gl_Position = uProj * vec4(p, 1.0);
}`;
const FRAG = `#version 300 es
precision highp float;
in vec3 vPos;
in vec3 vNor;
in vec3 vCol;
uniform int uLine;
uniform vec4 uLineColor;
uniform float uAlpha;
out vec4 outColor;
void main() {
  if (uLine == 1) { outColor = uLineColor; return; }
  // Vertex normals average poorly across folds of the parametrization; there,
  // use the normal of the triangle instead.
  vec3 N = length(vNor) > 0.5 ? vNor : cross(dFdx(vPos), dFdy(vPos));
  N = normalize(N);
  vec3 V = normalize(-vPos);
  if (dot(N, V) < 0.0) N = -N;                    // both sides of the surface are lit alike
  vec3 L = normalize(vec3(-0.45, 0.65, 0.75));  // key light
  vec3 K = normalize(vec3(0.6, -0.35, 0.5));     // fill light
  // Soft light, between 0.72 and 1.04 times the color, so that the surface
  // keeps the colors of the disk.
  float diff = 0.22 * max(dot(N, L), 0.0) + 0.1 * max(dot(N, K), 0.0);
  float spec = pow(max(dot(N, normalize(L + V)), 0.0), 40.0);
  vec3 c = vCol * (0.72 + diff) + 0.06 * spec;
  outColor = vec4(c, uAlpha);
}`;

// The mark of the probed weights: a round target of fixed size on screen,
// centered on a point given in view space.
const MARK_VERT = `#version 300 es
in vec2 aCorner;
uniform mat4 uProj;
uniform vec3 uCenter;
uniform vec2 uRadius;   // in normalized device coordinates
out vec2 vCorner;
void main() {
  vec4 p = uProj * vec4(uCenter, 1.0);
  vCorner = aCorner;
  gl_Position = vec4(p.xy + aCorner * uRadius * p.w, 0.0, p.w);
}`;
const MARK_FRAG = `#version 300 es
precision highp float;
in vec2 vCorner;
uniform float uAlpha;
uniform int uStyle;     // see STYLE
out vec4 outColor;
float step2(float e, float r, float w) { return smoothstep(e - w, e + w, r); }
void main() {
  // the radius: euclidean for the round marks, l1 for the diamond
  float r = uStyle == 2 ? abs(vCorner.x) + abs(vCorner.y) : length(vCorner), w = fwidth(r);
  if (r > 1.0) discard;
  vec3 c;
  if (uStyle == 0) c = mix(${INK_GL}, vec3(1.0), step2(${MARK_CORE}, r, w) * (1.0 - step2(${MARK_RIM}, r, w)));
  else if (uStyle == 1) c = mix(${ACCENT_GL}, vec3(1.0), step2(0.66, r, w));
  else c = mix(${ACCENT_GL}, vec3(1.0), step2(0.62, r, w));
  outColor = vec4(c, uAlpha * (1.0 - step2(1.0 - w, r, w)));
}`;

// The path of a run: each segment, from A to B, is a quad of fixed width on
// screen. Its depth is pulled towards the eye by uBias, so that the path is
// not hidden by the surface it lies on.
const LINE_VERT = `#version 300 es
in vec3 aA;
in vec3 aB;
in vec2 aCorner;        // (0 at A or 1 at B, side −1 or 1)
uniform mat4 uProj;
uniform vec2 uViewport; // in pixels
uniform float uHalf;    // half the width, in pixels
uniform float uBias;
void main() {
  vec4 a = uProj * vec4(aA, 1.0), b = uProj * vec4(aB, 1.0);
  vec2 d = (b.xy / b.w - a.xy / a.w) * uViewport;
  float len = length(d);
  vec2 nrm = len > 1e-4 ? vec2(-d.y, d.x) / len : vec2(0.0, 1.0);
  vec3 P = aCorner.x < 0.5 ? aA : aB;
  vec4 q = uProj * vec4(P, 1.0), z = uProj * vec4(P + vec3(0.0, 0.0, uBias), 1.0);
  gl_Position = vec4(q.xy + nrm * aCorner.y * uHalf * 2.0 / uViewport * q.w, z.z / z.w * q.w, q.w);
}`;
const LINE_FRAG = `#version 300 es
precision highp float;
uniform vec4 uColor;
out vec4 outColor;
void main() { outColor = uColor; }`;
// static indices of the quads of the path: two triangles for each segment
const PATH_IDX = new Uint16Array(6 * MAX_PATH);
for (let j = 0; j < MAX_PATH; j++) PATH_IDX.set([4 * j, 4 * j + 1, 4 * j + 2, 4 * j + 1, 4 * j + 3, 4 * j + 2], 6 * j);

// Whether the segment from the eye e to the point m meets a triangle of the
// mesh (with vertex positions pos) before it comes within tol of m: then the
// surface hides m. The cells of the grid in skip (if any) are left out: for
// a point of the surface, those around its own weights, where the mesh only
// approximates the surface. Möller–Trumbore, triangle by triangle.
function occluded(pos, ex, ey, ez, mx, my, mz, tol, skip) {
  const dx = mx - ex, dy = my - ey, dz = mz - ez;
  const tmax = 1 - tol / Math.hypot(dx, dy, dz);
  for (let k = 0; k < TRI.length; k += 3) {
    if (skip && skip.has((k / 6) | 0)) continue;  // the cell of the triangle
    const i0 = 3 * TRI[k], i1 = 3 * TRI[k + 1], i2 = 3 * TRI[k + 2];
    const ax = pos[i0], ay = pos[i0 + 1], az = pos[i0 + 2];
    const e1x = pos[i1] - ax, e1y = pos[i1 + 1] - ay, e1z = pos[i1 + 2] - az;
    const e2x = pos[i2] - ax, e2y = pos[i2 + 1] - ay, e2z = pos[i2 + 2] - az;
    const hx = dy * e2z - dz * e2y, hy = dz * e2x - dx * e2z, hz = dx * e2y - dy * e2x;
    const det = e1x * hx + e1y * hy + e1z * hz;
    if (det === 0) continue;
    const f = 1 / det, sx = ex - ax, sy = ey - ay, sz = ez - az;
    const u = f * (sx * hx + sy * hy + sz * hz);
    if (u < 0 || u > 1) continue;
    const qx = sy * e1z - sz * e1y, qy = sz * e1x - sx * e1z, qz = sx * e1y - sy * e1x;
    const v = f * (dx * qx + dy * qy + dz * qz);
    if (v < 0 || u + v > 1) continue;
    const t = f * (e2x * qx + e2y * qy + e2z * qz);
    if (t > 0 && t < tmax) return true;
  }
  return false;
}

function perspective(aspect) {
  const f = 1 / Math.tan(FOV / 2), near = 0.5, far = 20;
  return new Float32Array([f / aspect, 0, 0, 0, 0, f, 0, 0, 0, 0, (far + near) / (near - far), -1,
                           0, 0, 2 * far * near / (near - far), 0]);
}

// Static index buffers: the triangles of the grid, the iso-weight lines, and
// the two weight axes w1 = 0 and w2 = 0.
const TRI = new Uint16Array((GRID - 1) * (GRID - 1) * 6);
(() => {
  let k = 0;
  for (let b = 0; b < GRID - 1; b++) for (let a = 0; a < GRID - 1; a++) {
    const v = b * GRID + a;
    TRI.set([v, v + 1, v + GRID, v + 1, v + GRID + 1, v + GRID], k);
    k += 6;
  }
})();
function lineIndices(pred) {
  const out = [];
  for (let l = 0; l < GRID; l += LINE_EVERY) {
    if (!pred(l)) continue;
    for (let k = 0; k < GRID - 1; k++) {
      out.push(l * GRID + k, l * GRID + k + 1);  // w2 fixed
      out.push(k * GRID + l, (k + 1) * GRID + l);  // w1 fixed
    }
  }
  return new Uint16Array(out);
}
const LINES = lineIndices(l => l !== MID), AXES = lineIndices(l => l === MID);

// The 3D view of the surface. Its picture is the projection onto the first
// four rows of cam · basis, where basis is an orthogonal nn x nn matrix (a
// random one, or the principal components: mode is 'random' or 'pca') and
// cam an orthogonal 4 x 4 matrix (the orbit, and the 4D rotation): rows 0,
// 1, 2 are screen right, up, and towards the viewer; row 3 is a hidden
// direction, through which the 4D rotation turns the picture.
const view = { canvas: null, gl: null, ok: false, mode: 'random', basis: null, nn: 0, cam: null,
               r: 0, snap: true, dirty: true, markDirty: false, steps: 0 };

function initView(canvas) {
  const gl = canvas.getContext('webgl2', { antialias: true, alpha: false, preserveDrawingBuffer: true });
  view.canvas = canvas;
  view.gl = gl;
  view.ok = !!gl;
  if (!gl) return;

  function shader(type, src) {
    const s = gl.createShader(type);
    gl.shaderSource(s, src);
    gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(s));
    return s;
  }
  function program(vs, fs) {
    const p = gl.createProgram();
    gl.attachShader(p, shader(gl.VERTEX_SHADER, vs));
    gl.attachShader(p, shader(gl.FRAGMENT_SHADER, fs));
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
    return p;
  }
  let prog, mprog, lprog;
  try {
    prog = program(VERT, FRAG);
    mprog = program(MARK_VERT, MARK_FRAG);
    lprog = program(LINE_VERT, LINE_FRAG);
  } catch (e) {
    view.ok = false;
    return;
  }
  const U = name => gl.getUniformLocation(prog, name);
  const uProj = U('uProj'), uScale = U('uScale'), uLine = U('uLine'), uLineColor = U('uLineColor'), uAlpha = U('uAlpha');
  const MU = name => gl.getUniformLocation(mprog, name);
  const muProj = MU('uProj'), muCenter = MU('uCenter'), muRadius = MU('uRadius'), muAlpha = MU('uAlpha'), muStyle = MU('uStyle');
  const LU = name => gl.getUniformLocation(lprog, name);
  const luProj = LU('uProj'), luViewport = LU('uViewport'), luHalf = LU('uHalf'), luBias = LU('uBias'), luColor = LU('uColor');

  const pos = new Float32Array(NV * 3), nor = new Float32Array(NV * 3), col = new Uint8Array(NV * 3);
  const vao = gl.createVertexArray();
  gl.bindVertexArray(vao);
  function attrib(name, data, size, type, normalized) {
    const buf = gl.createBuffer(), loc = gl.getAttribLocation(prog, name);
    gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    gl.bufferData(gl.ARRAY_BUFFER, data.byteLength, gl.DYNAMIC_DRAW);
    gl.enableVertexAttribArray(loc);
    gl.vertexAttribPointer(loc, size, type, normalized, 0, 0);
    return buf;
  }
  const bPos = attrib('aPos', pos, 3, gl.FLOAT, false);
  const bNor = attrib('aNor', nor, 3, gl.FLOAT, false);
  const bCol = attrib('aCol', col, 3, gl.UNSIGNED_BYTE, true);
  function indexBuffer(data) {
    const buf = gl.createBuffer();
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, buf);
    gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, data, gl.STATIC_DRAW);
    return { buf, count: data.length };
  }
  const iTri = indexBuffer(TRI), iLines = indexBuffer(LINES), iAxes = indexBuffer(AXES);
  gl.bindVertexArray(null);

  // the corners of the mark's square, drawn as a triangle strip
  const mvao = gl.createVertexArray();
  gl.bindVertexArray(mvao);
  gl.bindBuffer(gl.ARRAY_BUFFER, gl.createBuffer());
  gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]), gl.STATIC_DRAW);
  const locCorner = gl.getAttribLocation(mprog, 'aCorner');
  gl.enableVertexAttribArray(locCorner);
  gl.vertexAttribPointer(locCorner, 2, gl.FLOAT, false, 0, 0);
  gl.bindVertexArray(null);

  // the quads of the path: 4 vertices per segment, each with A, B (in view
  // space) and its corner, interleaved
  const pathData = new Float32Array(4 * 8 * MAX_PATH);
  const lvao = gl.createVertexArray();
  gl.bindVertexArray(lvao);
  const bPath = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, bPath);
  gl.bufferData(gl.ARRAY_BUFFER, pathData.byteLength, gl.DYNAMIC_DRAW);
  [['aA', 3, 0], ['aB', 3, 3], ['aCorner', 2, 6]].forEach(([name, size, off]) => {
    const loc = gl.getAttribLocation(lprog, name);
    gl.enableVertexAttribArray(loc);
    gl.vertexAttribPointer(loc, size, gl.FLOAT, false, 32, 4 * off);
  });
  const bPathIdx = gl.createBuffer();
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, bPathIdx);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, PATH_IDX, gl.STATIC_DRAW);
  gl.bindVertexArray(null);

  // the first four rows of cam · basis
  const frame = () => {
    const nn = geo.nn, Fr = new Float64Array(4 * nn);
    for (let r = 0; r < 4; r++) for (let s = 0; s < 4; s++) {
      const c = view.cam[r * 4 + s];
      if (c === 0) continue;
      for (let k = 0; k < nn; k++) Fr[r * nn + k] += c * view.basis[s * nn + k];
    }
    return Fr;
  };
  view.frame = frame;

  // the colors of the weights, which change only with the surface
  view.colorsChanged = () => { view.colorsDirty = true; view.dirty = true; };

  view.resize = () => {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.max(1, Math.round(canvas.clientWidth * dpr)), h = Math.max(1, Math.round(canvas.clientHeight * dpr));
    view.dpr = dpr;
    if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; view.dirty = true; }
  };

  // Draws the view. With full = false, only the marks or the path have
  // changed, and the surface is drawn again from the buffers of the last full
  // render. Returns true if it needs another frame (to ease the scale towards
  // the size of the picture).
  let Fr = null, c = null, markY = null;
  view.render = full => {
    if (full) view.dirty = false;
    view.markDirty = false;
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.clearColor(BG[0], BG[1], BG[2], 1);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    if (!geo) return false;
    const nn = geo.nn;
    let more = false;
    if (full || !Fr || Fr.length !== 4 * nn) more = update(nn);
    draw();
    drawOverlays(nn);
    return more;
  };

  // A point with coordinates y (as geo.Y), in the coordinates of pos.
  function place(y, nn) {
    let x = -c[0], yy = -c[1], z = -c[2];
    for (let k = 0; k < nn; k++) {
      const t = y[k];
      x += Fr[k] * t; yy += Fr[nn + k] * t; z += Fr[2 * nn + k] * t;
    }
    return [x, yy, z];
  }

  // Projects the samples and computes normals and colors. Returns true while
  // the scale is still easing.
  function update(nn) {
    const Y = geo.Y;
    Fr = frame();
    c = [0, 0, 0];
    for (let r = 0; r < 3; r++) for (let k = 0; k < nn; k++) c[r] += Fr[r * nn + k] * geo.center[k];

    // project, about the center
    // The picture is scaled by 1 / view.r, with the eye at distance CAM_DIST.
    // A point (x, y, z) then lands within FILL of the half-width of the view
    // when max(|x|, |y|) / tan(FOV/2) ≤ FILL · (CAM_DIST · view.r − z), so
    // view.r is fitted to the largest z + K · max(|x|, |y|): the picture fills
    // the view as it turns. Against zooming far into a picture seen edge-on,
    // view.r stays at least 1 / MAX_ZOOM of its radius (which also keeps the
    // eye outside it).
    const K = 1 / (Math.tan(FOV / 2) * FILL);
    let r2 = 0, fit = 0;
    const include = (x, y, z) => {
      r2 = Math.max(r2, x * x + y * y + z * z);
      fit = Math.max(fit, z + K * Math.max(Math.abs(x), Math.abs(y)));
    };
    for (let v = 0; v < NV; v++) {
      const o = v * nn;
      let x = -c[0], y = -c[1], z = -c[2];
      for (let k = 0; k < nn; k++) {
        const t = Y[o + k];
        x += Fr[k] * t; y += Fr[nn + k] * t; z += Fr[2 * nn + k] * t;
      }
      pos[3 * v] = x; pos[3 * v + 1] = y; pos[3 * v + 2] = z;
      include(x, y, z);
    }
    if (train.target) include(...place(train.target.t, nn));   // the target, which may be off the surface, is in the picture too
    const r = Math.max(fit / CAM_DIST, Math.sqrt(r2) / MAX_ZOOM) || 1;
    let more = false;
    if (view.snap || !view.r) { view.r = r; view.snap = false; }
    else {
      view.r += 0.18 * (r - view.r);
      more = Math.abs(r - view.r) > 1e-3 * r;
    }

    // vertex normals, from the neighbors in the grid
    for (let b = 0; b < GRID; b++) for (let a = 0; a < GRID; a++) {
      const v = b * GRID + a;
      const l = 3 * (b * GRID + Math.max(a - 1, 0)), rr = 3 * (b * GRID + Math.min(a + 1, GRID - 1));
      const dn = 3 * (Math.max(b - 1, 0) * GRID + a), up = 3 * (Math.min(b + 1, GRID - 1) * GRID + a);
      const ux = pos[rr] - pos[l], uy = pos[rr + 1] - pos[l + 1], uz = pos[rr + 2] - pos[l + 2];
      const vx = pos[up] - pos[dn], vy = pos[up + 1] - pos[dn + 1], vz = pos[up + 2] - pos[dn + 2];
      let nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
      const len2 = nx * nx + ny * ny + nz * nz;
      const ref = (ux * ux + uy * uy + uz * uz) * (vx * vx + vy * vy + vz * vz);
      if (len2 > 1e-10 * ref && len2 > 0) { const s = 1 / Math.sqrt(len2); nx *= s; ny *= s; nz *= s; }
      else nx = ny = nz = 0;
      nor[3 * v] = nx; nor[3 * v + 1] = ny; nor[3 * v + 2] = nz;
    }

    const uploadColors = view.colorsDirty;
    if (uploadColors) for (let v = 0; v < NV; v++) weightColor(geo.W1[v] / range, geo.W2[v] / range, col, 3 * v, geo.sym);
    view.colorsDirty = false;

    gl.bindBuffer(gl.ARRAY_BUFFER, bPos); gl.bufferSubData(gl.ARRAY_BUFFER, 0, pos);
    gl.bindBuffer(gl.ARRAY_BUFFER, bNor); gl.bufferSubData(gl.ARRAY_BUFFER, 0, nor);
    if (uploadColors) { gl.bindBuffer(gl.ARRAY_BUFFER, bCol); gl.bufferSubData(gl.ARRAY_BUFFER, 0, col); }
    return more;
  }

  // Draws the surface and its grid lines, from the buffers.
  function draw() {
    gl.useProgram(prog);
    gl.bindVertexArray(vao);
    gl.uniformMatrix4fv(uProj, false, perspective(canvas.width / canvas.height));
    gl.uniform1f(uScale, 1 / view.r);

    // the surface
    gl.uniform1i(uLine, 0);
    if (xray) {
      gl.disable(gl.DEPTH_TEST);
      gl.enable(gl.BLEND);
      gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
      gl.uniform1f(uAlpha, 0.3);
    } else {
      gl.enable(gl.DEPTH_TEST);
      gl.depthFunc(gl.LEQUAL);
      gl.disable(gl.BLEND);
      gl.enable(gl.POLYGON_OFFSET_FILL);
      gl.polygonOffset(1, 1);
      gl.uniform1f(uAlpha, 1);
    }
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, iTri.buf);
    gl.drawElements(gl.TRIANGLES, iTri.count, gl.UNSIGNED_SHORT, 0);
    gl.disable(gl.POLYGON_OFFSET_FILL);

    // the iso-weight lines, and the weight axes in darker ink; always when the
    // neuromanifold is a segment, as they are all there is to see of it
    if (showLines || geo.span < 2) {
      gl.uniform1i(uLine, 1);
      gl.enable(gl.BLEND);
      gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
      gl.depthMask(false);
      gl.uniform4f(uLineColor, 23 / 255, 26 / 255, 33 / 255, xray ? 0.6 * LINE_A : LINE_A);
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, iLines.buf);
      gl.drawElements(gl.LINES, iLines.count, gl.UNSIGNED_SHORT, 0);
      gl.uniform4f(uLineColor, 23 / 255, 26 / 255, 33 / 255, xray ? 0.65 * AXIS_A : AXIS_A);
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, iAxes.buf);
      gl.drawElements(gl.LINES, iAxes.count, gl.UNSIGNED_SHORT, 0);
      gl.depthMask(true);
    }
    gl.bindVertexArray(null);
  }

  // Draws the path of the training, the target, the weights of the run, and
  // the probe; each is faint where the surface hides it.
  let runY = null;
  function drawOverlays(nn) {
    const T = train.target, run = train.run, proj = perspective(canvas.width / canvas.height);
    if (run) {
      if (!runY || runY.length !== nn) runY = new Float64Array(nn);
      geo.embed(run.w1, run.w2, runY);
      if (run.pathY.length) drawPath(nn, run, proj);
    }
    if (T) view.targetHidden = drawMarker(T.t, STYLE.target, nn, proj, null);
    if (run) view.runHidden = drawMarker(runY, STYLE.run, nn, proj, cellsNear(run.w1, run.w2, geo.sym));
    if (probe && showProbe) {
      if (!markY || markY.length !== nn) markY = new Float64Array(nn);
      geo.embed(probe.w1, probe.w2, markY);
      view.markHidden = drawMarker(markY, STYLE.probe, nn, proj, cellsNear(probe.w1, probe.w2, geo.sym));
    }
  }

  // Draws a mark at the point with coordinates y, and returns whether the
  // surface hides it; skip are the cells of the grid around the point itself,
  // if it is on the surface (see occluded).
  function drawMarker(y, style, nn, proj, skip) {
    const [x, yy, z] = place(y, nn), r = view.r;
    // The eye, at the origin of view space, is at (0, 0, CAM_DIST · r) in the
    // coordinates of pos.
    const hidden = !xray && occluded(pos, 0, 0, CAM_DIST * r, x, yy, z, 0.002 * r, skip);
    gl.useProgram(mprog);
    gl.bindVertexArray(mvao);
    gl.uniformMatrix4fv(muProj, false, proj);
    gl.uniform3f(muCenter, x / r, yy / r, z / r - CAM_DIST);
    const px = MARK_SIZE[style] * (view.dpr || 1);
    gl.uniform2f(muRadius, 2 * px / canvas.width, 2 * px / canvas.height);
    gl.uniform1f(muAlpha, hidden ? HIDDEN_ALPHA : 1);
    gl.uniform1i(muStyle, style);
    gl.disable(gl.DEPTH_TEST);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
    gl.bindVertexArray(null);
    return hidden;
  }

  // Draws the path of the run, through the current weights: first faintly
  // and through the surface, then, where it is in front, with a white halo.
  function drawPath(nn, run, proj) {
    const m = run.pathY.length + 1, segs = Math.min(m - 1, MAX_PATH), r = view.r;
    const P = new Float32Array(3 * m);             // the points, in view space
    for (let i = 0; i < m; i++) {
      const [x, y, z] = place(i < m - 1 ? run.pathY[i] : runY, nn);
      P[3 * i] = x / r; P[3 * i + 1] = y / r; P[3 * i + 2] = z / r - CAM_DIST;
    }
    for (let j = 0; j < segs; j++) for (let k = 0; k < 4; k++) {
      const o = 8 * (4 * j + k);
      pathData.set(P.subarray(3 * j, 3 * j + 6), o);   // A, then B
      pathData[o + 6] = k >> 1;
      pathData[o + 7] = k & 1 ? 1 : -1;
    }
    gl.useProgram(lprog);
    gl.bindVertexArray(lvao);
    gl.bindBuffer(gl.ARRAY_BUFFER, bPath);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, pathData.subarray(0, 32 * segs));
    gl.uniformMatrix4fv(luProj, false, proj);
    gl.uniform2f(luViewport, canvas.width, canvas.height);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.depthMask(false);
    const px = view.dpr || 1, count = 6 * segs;
    gl.disable(gl.DEPTH_TEST);
    gl.uniform1f(luBias, 0);
    gl.uniform1f(luHalf, 1.1 * px);
    gl.uniform4f(luColor, 0.659, 0.125, 0.227, 0.7 * HIDDEN_ALPHA);
    gl.drawElements(gl.TRIANGLES, count, gl.UNSIGNED_SHORT, 0);
    if (!xray) {
      gl.enable(gl.DEPTH_TEST);
      gl.depthFunc(gl.LEQUAL);
    }
    gl.uniform1f(luBias, 0.03);
    gl.uniform1f(luHalf, 2.4 * px);
    gl.uniform4f(luColor, 1, 1, 1, 0.9);
    gl.drawElements(gl.TRIANGLES, count, gl.UNSIGNED_SHORT, 0);
    gl.uniform1f(luHalf, 1.2 * px);
    gl.uniform4f(luColor, 0.659, 0.125, 0.227, 1);
    gl.drawElements(gl.TRIANGLES, count, gl.UNSIGNED_SHORT, 0);
    gl.depthMask(true);
    gl.bindVertexArray(null);
  }

  view.orbit = (dx, dy) => {
    rotateRows(view.cam, 4, 0, 2, dx * ORBIT_SPEED);
    rotateRows(view.cam, 4, 1, 2, -dy * ORBIT_SPEED);
    tidyCam();
  };
  view.rotate4 = (dx, dy) => {
    rotateRows(view.cam, 4, 0, 3, dx * ORBIT_SPEED);
    rotateRows(view.cam, 4, 1, 3, -dy * ORBIT_SPEED);
    tidyCam();
  };
  function tidyCam() {
    if (++view.steps % 64 === 0) orthonormalize(view.cam, 4);
    view.dirty = true;
  }
  view.resetCam = () => {
    view.cam = identity(4);
    rotateRows(view.cam, 4, 0, 2, 0.6);
    rotateRows(view.cam, 4, 1, 2, -0.42);
    view.dirty = true;
  };
  view.resetCam();
}

// ---------------------------------------------------------------- frame loop
let raf = 0;
function requestDraw() { if (!raf) raf = requestAnimationFrame(frame); }
function frame() {
  raf = 0;
  const training = !!(train.run && train.run.status === 'running' && geo && visible);
  if (training) advanceRun();
  let more = training;
  if (view.dirty) { if (view.render(true)) { view.dirty = true; more = true; } }   // still easing its scale
  else if (view.markDirty) view.render(false);
  if (disk.dirty) drawDisk();
  if (train.plotDirty) drawLossPlot();
  updateCaption();
  if (more) requestDraw();
}

// ---------------------------------------------------------------- the caption
// The share of the variance (of the surface, with its area element) that the
// projection holds.
let capText = '';
function updateCaption() {
  let text = '';
  if (geo) {
    const nn = geo.nn, Fr = view.frame(), C = geo.C;
    let held = 0;
    for (let r = 0; r < 3; r++) for (let i = 0; i < nn; i++) {
      const fi = Fr[r * nn + i];
      if (fi === 0) continue;
      for (let j = 0; j < nn; j++) held += fi * C[i * nn + j] * Fr[r * nn + j];
    }
    held /= geo.trC || 1;
    text = `This projection holds ${pct(held)} of the variance.`;
  }
  if (text !== capText) { $('nm-cap').textContent = text; capText = text; }
}

// ---------------------------------------------------------------- after a new surface
// The principal components follow the surface; a random projection stays,
// unless the dimension changes.
function afterGeometry() {
  if (geo) {
    if (view.mode === 'pca') { view.basis = geo.E; view.nn = geo.nn; }
    else if (!view.basis || view.nn !== geo.nn) newProjection();
  }
  view.snap = true;
  view.colorsChanged();
  if (disk.sym !== (geo ? geo.sym : 'none')) disk.layerDirty = true;   // the colors of the disk change with the symmetries of the network
  disk.dirty = true;
  // The target is made again for the new surface, from the same teacher
  // weights and noise; a run starts again from the same weights.
  if (train.target) buildTarget(false);
  if (train.run) {
    if (geo) startRun(...train.run.start);
    else train.run = null;
  }
  trainChanged();
  requestDraw();
}

// ---------------------------------------------------------------- the disk of weights
// The weights w1² + w2² ≤ R², with their colors and the grid lines of the
// surfaces (the images of the lines of the grid square). Pointing at the disk
// sets the probe: its weights are marked in the view. The probe stays when
// the pointer leaves, so that the view can be turned around it; Escape
// removes it. Clicking (or Enter) starts a run of training from the probe.
const disk = { canvas: null, ctx: null, layer: null, dpr: 1, dirty: true, layerDirty: true };

function diskResize() {
  const cv = disk.canvas, dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = Math.max(1, Math.round(cv.clientWidth * dpr)), h = Math.max(1, Math.round(cv.clientHeight * dpr));
  if (cv.width !== w || cv.height !== h || disk.dpr !== dpr) { cv.width = w; cv.height = h; disk.layerDirty = true; }
  disk.dpr = dpr;
  disk.dirty = true;
}
const diskRadius = () => Math.min(disk.canvas.width, disk.canvas.height) / 2 - 2 * disk.dpr;

// The disk, its colors and its grid lines, drawn into an offscreen layer.
function drawDiskLayer() {
  disk.layerDirty = false;
  const W = disk.canvas.width, H = disk.canvas.height;
  const layer = disk.layer || (disk.layer = document.createElement('canvas'));
  layer.width = W;
  layer.height = H;
  const g = layer.getContext('2d');
  const img = g.createImageData(W, H), px = img.data, rgb = new Uint8Array(3);
  const cx = W / 2, cy = H / 2, rad = diskRadius(), sym = disk.sym = geo ? geo.sym : 'none';
  for (let j = 0; j < H; j++) for (let i = 0; i < W; i++) {
    const x = (i + 0.5 - cx) / rad, y = (cy - j - 0.5) / rad;
    const cover = Math.min(Math.max((1 - Math.hypot(x, y)) * rad + 0.5, 0), 1);   // smooth edge
    if (cover === 0) continue;
    weightColor(x, y, rgb, 0, sym);
    const o = 4 * (j * W + i);
    px[o] = rgb[0]; px[o + 1] = rgb[1]; px[o + 2] = rgb[2]; px[o + 3] = Math.round(255 * cover);
  }
  g.putImageData(img, 0, 0);
  disk.lines = showLines;
  if (!showLines) return;

  const curve = (u0, alongT) => {               // the image of s = u0 (or of t = u0)
    g.beginPath();
    for (let k = 0; k <= 64; k++) {
      const u = -1 + k / 32, [x, y] = alongT ? squareToDisk(u0, u) : squareToDisk(u, u0);
      if (k) g.lineTo(cx + x * rad, cy - y * rad); else g.moveTo(cx + x * rad, cy - y * rad);
    }
    g.stroke();
  };
  g.lineWidth = disk.dpr;
  g.strokeStyle = LINE_INK + LINE_A + ')';
  for (let l = LINE_EVERY; l < GRID - 1; l += LINE_EVERY) {
    if (l === MID) continue;
    curve((l - MID) / MID, true);
    curve((l - MID) / MID, false);
  }
  g.lineWidth = 1.25 * disk.dpr;
  g.strokeStyle = LINE_INK + AXIS_A + ')';
  curve(0, true);
  curve(0, false);
  g.beginPath();
  g.arc(cx, cy, rad, 0, 2 * Math.PI);           // the border: the images of s = ±1 and t = ±1
  g.stroke();
}

function drawDisk() {
  disk.dirty = false;
  if (!disk.ctx) return;
  if (disk.layerDirty) drawDiskLayer();
  const { canvas: cv, ctx: g } = disk, d = disk.dpr;
  g.clearRect(0, 0, cv.width, cv.height);
  g.drawImage(disk.layer, 0, 0);
  const rad = diskRadius(), X = w => cv.width / 2 + w / range * rad, Y = w => cv.height / 2 - w / range * rad;
  const dot = (x, y, layers) => {
    for (const [rr, color] of layers) {
      g.beginPath();
      g.arc(x, y, rr, 0, 2 * Math.PI);
      g.fillStyle = color;
      g.fill();
    }
  };
  const run = train.run;
  if (run) {                                    // the path: crimson, with a white halo
    const P = run.path;
    g.beginPath();
    g.moveTo(X(P[0]), Y(P[1]));
    for (let i = 2; i < P.length; i += 2) g.lineTo(X(P[i]), Y(P[i + 1]));
    g.lineTo(X(run.w1), Y(run.w2));
    g.lineJoin = g.lineCap = 'round';
    g.strokeStyle = 'rgba(255, 255, 255, 0.9)';
    g.lineWidth = 4.2 * d;
    g.stroke();
    g.strokeStyle = ACCENT;
    g.lineWidth = 2 * d;
    g.stroke();
  }
  if (run) dot(X(run.w1), Y(run.w2), [[MARK_SIZE[STYLE.run] * d, '#ffffff'], [0.66 * MARK_SIZE[STYLE.run] * d, ACCENT]]);
  if (probe && showProbe) {
    const r = MARK_R * d;
    dot(X(probe.w1), Y(probe.w2), [[r, INK], [MARK_RIM * r, '#ffffff'], [MARK_CORE * r, INK]]);
  }
}

// Sets the probe to the weights (w1, w2), pulled into the disk; null removes it.
function setProbe(w1, w2) {
  if (w1 === null) probe = null;
  else {
    const r = Math.hypot(w1, w2);
    if (r > range) { w1 *= range / r; w2 *= range / r; }
    probe = { w1, w2 };
  }
  disk.dirty = true;
  view.markDirty = true;
  requestDraw();
}

function initDisk() {
  const cv = disk.canvas = $('nm-disk');
  disk.ctx = cv.getContext('2d');
  // The probe follows a hovering mouse or pen; touch sets it by dragging. A
  // click or a tap (not a drag) starts a run of training from there.
  let drag = null, down = null;
  const fromEvent = e => {
    const rect = cv.getBoundingClientRect(), rad = diskRadius() / disk.dpr;
    setProbe(range * (e.clientX - rect.left - rect.width / 2) / rad, -range * (e.clientY - rect.top - rect.height / 2) / rad);
  };
  cv.addEventListener('pointerdown', e => {
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    drag = e.pointerId;
    down = { x: e.clientX, y: e.clientY };
    cv.setPointerCapture(e.pointerId);
    fromEvent(e);
  });
  cv.addEventListener('pointermove', e => {
    if (e.pointerId === drag || (drag === null && e.pointerType !== 'touch')) fromEvent(e);
  });
  cv.addEventListener('pointerup', e => {
    if (e.pointerId !== drag) return;
    drag = null;
    if (down && Math.hypot(e.clientX - down.x, e.clientY - down.y) < 6) {
      fromEvent(e);
      startRun(probe.w1, probe.w2);
    }
    down = null;
  });
  cv.addEventListener('pointercancel', e => { if (e.pointerId === drag) drag = down = null; });
  cv.addEventListener('keydown', e => {
    if (e.key === 'Escape' && probe) { e.preventDefault(); setProbe(null); return; }
    if (e.key === 'Enter' || e.key === ' ') {
      e.preventDefault();
      if (!probe) setProbe(0, 0);
      startRun(probe.w1, probe.w2);
      return;
    }
    const k = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, 1], ArrowDown: [0, -1] }[e.key];
    if (!k) return;
    e.preventDefault();
    const p = probe || { w1: 0, w2: 0 }, step = 0.04 * range;
    setProbe(p.w1 + k[0] * step, p.w2 + k[1] * step);
  });
  new ResizeObserver(() => { diskResize(); requestDraw(); }).observe(cv);
  diskResize();
}

// Shows a random projection: a random orthogonal basis. Within the 3-space
// it spans, the axes are turned to the principal axes of the picture, so
// that the camera looks along its thinnest direction: this changes the
// viewpoint, not the projection.
function newProjection() {
  const nn = geo.nn, Q = randomOrthogonal(nn), C = geo.C;
  const S = new Float64Array(9);
  for (let r = 0; r < 3; r++) for (let s = 0; s < 3; s++) {
    let x = 0;
    for (let i = 0; i < nn; i++) {
      const qi = Q[r * nn + i];
      if (qi === 0) continue;
      for (let j = 0; j < nn; j++) x += qi * C[i * nn + j] * Q[s * nn + j];
    }
    S[r * 3 + s] = x;
  }
  const U = eigenSym(S, 3).vectors, top = Q.slice(0, 3 * nn);
  for (let r = 0; r < 3; r++) for (let k = 0; k < nn; k++)
    Q[r * nn + k] = U[r * 3] * top[k] + U[r * 3 + 1] * top[nn + k] + U[r * 3 + 2] * top[2 * nn + k];
  setBasis('random', Q);
}

// Shows the top three principal components (the camera looks along the
// third one, before the orbit of resetCam).
function showPca() {
  setBasis('pca', geo.E);
}

function setBasis(mode, basis) {
  view.mode = mode;
  view.basis = basis;
  view.nn = geo.nn;
  view.resetCam();
  view.snap = true;
}

// ---------------------------------------------------------------- training
// Gradient descent on the weights, for the loss L(w) = ||f_w − g||²_BW: the
// squared Bombieri–Weyl distance from f to a target g, computed exactly (no
// samples). The target is a teacher network plus noise, g = f_w* + ν ρ u,
// where w* is random in the disk of radius 0.8 R, u is a random unit vector
// in BW coordinates (a normalized Kostlan polynomial), ρ is the RMS size of
// the surface and ν the noise level: with ν = 0, the target is on the surface.
// With regularization on, the loss is L(w) = ||f_w − g||²_BW + λ ||w||², the
// squared L² norm of the weights (weight decay).
// The learning rate is constant: 1/(2 (gmax + λ)), half the largest stable
// rate for the Gauss–Newton part 2 (JᵀJ + λ) of the curvature over the disk.
// Should the loss ever go up, the step is undone and the rate halved.
const train = { nu: 0.3, reg: false, target: null, run: null, plotDirty: true };

// λ, or 0 when the regularization is off. It is REG ρ²/R², with ρ the RMS
// size of the surface (as for the noise) and R the radius of the disk: the
// loss scales as ρ² and ||w||² as R², and their sizes change by orders of
// magnitude with deg σ, so that a fixed λ would do nothing for some σ and
// everything for others.
function regLambda() {
  return train.reg && geo ? REG * geo.scale * geo.scale * geo.trC / (range * range) : 0;
}

// Makes the target for the current surface: a new one if fresh, or else from
// the same teacher weights and noise direction.
function buildTarget(fresh) {
  if (!geo) { train.target = null; return; }
  const { n, nn } = geo;
  let T = train.target;
  if (fresh || !T || T.u.length !== n) {
    const r = 0.8 * range * Math.sqrt(Math.random()), th = 2 * Math.PI * Math.random();
    const u = new Float64Array(n);
    for (let i = 0; i < n; i++) u[i] = gauss();
    const s = Math.hypot(...u);
    for (let i = 0; i < n; i++) u[i] /= s;
    T = { ws: [r * Math.cos(th), r * Math.sin(th)], u };
  } else {
    const r = Math.hypot(...T.ws);              // keep the teacher in the disk
    if (r > range) T.ws = T.ws.map(w => w * range / r);
  }
  const F = new Float64Array(n), J1 = new Float64Array(n), J2 = new Float64Array(n);
  geo.net(T.ws[0], T.ws[1], F, J1, J2);
  const rho = geo.scale * Math.sqrt(geo.trC);
  T.g = new Float64Array(n);                    // the target, in BW coordinates
  T.t = new Float64Array(nn);                   // and in those of geo.Y
  for (let i = 0; i < n; i++) {
    T.g[i] = F[i] * geo.bw[i] + train.nu * rho * T.u[i];
    T.t[i] = (T.g[i] - geo.mu[i]) / geo.scale;
  }
  // the lowest loss over the grid
  const Y = geo.Y, s2 = geo.scale * geo.scale, lam = regLambda();
  let lo = Infinity, best = 0;
  for (let v = 0; v < NV; v++) {
    let q = 0;
    for (let i = 0; i < nn; i++) { const e = Y[v * nn + i] - T.t[i]; q += e * e; }
    q = q * s2 + lam * (geo.W1[v] * geo.W1[v] + geo.W2[v] * geo.W2[v]);
    if (q < lo) { lo = q; best = v; }
  }
  T.lossMin = Math.min(lo, polishMin(T, geo.W1[best], geo.W2[best]));
  train.target = T;
}

// The lowest loss on the disk, more precisely than on the grid:
// Levenberg–Marquardt steps from the best sample, staying in the disk.
function polishMin(T, w1, w2) {
  const n = geo.n, bw = geo.bw, F = new Float64Array(n), J1 = new Float64Array(n), J2 = new Float64Array(n);
  const lam = regLambda();
  const loss = (x, y) => {
    geo.net(x, y, F, J1, J2);
    let s = 0;
    for (let i = 0; i < n; i++) { const r = F[i] * bw[i] - T.g[i]; s += r * r; }
    return s + lam * (x * x + y * y);
  };
  let L = loss(w1, w2), lambda = -1;
  for (let it = 0; it < 200 && L > 0; it++) {
    geo.net(w1, w2, F, J1, J2);
    // Gauss–Newton for the residuals f − g and √λ w
    let a = lam, b = 0, c = lam, g1 = lam * w1, g2 = lam * w2;
    for (let i = 0; i < n; i++) {
      const s = bw[i], j1 = J1[i] * s, j2 = J2[i] * s, r = F[i] * s - T.g[i];
      a += j1 * j1; b += j1 * j2; c += j2 * j2; g1 += j1 * r; g2 += j2 * r;
    }
    if (lambda < 0) lambda = 1e-3 * (a + c) / 2 + 1e-300;
    let moved = -1;
    for (let k = 0; k < 30; k++, lambda *= 10) {   // damp more until the loss goes down
      const A = a + lambda, C = c + lambda, det = A * C - b * b;
      const d1 = -(C * g1 - b * g2) / det, d2 = -(A * g2 - b * g1) / det, x = w1 + d1, y = w2 + d2;
      if (!(det > 0) || Math.hypot(x, y) > range) continue;
      const Ln = loss(x, y);
      if (Ln < L) {
        moved = Math.hypot(d1, d2);
        w1 = x; w2 = y; L = Ln;
        lambda = Math.max(lambda / 10, 1e-15 * (a + c));
        break;
      }
    }
    if (moved < 1e-14 * range) break;
  }
  return L;
}

// The loss and its gradient at the weights (w1, w2), into run.L, run.g1, run.g2.
function lossGrad(run, w1, w2) {
  const { F, J1, J2 } = run, g = train.target.g, bw = geo.bw, lam = regLambda();
  geo.net(w1, w2, F, J1, J2);
  let L = 0, g1 = 0, g2 = 0;
  for (let i = 0; i < geo.n; i++) {
    const b = bw[i], r = F[i] * b - g[i];
    L += r * r;
    g1 += r * J1[i] * b;
    g2 += r * J2[i] * b;
  }
  run.L = L + lam * (w1 * w1 + w2 * w2);
  run.g1 = 2 * (g1 + lam * w1);
  run.g2 = 2 * (g2 + lam * w2);
}

// Starts a run of gradient descent from the weights (w1, w2), pulled into the disk.
function startRun(w1, w2) {
  if (!geo) return;
  const r = Math.hypot(w1, w2);
  if (r > range) { w1 *= range / r; w2 *= range / r; }
  if (!train.target) buildTarget(true);
  const n = geo.n;
  const run = train.run = {
    start: [w1, w2], w1, w2, step: 0, frames: 0, status: 'running',
    lr: geo.gmax + regLambda() > 0 ? 0.5 / (geo.gmax + regLambda()) : 1,
    F: new Float64Array(n), J1: new Float64Array(n), J2: new Float64Array(n),
    path: [], pathY: [], hist: [], nextLog: 1,
  };
  lossGrad(run, w1, w2);
  addPathPoint(run, true);
  run.hist.push([0, run.L]);
  trainChanged();
}

// Adds the current weights to the path, if they moved enough since its last point.
function addPathPoint(run, force) {
  const P = run.path, k = P.length;
  if (!force && k && Math.hypot(run.w1 - P[k - 2], run.w2 - P[k - 1]) < PATH_EPS * range) return;
  if (k / 2 >= MAX_PATH) {                      // too many points: keep every other one
    run.pathY = run.pathY.filter((_, i) => i % 2 === 0);
    const Q = [];
    for (let i = 0; i < k; i += 4) Q.push(P[i], P[i + 1]);
    run.path = Q;
  }
  run.path.push(run.w1, run.w2);
  const y = new Float64Array(geo.nn);
  geo.embed(run.w1, run.w2, y);
  run.pathY.push(y);
}

// One frame of training. The number of steps per frame grows geometrically,
// so that the first steps are seen one by one, and later ones go fast.
function advanceRun() {
  const run = train.run;
  const count = Math.min(SPF_MAX, Math.ceil(1.04 ** run.frames));
  run.frames++;
  for (let k = 0; k < count && run.status === 'running'; k++) {
    const { w1, w2, L } = run;
    const n1 = w1 - run.lr * run.g1, n2 = w2 - run.lr * run.g2;
    lossGrad(run, n1, n2);
    if (!isFinite(run.L)) { lossGrad(run, w1, w2); run.status = 'diverged'; break; }
    if (run.L > L * (1 + 1e-12)) {              // the loss went up: undo the step, and halve the rate
      run.lr /= 2;
      lossGrad(run, w1, w2);
      continue;
    }
    run.w1 = n1;
    run.w2 = n2;
    run.step++;
    if (run.step >= run.nextLog) {
      run.hist.push([run.step, run.L]);
      run.nextLog = Math.max(run.step + 1, Math.ceil(run.nextLog * 1.05));
    }
    addPathPoint(run, false);
    if (Math.hypot(n1, n2) > range) run.status = 'left';
    else if (Math.hypot(n1 - w1, n2 - w2) < 1e-9 * range) run.status = 'converged';
    else if (run.step >= MAX_STEPS) run.status = 'limit';
  }
  if (run.status !== 'running') {
    addPathPoint(run, true);
    run.hist.push([run.step, run.L]);
    updateTrainButtons();
  }
  view.markDirty = true;
  disk.dirty = true;
  train.plotDirty = true;
}

// After a new target or run: redraw what shows them.
function trainChanged() {
  view.dirty = true;                            // the framing takes in the target
  disk.dirty = true;
  train.plotDirty = true;
  updateTrainButtons();
  requestDraw();
}

function updateTrainButtons() {
  $('nm-clear').disabled = !train.target;
}

// The loss against the steps, both on log scales, with the lowest loss on the
// disk as a dashed line.
function drawLossPlot() {
  train.plotDirty = false;
  const cv = $('nm-loss'), dpr = Math.min(window.devicePixelRatio || 1, 2);
  const W = Math.max(1, Math.round(cv.clientWidth * dpr)), H = Math.max(1, Math.round(cv.clientHeight * dpr));
  if (cv.width !== W || cv.height !== H) { cv.width = W; cv.height = H; }
  const g = cv.getContext('2d'), T = train.target, run = train.run;
  g.clearRect(0, 0, W, H);
  if (!run || !T) return;
  const lg = x => Math.log10(Math.max(x, 1e-300));
  const xs = run.hist.map(([s]) => Math.log10(s + 1)), ys = run.hist.map(([, L]) => lg(L));
  let yhi = Math.max(...ys, lg(T.lossMin)), ylo = Math.max(Math.min(...ys, lg(T.lossMin)), yhi - 10);
  if (yhi - ylo < 1) { ylo = (yhi + ylo) / 2 - 0.5; yhi = ylo + 1; }
  const xhi = Math.max(2, xs[xs.length - 1]), pad = 5 * dpr;
  const X = x => pad + (W - 2 * pad) * x / xhi, Y = y => H - pad - (H - 2 * pad) * (Math.max(y, ylo) - ylo) / (yhi - ylo);
  if (T.lossMin > 0) {
    g.setLineDash([4 * dpr, 3 * dpr]);
    g.strokeStyle = 'rgba(23, 26, 33, 0.45)';
    g.lineWidth = dpr;
    g.beginPath();
    g.moveTo(pad, Y(lg(T.lossMin)));
    g.lineTo(W - pad, Y(lg(T.lossMin)));
    g.stroke();
    g.setLineDash([]);
  }
  g.strokeStyle = ACCENT;
  g.lineWidth = 1.6 * dpr;
  g.lineJoin = 'round';
  g.beginPath();
  xs.forEach((x, i) => (i ? g.lineTo(X(x), Y(ys[i])) : g.moveTo(X(x), Y(ys[i]))));
  g.stroke();
}

function clearTraining() {
  train.run = null;
  train.target = null;
  trainChanged();
}

// ---------------------------------------------------------------- controls
const fmt = x => String(Math.round(x * 1000) / 1000);
const supTerm = k => k === 0 ? '' : k === 1 ? '<i>t</i>' : `<i>t</i><sup>${k}</sup>`;

let pending = 0;
function scheduleRecompute() {
  if (pending) return;
  pending = requestAnimationFrame(() => { pending = 0; recompute(); });
}

function buildSigma() {
  const box = $('nm-sigma');
  box.innerHTML = '<span class="nm-sigma-lhs">σ(<i>t</i>) =</span>';
  for (let k = deg; k >= 0; k--) {
    const term = document.createElement('span');
    term.className = 'nm-term';
    if (k < deg) term.insertAdjacentHTML('beforeend', '<span class="nm-plus">+</span>');
    const inp = document.createElement('input');
    inp.type = 'number';
    inp.step = '0.1';
    inp.inputMode = 'decimal';
    inp.className = 'nm-num';
    inp.value = fmt(coef[k]);
    inp.setAttribute('aria-label', k === 0 ? 'Constant term of σ' : `Coefficient of t to the ${k} in σ`);
    inp.addEventListener('input', () => {
      const x = parseFloat(inp.value);
      coef[k] = isFinite(x) ? Math.max(-MAX_COEF, Math.min(MAX_COEF, x)) : 0;
      scheduleRecompute();
    });
    inp.addEventListener('change', () => { inp.value = fmt(coef[k]); });
    term.append(inp);
    if (k > 0) term.insertAdjacentHTML('beforeend', `<span class="nm-mono">${supTerm(k)}</span>`);
    box.append(term);
  }
}

// A new degree starts from the monomial σ(t) = t^d.
function setDegree(d) {
  deg = d;
  coef.fill(0);
  coef[d] = 1;
  buildSigma();
  recompute();
}

function init() {
  initView($('nm-view'));
  if (!view.ok) {
    root.classList.add('nm-nogl');
    $('nm-status').textContent = 'This viewer needs WebGL 2, which this browser does not provide.';
    return;
  }

  const degIn = $('nm-degree'), degOut = $('nm-degree-out');
  degIn.addEventListener('input', () => {
    const d = parseInt(degIn.value, 10);
    degOut.textContent = d;
    if (d !== deg) setDegree(d);
  });

  const skipIn = $('nm-skip');
  skip = skipIn.checked;                        // as the browser may have restored it
  skipIn.addEventListener('change', () => { skip = skipIn.checked; recompute(); });

  $('nm-random').addEventListener('click', () => {
    coef.fill(0);
    for (let k = 0; k < deg; k++) coef[k] = Math.round(20 * Math.random() - 10) / 10;
    coef[deg] = (Math.random() < 0.5 ? -1 : 1) * Math.round(5 + 5 * Math.random()) / 10;
    buildSigma();
    recompute();
  });
  const rangeIn = $('nm-range'), rangeOut = $('nm-range-out');
  rangeIn.addEventListener('input', () => {
    range = parseFloat(rangeIn.value);
    rangeOut.textContent = range.toFixed(2);
    if (probe) setProbe(probe.w1, probe.w2);   // the same weights, pulled into the new disk
    disk.dirty = true;
    scheduleRecompute();
  });
  $('nm-lines').addEventListener('change', e => {
    showLines = e.target.checked;
    view.dirty = true;
    disk.layerDirty = disk.dirty = true;
    requestDraw();
  });
  $('nm-probe').addEventListener('change', e => {
    showProbe = e.target.checked;
    view.markDirty = true;
    disk.dirty = true;
    requestDraw();
  });
  $('nm-xray').addEventListener('change', e => { xray = e.target.checked; view.dirty = true; requestDraw(); });
  $('nm-new').addEventListener('click', () => {
    if (!geo) return;
    newProjection();
    requestDraw();
  });
  $('nm-pca').addEventListener('click', () => {
    if (!geo) return;
    showPca();
    requestDraw();
  });
  // training
  const noiseIn = $('nm-noise'), noiseOut = $('nm-noise-out');
  noiseIn.addEventListener('input', () => {
    train.nu = parseFloat(noiseIn.value);
    noiseOut.textContent = train.nu.toFixed(2);
    if (!train.target) return;
    buildTarget(false);
    if (train.run) startRun(...train.run.start);
    else trainChanged();
  });
  $('nm-target').addEventListener('click', () => {
    if (!geo) return;
    buildTarget(true);
    if (train.run) startRun(...train.run.start);
    else trainChanged();
  });
  $('nm-reg').addEventListener('change', e => {
    train.reg = e.target.checked;
    if (!train.target) return;
    buildTarget(false);                         // the same target, with the lowest loss for the new loss
    if (train.run) startRun(...train.run.start);
    else trainChanged();
  });
  $('nm-clear').addEventListener('click', clearTraining);
  new ResizeObserver(() => { train.plotDirty = true; requestDraw(); }).observe($('nm-loss'));

  // the view: drag to orbit, Shift-drag to rotate through a hidden dimension
  const c = view.canvas;
  let drag = null;
  c.addEventListener('pointerdown', e => {
    if (drag || (e.pointerType === 'mouse' && e.button !== 0)) return;
    drag = { id: e.pointerId, x: e.clientX, y: e.clientY };
    c.setPointerCapture(e.pointerId);
    c.classList.add('nm-grabbing');
  });
  c.addEventListener('pointermove', e => {
    if (!drag || e.pointerId !== drag.id) return;
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    drag.x = e.clientX; drag.y = e.clientY;
    if (e.shiftKey) view.rotate4(dx, dy);
    else view.orbit(dx, dy);
    requestDraw();
  });
  const end = e => {
    if (!drag || e.pointerId !== drag.id) return;
    drag = null;
    c.classList.remove('nm-grabbing');
  };
  c.addEventListener('pointerup', end);
  c.addEventListener('pointercancel', end);
  c.addEventListener('keydown', e => {
    const k = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[e.key];
    if (!k) return;
    e.preventDefault();
    const px = KEY_STEP / ORBIT_SPEED;
    if (e.shiftKey) view.rotate4(k[0] * px, k[1] * px);
    else view.orbit(k[0] * px, k[1] * px);
    requestDraw();
  });
  new ResizeObserver(() => { view.resize(); requestDraw(); }).observe(c);
  view.resize();

  new IntersectionObserver(es => {
    visible = es.some(e => e.isIntersecting);
    if (visible) requestDraw();
  }).observe(root);

  initDisk();
  updateTrainButtons();
  buildSigma();
  recompute();
}

if (window.NM_DEBUG) {
  window.NM_DEBUG = { makeNetwork, eigenSym, binomial, affineSpan, squareToDisk, diskToSquare, cellsNear, occluded, TRI, GRID, setProbe,
                      train, startRun, lossGrad, buildTarget, view, newProjection, showPca,
                      get geo() { return geo; }, get probe() { return probe; } };
}
init();
})();
