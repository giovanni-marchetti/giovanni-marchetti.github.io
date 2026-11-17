// Home-page figure: a small neural network, an arrow, and a curved surface standing for its neuromanifold.
// This script draws everything into the empty <svg> of <figure id="nm-figure">. No libraries.
//
// Hooks for making the figure interactive:
//  * While a dictionary button with data-topic="x" is hovered or focused, the figure has data-topic="x",
//    so CSS can restyle parts of the figure while that button is hovered, for example
//      #nm-figure[data-topic="singularities"] .nm-edge { stroke: var(--orange); }
//    Objects of the scene with topic "x" (class .nm-on-x) stay hidden until then, and parts with class
//    .nm-off-x disappear meanwhile.
//  * Every part has a class. Network: .nm-node (with data-layer, data-index) and .nm-edge (with data-from,
//    data-to, written "layer-index"); the neuron PRUNED and its edges are also .nm-pruned, and the cross
//    on it is .nm-cross. Arrows: .nm-arrow, made of a .nm-shaft and one or two .nm-head; the orange ones are
//    also .nm-accent: .nm-swap between the neurons SWAP.neurons, .nm-backprop beside the network, and the
//    training path .nm-flow on the surface. The datapoints under the network are .nm-point.nm-sample, and
//    the target f* is a group .nm-target of its halo .nm-halo and its .nm-dot. 3D scene: .nm-face (cells of the grid, also
//    .nm-front or .nm-back by the side of the surface facing the viewer), .nm-mesh (grid lines),
//    .nm-contour (rim and folds), .nm-curve and .nm-point, together with the classes of the object they
//    belong to (the surface is .nm-manifold). A curve drawn on top is a group .nm-top, with the classes of
//    its object, holding its .nm-curve (after its halo .nm-glow, if it glows).
//  * The 3D scene is the list SCENE. Its pieces are drawn back to front: flat objects (planes) cut the
//    others along their planes, which makes their overlaps exact, and everything else is sorted by depth.
//    After changing SCENE or CAMERA in code below, call render() to redraw.

(() => {
  "use strict";

  const figure = document.getElementById("nm-figure");
  if (!figure) return;
  const svg = figure.querySelector("svg");
  const NS = "http://www.w3.org/2000/svg";
  const [, , W, H] = svg.getAttribute("viewBox").split(/\s+/).map(Number);

  // ---------- Settings ----------

  // Network: layer widths from input (bottom) to output (top), as in the animation at the top of the page.
  const LAYERS = [3, 2, 2];
  // Centre, node spacing, layer spacing, node radius. The centre leaves room on the left for BACKPROP and its label.
  const NET = { x: 128, y: H / 2, dx: 56, dy: 70, r: 6 };
  // "Singularities / Subnetworks": this hidden neuron ("layer-index") is removed, leaving a subnetwork. While
  // that button is hovered, the neuron and its edges grey out and an orange cross appears on the neuron.
  const PRUNED = "1-1";
  // "Fibers / Identifiability, symmetries": swapping these two neurons does not change the function. While that
  // button is hovered, an orange double-headed arrow joins them, bulging `bend` upward, with heads of length
  // `head`, `gap` away from the neurons. And the arrow to the surface becomes two arrows whose tips almost meet,
  // FIBER.reach closer to the surface than its tip: they start at heights NET.y ± FIBER.dy, bulge FIBER.bend
  // apart, and are then moved FIBER.sep up and down. The point "f" of SCENE is where they land.
  const SWAP = { neurons: ["1-0", "1-1"], bend: 92, head: 9, gap: 8 };
  const FIBER = { dy: 26, bend: 30, sep: 1.5, reach: 10 };
  // "Gradient flow / Training": the backpropagation arrow runs down the left of the network, from the output layer
  // to the input layer, at x = `x`; its label, the negative gradient, is centred `label` above its top.
  const BACKPROP = { x: 40, head: 10, label: 17 };
  // "Dimension, degree / Expressivity, sample complexity": datapoints of radius `r` lying around under the network,
  // at offsets `at` from the middle of its input layer; and the target function f*, off the surface at (x, y), a dot
  // of radius `r` on a fading halo of radius `halo`, with its label "fstar" centred at offset `label` (all in svg
  // units).
  const SAMPLE = { r: 4, at: [[-57, 34], [-26, 25], [-7, 54], [34, 40], [58, 61]] };
  const TARGET = { x: 383, y: 60, r: 4.5, halo: 22, label: [0, -34] };

  // The surface is scaled to fit this box, and the label M is centred at LABEL (both in svg units).
  const BOX = { x0: 290, y0: 0, x1: W - 6, y1: H - 24 };
  const LABEL = { x: 573, y: 126 };

  // Camera: turn the scene by `yaw` about the vertical axis, then view it from `pitch` above (radians).
  const CAMERA = { yaw: 0.6, pitch: 1.0 };

  // Stand-in for a neuromanifold: the Whitney umbrella, the image of the polynomial map below.
  // It is singular: the surface crosses itself along the half-line {x = y = 0, z >= 0}, whose points have
  // two preimages (0, ±v), and that half-line ends in a pinch point at the origin.
  function umbrella(u, v) {
    return [u, u * v, v * v];
  }

  // "Hyperplane / Datapoint": two planes H1, H2 through the line LINE.p + s LINE.d, which is their intersection.
  // LINE.p = umbrella(-0.5, -1.1) lies on the surface, so the line visibly pierces it there.
  const LINE = { p: [-0.5, 0.55, 1.21], d: [0, 0, 1] };
  const plane = a => (s, t) => [0, 1, 2].map(k => LINE.p[k] + s * LINE.d[k] + t * a[k]);
  const H1 = plane([Math.cos(0.2), Math.sin(0.2), 0]), H2 = plane([Math.cos(-1.4), Math.sin(-1.4), 0]);
  const SIDES = ["u0", "u1", "v0", "v1"];

  // "Gradient flow / Training": a training path on the surface, a cubic Bézier curve in the parameters (u, v)
  // with these control points. It stays in the front sheet (u and v about -1 to 0), which nothing hides.
  const FLOW = [[-0.85, -1.05], [-0.4, -1.0], [-0.8, -0.5], [-0.35, -0.3]];
  const bezier = (c, t) => [0, 1].map(i =>
    (1 - t) ** 3 * c[0][i] + 3 * t * (1 - t) ** 2 * c[1][i] + 3 * t * t * (1 - t) * c[2][i] + t ** 3 * c[3][i]);

  // The scene. Every object has a `name`, giving its pieces the class nm-<name>; it may have a `style`
  // (class nm-<style>), a `topic` (its pieces are hidden until the dictionary button with that
  // data-topic is hovered), and a `label` (the span .nm-label[data-label=name] is placed next to the
  // point `at` of the object, shifted by dx, dy in svg units).
  // A surface maps parameters (u, v), in the rectangle u × v, to a point [x, y, z] of space (z up).
  // `cells` sets the grid, `mesh` draws a line every so many cells in each direction, `rim` lists
  // the sides of the rectangle ("u0", "u1", "v0", "v1") that are edges of the surface, and `wrap` glues
  // the sides v0 and v1 together. A `flat` surface is a piece of a plane, along which everything else is
  // cut. A curve is a polyline through `points`; `on` lists the flat objects it lies in. With `top`, it is
  // not sorted but drawn over everything else as one path, which is only right if nothing hides it; `glow`
  // (a blurred halo) and `arrow` (a head of length `head` at its last point, and with `dash: [dash, gap]` a
  // dashed shaft) imply `top` (see drawOnTop). A point lies on
  // the surface SCENE[surface], at parameters `at`. The view is fitted to SCENE[0].
  const SCENE = [
    { kind: "surface", name: "manifold", map: umbrella, u: [-1, 1], v: [-1.2, 1.2], cells: [20, 24], mesh: [2, 2], rim: SIDES },
    { kind: "surface", name: "H1", style: "plane", flat: true, topic: "hyperplane", map: H1, u: [-1.3, 1.2], v: [-0.85, 0.85],
      cells: [15, 12], mesh: [5, 4], rim: SIDES, label: { name: "H1", at: [-1.3, -0.85], dx: -14, dy: 4 } },
    // H2's half nearer the camera (v > 0) is longer, so that it crosses the whole surface.
    { kind: "surface", name: "H2", style: "plane", flat: true, topic: "hyperplane", map: H2, u: [-1.3, 1.2], v: [-0.85, 1.7],
      cells: [15, 18], mesh: [5, 4], rim: SIDES, label: { name: "H2", at: [1.2, -0.85], dx: -14, dy: -4 } },
    { kind: "curve", name: "H12", topic: "hyperplane", on: ["H1", "H2"], points: Array.from({ length: 26 }, (_, k) => H1(-1.3 + 0.1 * k, 0)) },
    // "Singularities / Subnetworks": the singular half-line {x = y = 0}, from the pinch point up to the top of
    // the surface (z = 1.2², where v = ±1.2). From this camera no part of the surface hides it, so it can be drawn
    // on top (sorted with the surface, it would be partly covered by the cells next to it, seen almost edge-on).
    { kind: "curve", name: "singular", topic: "singularities", top: true, points: [[0, 0, 0], [0, 0, 1.44]] },
    // "Fibers / Identifiability": the function f where a network and its copy with swapped neurons both land,
    // on the front sheet just right of the tips of the two arrows.
    { kind: "point", name: "f", topic: "fibers", surface: 0, at: [-0.9, -0.9] },
    { kind: "curve", name: "flow", topic: "gradient-flow", arrow: true, head: 12, dash: [8, 5], points: Array.from({ length: 61 }, (_, k) => umbrella(...bezier(FLOW, k / 60))) },
  ];

  // Classes of the pieces of object o.
  const classesOf = o => ["nm-" + o.name, o.style && "nm-" + o.style, o.topic && "nm-extra nm-on-" + o.topic].filter(Boolean).join(" ");

  // ---------- Drawing ----------
  // The scene is built from pieces (polygons, segments, circles) in camera coordinates, grouped in items:
  // an item is drawn as a whole, for example a cell of a surface followed by the lines along its sides.

  function render() {
    svg.textContent = "";
    const defs = svg.appendChild(el("defs", {}));
    // The blur of the glowing curves. Its region is given in svg units, since a straight vertical or horizontal
    // curve has an empty bounding box, which would cut the blur off.
    if (SCENE.some(o => o.glow)) {
      const blur = defs.appendChild(el("filter", {
        id: "nm-blur", filterUnits: "userSpaceOnUse", x: -20, y: -20, width: W + 40, height: H + 40 }));
      blur.appendChild(el("feGaussianBlur", { stdDeviation: 3 }));
    }
    // The fading halo of the target f*, a radial gradient whose colours are set in CSS (.nm-halo-in, .nm-halo-out).
    const halo = defs.appendChild(el("radialGradient", { id: "nm-halo" }));
    halo.appendChild(el("stop", { offset: 0, class: "nm-halo-in" }));
    halo.appendChild(el("stop", { offset: 1, class: "nm-halo-out" }));
    const grids = new Map(SCENE.filter(o => o.kind === "surface").map(o => [o, sample(o)]));
    const main = grids.get(SCENE[0]), fit = fitTo(main.flat());
    const zs = main.flat().map(p => p[2]), lift = 0.04 * (Math.max(...zs) - Math.min(...zs));

    const items = [];
    for (const [o, P] of grids) addSurface(o, P, items);
    const onTop = o => o.kind === "curve" && (o.top || o.glow || o.arrow);
    for (const o of SCENE.filter(o => o.kind === "curve" && !onTop(o))) addCurve(o, items, lift);
    for (const o of SCENE.filter(o => o.kind === "point")) addPoint(o, items, lift);
    const planes = SCENE.filter(o => o.flat).map(o => planeOf(o, grids.get(o)));
    const scene = el("g", { class: "nm-scene" });
    for (const item of order(items, planes)) for (const piece of item.pieces) scene.appendChild(draw(piece, fit));
    for (const o of SCENE.filter(onTop)) scene.appendChild(drawOnTop(o, fit));

    const netRight = drawNetwork();
    svg.appendChild(scene);
    // A horizontal arrow that stops just before the surface (or before its left edge, if it passes below or above),
    // and the two curved arrows ending on either side of its tip that replace it while "Fibers" is hovered.
    const hit = leftEdgeAt(main, fit, NET.y), tail = netRight + 24, tip = [(Number.isFinite(hit) ? hit : fit.left) - 20, NET.y];
    svg.appendChild(drawArrow([tail, NET.y], tip, "nm-arrow nm-off-fibers"));
    for (const s of [-1, 1])
      svg.appendChild(drawArrow([tail, NET.y + s * (FIBER.dy + FIBER.sep)], [tip[0] + FIBER.reach, tip[1] + s * FIBER.sep],
        "nm-arrow nm-extra nm-on-fibers", { bend: -s * FIBER.bend }));
    // The target function f*, off the surface: a dot on a fading halo, with its label.
    const target = svg.appendChild(el("g", { class: "nm-target nm-extra nm-on-dimension" }));
    target.appendChild(el("circle", { class: "nm-halo", cx: TARGET.x, cy: TARGET.y, r: TARGET.halo }));
    target.appendChild(el("circle", { class: "nm-dot", cx: TARGET.x, cy: TARGET.y, r: TARGET.r }));
    place("fstar", TARGET.x + TARGET.label[0], TARGET.y + TARGET.label[1]);

    place("M", LABEL.x, LABEL.y);
    for (const o of SCENE.filter(o => o.label)) {
      const [x, y] = fit.screen(toCamera(o.map(...o.label.at)));
      place(o.label.name, x + (o.label.dx || 0), y + (o.label.dy || 0));
    }
  }

  // Centre the label span .nm-label[data-label=name] at (x, y), in svg units.
  function place(name, x, y) {
    const span = figure.querySelector(`.nm-label[data-label="${name}"]`);
    if (!span) return;
    span.style.left = (100 * x / W) + "%";
    span.style.top = (100 * y / H) + "%";
  }

  // Grid of the surface's points, in camera coordinates.
  function sample(o) {
    const [nu, nv] = o.cells, P = [];
    for (let i = 0; i <= nu; i++) {
      P.push([]);
      for (let j = 0; j <= nv; j++) {
        const u = o.u[0] + (o.u[1] - o.u[0]) * i / nu, v = o.v[0] + (o.v[1] - o.v[0]) * j / nv;
        P[i].push(toCamera(o.map(u, v)));
      }
    }
    return P;
  }

  // World coordinates (z up) to camera coordinates (right, up, toward the viewer).
  function toCamera([x, y, z]) {
    const cy = Math.cos(CAMERA.yaw), sy = Math.sin(CAMERA.yaw);
    const cp = Math.cos(CAMERA.pitch), sp = Math.sin(CAMERA.pitch);
    const x1 = cy * x - sy * y, y1 = sy * x + cy * y;
    return [x1, sp * y1 + cp * z, -cp * y1 + sp * z];
  }

  // Scale and centre the given camera-space points in BOX; fit.screen(p) projects a camera-space point,
  // and fit.left is the x-coordinate of the leftmost one on screen.
  function fitTo(points) {
    const xs = points.map(p => p[0]), ys = points.map(p => p[1]);
    const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
    const s = Math.min((BOX.x1 - BOX.x0) / (maxX - minX), (BOX.y1 - BOX.y0) / (maxY - minY));
    const ox = (BOX.x0 + BOX.x1) / 2 - s * (minX + maxX) / 2, oy = (BOX.y0 + BOX.y1) / 2 + s * (minY + maxY) / 2;
    return { screen: p => [ox + s * p[0], oy - s * p[1]], left: ox + s * minX };
  }

  // Smallest x at which the horizontal line at height y crosses the projected grid P (Infinity if it misses).
  function leftEdgeAt(P, fit, y) {
    let best = Infinity;
    const meet = (p, q) => {
      const [x1, y1] = fit.screen(p), [x2, y2] = fit.screen(q);
      if (y1 !== y2 && (y1 - y) * (y2 - y) <= 0) best = Math.min(best, x1 + (x2 - x1) * (y - y1) / (y2 - y1));
    };
    P.forEach((row, i) => row.forEach((p, j) => {
      if (i + 1 < P.length) meet(p, P[i + 1][j]);
      if (j + 1 < row.length) meet(p, row[j + 1]);
    }));
    return best;
  }

  // One item per cell of the grid: the cell, then the lines along its sides that it carries.
  // A cell is .nm-front or .nm-back depending on which side of the surface faces the viewer (CSS colours
  // them). Lines are contours (the rim, and folds where the surface turns away from the viewer) or mesh.
  function addSurface(o, P, items) {
    const [nu, nv] = o.cells, [mu, mv] = o.mesh || [1, 1], cls = classesOf(o), faces = [];
    for (let i = 0; i < nu; i++) {
      faces.push([]);
      for (let j = 0; j < nv; j++) {
        const a = P[i][j], b = P[i + 1][j], c = P[i + 1][j + 1], d = P[i][j + 1];
        const front = cross(sub(c, a), sub(d, b))[2] >= 0;
        const item = {
          depth: (a[2] + b[2] + c[2] + d[2]) / 4, front, owner: o, on: o.flat ? [o] : [],
          pieces: [{ type: "poly", pts: [a, b, c, d], cls: `nm-face ${front ? "nm-front" : "nm-back"} ${cls}` }],
        };
        faces[i].push(item);
        items.push(item);
      }
    }
    const line = (item, kind, p, q) => item.pieces.push({ type: "seg", pts: [p, q], cls: kind + " " + cls });
    // The side p–q between cells f and g (one of them is missing on the border of the rectangle).
    const side = (f, g, onRim, onMesh, p, q) => {
      if (!(f && g)) { if (onRim) line(f || g, "nm-contour", p, q); return; }
      const nearer = f.depth > g.depth ? f : g;
      if (f.front !== g.front) line(nearer, "nm-contour", p, q);
      else if (onMesh) line(nearer, "nm-mesh", p, q);
    };
    const rim = s => o.rim.includes(s);
    for (let i = 0; i < nu; i++) {         // sides along u, on the parameter lines v = const
      for (let j = 0; j <= nv; j++) {
        if (j === nv && o.wrap) continue;
        const f = j > 0 ? faces[i][j - 1] : (o.wrap ? faces[i][nv - 1] : null);
        const g = j < nv ? faces[i][j] : null;
        side(f, g, rim(j === 0 ? "v0" : "v1"), j % mv === 0, P[i][j], P[i + 1][j]);
      }
    }
    for (let i = 0; i <= nu; i++) {        // sides along v, on the parameter lines u = const
      for (let j = 0; j < nv; j++) {
        const f = i > 0 ? faces[i - 1][j] : null, g = i < nu ? faces[i][j] : null;
        side(f, g, rim(i === 0 ? "u0" : "u1"), i % mu === 0, P[i][j], P[i][j + 1]);
      }
    }
  }

  // Each segment of a curve is an item of its own, sorted as if lifted slightly toward the viewer so that
  // the cells of a surface it lies on do not cover it.
  function addCurve(o, items, lift) {
    const P = o.points.map(toCamera), on = SCENE.filter(s => (o.on || []).includes(s.name));
    for (let k = 0; k + 1 < P.length; k++) {
      items.push({ depth: (P[k][2] + P[k + 1][2]) / 2 + lift, owner: o, on,
        pieces: [{ type: "seg", pts: [P[k], P[k + 1]], cls: "nm-curve " + classesOf(o) }] });
    }
  }

  // A curve drawn on top is not sorted with the rest: it is drawn last, as one path. With `arrow` it is an arrow;
  // with `glow` it lies on a blurred copy of itself, like the sparks of the animation at the top of the page.
  function drawOnTop(o, fit) {
    const pts = o.points.map(p => fit.screen(toCamera(p)));
    if (o.arrow) return arrowAlong(pts, "nm-arrow nm-accent " + classesOf(o), { head: o.head || 10, dash: o.dash });
    const d = "M" + pts.map(p => p.map(r1).join(" ")).join("L");
    const g = el("g", { class: "nm-top " + classesOf(o) });
    if (o.glow) g.appendChild(el("path", { class: "nm-glow", d }));
    g.appendChild(el("path", { class: "nm-curve", d }));
    return g;
  }

  // A point is sorted as if lifted slightly toward the viewer, so the cells around it do not cover it.
  function addPoint(o, items, lift) {
    const p = toCamera(SCENE[o.surface].map(o.at[0], o.at[1]));
    items.push({ depth: p[2] + lift, owner: o, on: [], pieces: [{ type: "circle", pts: [p], r: 5.5, cls: "nm-point " + classesOf(o) }] });
  }

  // The plane of a flat surface, as n·p = c in camera coordinates, with n pointing toward the viewer.
  function planeOf(o, P) {
    const a = P[0][0], n = unit(cross(sub(P[P.length - 1][0], a), sub(P[0][P[0].length - 1], a)));
    const m = n[2] < 0 ? n.map(t => -t) : n;
    return { obj: o, n: m, c: dot(m, a) };
  }

  // Back-to-front order of the items. The first plane splits them into the items behind it, those lying
  // in it, and those in front of it (cutting the items that cross it); each part is then ordered by the
  // remaining planes, and once no plane is left, by depth. Along any line of sight, whatever is in front
  // of a plane comes before whatever is behind it, so this order is exact with respect to the planes.
  // An item lying in several planes (their common line) is drawn just after the last of them.
  function order(items, planes) {
    if (!planes.length) return items.sort((a, b) => a.depth - b.depth);
    const [pl, ...rest] = planes, back = [], on = [], front = [];
    for (const item of items) {
      if (item.on.includes(pl.obj)) (rest.some(r => item.on.includes(r.obj)) ? front : on).push(item);
      else {
        const [b, f] = cut(item, pl);
        if (b) back.push(b);
        if (f) front.push(f);
      }
    }
    on.sort((a, b) => (a.owner === pl.obj ? 0 : 1) - (b.owner === pl.obj ? 0 : 1));  // the plane, then what lies in it
    return [...order(back, rest), ...on, ...order(front, rest)];
  }

  // Cut an item along a plane into its parts behind and in front of it (null when a part is empty).
  function cut(item, { n, c }) {
    const back = [], front = [];
    for (const piece of item.pieces) {
      const s = piece.pts.map(p => dot(n, p) - c);
      if (s.every(v => v >= -1e-9)) front.push(piece);
      else if (s.every(v => v <= 1e-9)) back.push(piece);
      else {
        const [pb, pf] = split(piece.pts, s, piece.type === "poly");
        back.push({ ...piece, pts: pb });
        front.push({ ...piece, pts: pf });
      }
    }
    return [back.length ? { ...item, pieces: back } : null, front.length ? { ...item, pieces: front } : null];
  }

  // Split a polygon (closed) or a segment (open) whose vertices are at signed distances s from a plane.
  function split(pts, s, closed) {
    const back = [], front = [];
    pts.forEach((p, i) => {
      const j = (i + 1) % pts.length;
      if (s[i] <= 0) back.push(p);
      if (s[i] >= 0) front.push(p);
      if ((closed || j > 0) && s[i] * s[j] < 0) {
        const m = lerp(p, pts[j], s[i] / (s[i] - s[j]));
        back.push(m);
        front.push(m);
      }
    });
    return [back, front];
  }

  // The SVG element of a piece.
  function draw(piece, fit) {
    const pts = piece.pts.map(fit.screen);
    if (piece.type === "poly") return el("path", { class: piece.cls, d: pathOf(pts) });
    if (piece.type === "seg") return el("line", { class: piece.cls, x1: r1(pts[0][0]), y1: r1(pts[0][1]), x2: r1(pts[1][0]), y2: r1(pts[1][1]) });
    return el("circle", { class: piece.cls, cx: r1(pts[0][0]), cy: r1(pts[0][1]), r: piece.r });
  }

  // The network, inputs at the bottom. Returns the x-coordinate of its right edge.
  // The edges of the neuron PRUNED are drawn first, so that the other edges cross over them once they are grey.
  function drawNetwork() {
    const g = el("g", { class: "nm-network" });
    const pos = LAYERS.map((n, l) => Array.from({ length: n }, (_, i) =>
      [NET.x + (i - (n - 1) / 2) * NET.dx, NET.y + ((LAYERS.length - 1) / 2 - l) * NET.dy]));
    const cls = (base, ...ends) => ends.includes(PRUNED) ? base + " nm-pruned" : base;
    const edges = [];
    pos.slice(0, -1).forEach((layer, l) => layer.forEach((p, i) => pos[l + 1].forEach((q, j) => {
      const from = l + "-" + i, to = (l + 1) + "-" + j;
      edges.push(el("line", { class: cls("nm-edge", from, to), x1: p[0], y1: p[1], x2: q[0], y2: q[1], "data-from": from, "data-to": to }));
    })));
    const pruned = e => e.classList.contains("nm-pruned");
    edges.sort((a, b) => pruned(b) - pruned(a)).forEach(e => g.appendChild(e));
    pos.forEach((layer, l) => layer.forEach((p, i) =>
      g.appendChild(el("circle", { class: cls("nm-node", l + "-" + i), cx: p[0], cy: p[1], r: NET.r, "data-layer": l, "data-index": i }))));
    const at = id => { const [l, i] = id.split("-").map(Number); return pos[l] && pos[l][i]; };
    // The datapoints lying around under the input layer.
    for (const [dx, dy] of SAMPLE.at)
      g.appendChild(el("circle", { class: "nm-point nm-sample nm-extra nm-on-dimension", cx: NET.x + dx, cy: pos[0][0][1] + dy, r: SAMPLE.r }));
    // The cross on the pruned neuron, a little wider than the neuron.
    const c = at(PRUNED), a = NET.r + 3;
    if (c) g.appendChild(el("path", { class: "nm-cross nm-extra nm-on-singularities",
      d: `M${c[0] - a} ${c[1] - a}L${c[0] + a} ${c[1] + a}M${c[0] - a} ${c[1] + a}L${c[0] + a} ${c[1] - a}` }));
    // The double-headed arrow between the swapped neurons.
    const [s, t] = SWAP.neurons.map(at);
    if (s && t) g.appendChild(drawArrow(s, t, "nm-arrow nm-accent nm-swap nm-extra nm-on-fibers",
      { bend: SWAP.bend, gap: NET.r + SWAP.gap, head: SWAP.head, both: true }));
    // The backpropagation arrow, from the height of the output layer down to that of the input layer, with the
    // label "grad" (the negative gradient) on top of it.
    const x = BACKPROP.x, y0 = pos[pos.length - 1][0][1], y1 = pos[0][0][1];
    g.appendChild(drawArrow([x, y0], [x, y1], "nm-arrow nm-accent nm-backprop nm-extra nm-on-gradient-flow", { head: BACKPROP.head }));
    place("grad", x, y0 - BACKPROP.label);
    svg.appendChild(g);
    return NET.x + (Math.max(...LAYERS) - 1) / 2 * NET.dx + NET.r;
  }

  // An arrow from p to q along a quadratic curve that bulges `bend` svg units to the left of the direction p → q
  // (0 gives a straight arrow), with a head of length `head` at its end, `gap` short of q. With `both`, it also
  // has a head at its start, `gap` short of p.
  function drawArrow(p, q, cls, { bend = 0, ...opts } = {}) {
    const d = [q[0] - p[0], q[1] - p[1]], len = Math.hypot(d[0], d[1]), n = bend ? 64 : 1;
    const c = [(p[0] + q[0]) / 2 + bend * d[1] / len, (p[1] + q[1]) / 2 - bend * d[0] / len];
    return arrowAlong(Array.from({ length: n + 1 }, (_, k) => [0, 1].map(i => {
      const t = k / n;
      return (1 - t) * (1 - t) * p[i] + 2 * t * (1 - t) * c[i] + t * t * q[i];
    })), cls, opts);
  }

  // An arrow along the polyline pts (in svg units), with the same options as drawArrow, and `dash: [dash, gap]`
  // for a dashed shaft.
  function arrowAlong(pts, cls, { gap = 0, head = 10, both = false, dash = null } = {}) {
    const g = el("g", { class: cls });
    // Cut the polyline `gap` short of its last point, put a head at the new end, and stop the shaft just inside
    // the head (so that a dashed shaft shows a whole dash next to it).
    const end = pts => {
      pts = cutEnd(pts, pts[pts.length - 1], gap);
      const tip = pts[pts.length - 1], back = cutEnd(pts, tip, head).pop();
      const l = Math.hypot(tip[0] - back[0], tip[1] - back[1]), u = [(tip[0] - back[0]) / l, (tip[1] - back[1]) / l];
      const b = [tip[0] - head * u[0], tip[1] - head * u[1]], w = 0.45 * head;
      g.appendChild(el("path", { class: "nm-head", d: pathOf([tip, [b[0] - w * u[1], b[1] + w * u[0]], [b[0] + w * u[1], b[1] - w * u[0]]]) }));
      return cutEnd(pts, tip, head - 1);
    };
    pts = end(pts);
    if (both) pts = end(pts.reverse()).reverse();
    const shaft = el("path", { class: "nm-shaft", d: "M" + pts.map(p => r1(p[0]) + " " + r1(p[1])).join("L") });
    if (dash) {
      // Stretch the gaps a little, so that the shaft starts and ends with a whole dash.
      const L = pts.slice(1).reduce((s, p, k) => s + Math.hypot(p[0] - pts[k][0], p[1] - pts[k][1]), 0);
      const n = Math.max(1, Math.round((L + dash[1]) / (dash[0] + dash[1])));
      if (n > 1) shaft.setAttribute("stroke-dasharray", dash[0] + " " + ((L - n * dash[0]) / (n - 1)).toFixed(3));
    }
    g.prepend(shaft);
    return g;
  }

  // The polyline pts (in the plane), ending where it last leaves the circle of radius r around o.
  function cutEnd(pts, o, r) {
    const dist = p => Math.hypot(p[0] - o[0], p[1] - o[1]);
    for (let k = pts.length - 1; k > 0; k--) {
      const d1 = dist(pts[k - 1]);
      if (d1 >= r) {
        const t = (d1 - r) / (d1 - dist(pts[k]) || 1), p = pts[k - 1], q = pts[k];
        return [...pts.slice(0, k), [p[0] + (q[0] - p[0]) * t, p[1] + (q[1] - p[1]) * t]];
      }
    }
    return pts.slice(0, 1);
  }

  // ---------- Small helpers ----------

  function el(tag, attrs) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    return e;
  }
  function sub(a, b) { return [a[0] - b[0], a[1] - b[1], a[2] - b[2]]; }
  function dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
  function cross(a, b) { return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]; }
  function unit(a) { const n = Math.hypot(a[0], a[1], a[2]) || 1; return [a[0] / n, a[1] / n, a[2] / n]; }
  function lerp(p, q, t) { return [p[0] + (q[0] - p[0]) * t, p[1] + (q[1] - p[1]) * t, p[2] + (q[2] - p[2]) * t]; }
  function r1(x) { return Math.round(x * 10) / 10; }
  function pathOf(pts) { return "M" + pts.map(p => r1(p[0]) + " " + r1(p[1])).join("L") + "Z"; }

  // ---------- Start ----------

  render();

  // Dictionary buttons: hovering or focusing one tells the figure which topic is active.
  document.querySelectorAll(".dict-entry[data-topic]").forEach(button => {
    const enter = () => { figure.dataset.topic = button.dataset.topic; };
    const leave = () => { delete figure.dataset.topic; };
    button.addEventListener("mouseenter", enter);
    button.addEventListener("mouseleave", leave);
    button.addEventListener("focus", enter);
    button.addEventListener("blur", leave);
  });
})();
