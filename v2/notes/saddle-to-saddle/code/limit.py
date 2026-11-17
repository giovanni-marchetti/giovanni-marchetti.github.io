"""Predicted saddle-to-saddle limit process for the deep ResNet (k >= 3)."""
import numpy as np
from scipy.integrate import solve_ivp
from resnet import ResNet, U_val, U_grad


def restricted_flow(net, th0, active_mask, T=1e6, tol=1e-10):
    """Gradient flow of F restricted to the active coordinates, until the gradient is tiny."""
    f = lambda t, th: -net.grad(th) * active_mask
    def ev(t, th):
        return np.linalg.norm(net.grad(th) * active_mask) - tol
    ev.terminal = True
    # first get out of the saddle region with an adaptive solver, then polish with Newton
    sol = solve_ivp(f, (0, T), th0, method="LSODA", rtol=1e-10, atol=1e-13, events=ev)
    th = sol.y[:, -1]
    idx = np.where(active_mask > 0)[0]
    for _ in range(20):
        g = net.grad(th)[idx]
        if np.linalg.norm(g) < 1e-13:
            break
        H = np.zeros((len(idx), len(idx)))
        h = 1e-6
        for a, p in enumerate(idx):
            e = np.zeros_like(th); e[p] = h
            H[:, a] = (net.grad(th + e)[idx] - net.grad(th - e)[idx]) / (2 * h)
        H = 0.5 * (H + H.T)
        th[idx] -= np.linalg.solve(H, g)
    return th


def restricted_hessian_eigs(net, th, active_mask, h=1e-6):
    idx = np.where(active_mask > 0)[0]
    H = np.zeros((len(idx), len(idx)))
    for a, p in enumerate(idx):
        e = np.zeros_like(th); e[p] = h
        H[:, a] = (net.grad(th + e)[idx] - net.grad(th - e)[idx]) / (2 * h)
    H = 0.5 * (H + H.T)
    return np.linalg.eigvalsh(H)


def blowup(c, P, x0, k, s_max, big=1e7):
    """Integrate Xi' = grad U(Xi) from x0 for time s_max; return (blow-up time or inf, state)."""
    f = lambda s, x: U_grad(c, P, x, k)
    ev = lambda s, x: np.linalg.norm(x) - big
    ev.terminal = True
    sol = solve_ivp(f, (0, s_max), x0, method="DOP853", rtol=1e-11, atol=1e-14, events=ev)
    if sol.status == 1:  # event: blow-up
        x = sol.y[:, -1]
        r = np.linalg.norm(x); u = x / r
        Uu = U_val(c, P, u, k)
        T = sol.t[-1] + r ** (2 - k) / ((k - 2) * k * Uu)
        return T, u
    return np.inf, sol.y[:, -1]


def flow_for(c, P, x0, k, s):
    if s <= 0:
        return x0.copy()
    f = lambda t, x: U_grad(c, P, x, k)
    sol = solve_ivp(f, (0, s), x0, method="DOP853", rtol=1e-11, atol=1e-14)
    return sol.y[:, -1]


def limit_process(net, xi, S_max, eps=1e-3, verbose=True):
    L, d, k = net.L, net.d, net.k
    th = np.zeros(L * d * d)
    Xi = xi.reshape(L, d, d).copy()
    A = set()
    s = 0.0
    stages = [dict(s=0.0, theta=th.copy(), A=set(), loss=net.loss(th))]
    while True:
        dormant = [(i, j) for i in range(L) for j in range(d) if (i, j) not in A]
        coeffs = {n: net.utility_coeffs(th, *n) for n in dormant}
        best = (np.inf, None, None)
        for n in dormant:
            c, P = coeffs[n]
            T, u = blowup(c, P, Xi[n], k, S_max - s)
            if T < best[0]:
                best = (T, n, u)
        T, n_star, u_star = best
        if not np.isfinite(T) or s + T > S_max:
            break
        # advance the other dormant neurons
        for n in dormant:
            if n != n_star:
                c, P = coeffs[n]
                Xi[n] = flow_for(c, P, Xi[n], k, T)
        s += T
        A = A | {n_star}
        mask = np.zeros((L, d, d))
        for (i, j) in A:
            mask[i, j, :] = 1.0
        mask = mask.ravel()
        th0 = th.reshape(L, d, d).copy()
        th0[n_star] = eps * u_star
        th = restricted_flow(net, th0.ravel(), mask)
        eig = restricted_hessian_eigs(net, th, mask)
        # spherical Hessian of the utility at the escape direction (check: non-degenerate local max)
        c, P = coeffs[n_star]
        Mh = k * (k - 1) * P.T @ (c[:, None] * (P @ u_star)[:, None] ** (k - 2) * P)
        Uu = U_val(c, P, u_star, k)
        Q, _ = np.linalg.qr(np.column_stack([u_star, np.eye(d)]))
        Tb = Q[:, 1:d]                      # orthonormal basis of the tangent space u*^perp
        Hs = Tb.T @ (Mh - k * Uu * np.eye(d)) @ Tb
        hs_eigs = np.linalg.eigvalsh(Hs) if d > 1 else np.array([])
        stages.append(dict(s=s, theta=th.copy(), A=set(A), loss=net.loss(th), neuron=n_star,
                           u=u_star, hess_min=eig.min(), sph_hess=hs_eigs, U=Uu))
        if verbose:
            print(f"jump at s={s:.5f}: neuron (layer {n_star[0]+1}, coord {n_star[1]+1}), "
                  f"U(u*)={Uu:.4g}, sph.Hess eigs={np.round(hs_eigs, 4)}, "
                  f"loss -> {net.loss(th):.6g}, min eig restricted Hessian={eig.min():.3g}")
    return stages
