"""Deep polynomial ResNet  h_i = h_{i-1} + sigma(W_i h_{i-1}),  sigma(z) = z^k  (no biases).

Gradient flow from theta(0) = alpha * xi, and the predicted vanishing-initialization limit
(saddle-to-saddle process): dormant neurons follow  Xi' = grad U_n(Xi)  in rescaled time
s = alpha^(k-2) t, a neuron activates when Xi blows up, and the active subnetwork jumps to a
local minimum of the restricted loss along the escape orbit.
"""
import numpy as np
from scipy.integrate import solve_ivp


class ResNet:
    def __init__(self, X, Y, L, k):
        self.X, self.Y, self.L, self.k = X, Y, L, k
        self.n, self.d = X.shape

    def unpack(self, th):
        return th.reshape(self.L, self.d, self.d)

    def forward(self, th):
        W = self.unpack(th)
        hs, zs = [self.X], []
        h = self.X
        for i in range(self.L):
            z = h @ W[i].T
            zs.append(z)
            h = h + z ** self.k
            hs.append(h)
        return hs, zs

    def loss(self, th):
        hs, _ = self.forward(th)
        r = hs[-1] - self.Y
        return 0.5 * np.sum(r * r) / self.n

    def grad(self, th):
        W = self.unpack(th)
        hs, zs = self.forward(th)
        g = (hs[-1] - self.Y) / self.n          # dF/dh_L
        G = np.zeros_like(W)
        gs = [None] * (self.L + 1)
        gs[self.L] = g
        for i in reversed(range(self.L)):
            delta = g * (self.k * zs[i] ** (self.k - 1))
            G[i] = delta.T @ hs[i]
            g = g + delta @ W[i]
            gs[i] = g
        return G.ravel()

    def backprop_signals(self, th):
        """h_{i-1} and g_i = dF/dh_i (times n) for every layer i = 1..L (0-based lists)."""
        W = self.unpack(th)
        hs, zs = self.forward(th)
        g = (hs[-1] - self.Y)
        gs = [None] * self.L
        for i in reversed(range(self.L)):
            gs[i] = g.copy()                    # dF/dh_{i+1} in 1-based notation
            delta = g * (self.k * zs[i] ** (self.k - 1))
            g = g + delta @ W[i]
        return hs[:-1], gs                      # hs[i] = h_{i} (input of layer i+1)

    def utility_coeffs(self, th, i, j):
        """U_{(i,j)}(w) = -(1/n) sum_a g_i[a,j] <w, h_{i-1}(x_a)>^k   (sigma = z^k, c_sigma = 1)."""
        hs, gs = self.backprop_signals(th)
        return -gs[i][:, j] / self.n, hs[i]     # weights c_a, points p_a: U(w) = sum c_a <w,p_a>^k


def U_val(c, P, w, k):
    return np.sum(c * (P @ w) ** k)


def U_grad(c, P, w, k):
    return k * P.T @ (c * (P @ w) ** (k - 1))


def gradient_flow(net, th0, T, rtol=1e-10, atol=1e-14, n_out=4000):
    f = lambda t, th: -net.grad(th)
    ts = np.concatenate([[0.0], np.geomspace(1e-3, T, n_out)])
    sol = solve_ivp(f, (0, T), th0, method="DOP853", t_eval=ts, rtol=rtol, atol=atol)
    return sol.t, sol.y.T
