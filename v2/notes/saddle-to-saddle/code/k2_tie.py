# k = 2, d = 1, L = 2, no bias: h1 = x + (w1 x)^2, f = h1 + (w2 h1)^2, target y = x + c x^2.
# Both neurons have the same utility at theta = 0; check that the endpoint of the first jump
# depends on the ratio of the initial weights.
import numpy as np
from scipy.integrate import solve_ivp
from resnet import ResNet
rng = np.random.default_rng(1)
X = rng.uniform(-1, 1, (400, 1)); c = 0.8
Y = X + c * X ** 2
net = ResNet(X, Y, 2, 2)
alpha = 1e-6
for r in [0.2, 0.5, 0.8, 0.9, 1.0, 1.1, 1.25, 2.0, 5.0]:
    th0 = alpha * np.array([1.0, r])
    sol = solve_ivp(lambda t, th: -net.grad(th), (0, 400), th0, method="DOP853", rtol=1e-10, atol=1e-16)
    w = sol.y[:, -1]
    print(f"xi2/xi1={r:4.2f}: final (w1^2, w2^2)=({w[0]**2:.4f}, {w[1]**2:.4f}), loss={net.loss(w):.2e}")
