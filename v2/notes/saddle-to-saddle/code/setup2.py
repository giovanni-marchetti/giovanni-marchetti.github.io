import numpy as np
from resnet import ResNet
def make(seed=0, d=2, L=3, k=3, n=400, noise=0.05):
    rng = np.random.default_rng(seed)
    X = rng.uniform(-1, 1, (n, d))
    Wt = np.zeros((2, d, d)); Wt[0, 0] = [1.2, 0.5]; Wt[1, 1] = [0.6, -1.0]
    Y = ResNet(X, np.zeros_like(X), 2, k).forward(Wt.ravel())[0][-1]
    Y = Y + noise * rng.standard_normal(Y.shape)
    net = ResNet(X, Y, L, k)
    xi = rng.standard_normal(L * d * d)
    return net, xi
