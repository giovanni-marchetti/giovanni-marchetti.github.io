import numpy as np, pickle, time
from scipy.integrate import solve_ivp
from setup2 import make
net, xi = make()
st = pickle.load(open('stages2.pkl', 'rb'))
k = net.k
S = 1.0
res = {}
for alpha in [3e-2, 1e-2, 3e-3, 1e-3, 3e-4]:
    t0 = time.time()
    T = S / alpha ** (k - 2)
    s_eval = np.linspace(0, S, 4001)
    sol = solve_ivp(lambda t, th: -net.grad(th), (0, T), alpha * xi, method="DOP853",
                    t_eval=s_eval * T / S, rtol=1e-10, atol=1e-14 * alpha)
    losses = np.array([net.loss(th) for th in sol.y.T])
    res[alpha] = (s_eval, losses, sol.y.T)
    def cross(level):
        i = np.argmax(losses < level); return s_eval[i]
    # distance to predicted plateau parameters
    def dist(s, m):
        i = np.argmin(abs(s_eval - s)); return np.linalg.norm(sol.y.T[i] - st[m]['theta'])
    print(f"alpha={alpha:.0e}: cross(1.9)={cross(1.9):.4f} [pred {st[1]['s']:.4f}], "
          f"cross(0.53)={cross(0.53):.4f} [pred {st[2]['s']:.4f}/{st[3]['s']:.4f}], "
          f"F(0.1)={losses[400]:.4f}, F(0.25)={losses[1000]:.4f}, F(0.6)={losses[2400]:.5f}, "
          f"|th-th1|@0.25={dist(0.25,1):.2e}, |th-th3|@0.6={dist(0.6,3):.2e}  ({time.time()-t0:.0f}s)", flush=True)
pickle.dump(res, open('sim2.pkl', 'wb'))
print("pred plateaus:", [round(s['loss'], 5) for s in st])
