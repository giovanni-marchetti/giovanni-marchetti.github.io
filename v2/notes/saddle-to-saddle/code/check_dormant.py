import numpy as np, pickle
from setup2 import make
from limit import flow_for
net, xi = make()
st = pickle.load(open('stages2.pkl', 'rb')); res = pickle.load(open('sim2.pkl', 'rb'))
L, d, k = net.L, net.d, net.k
s1, s_check = st[1]['s'], 0.25
Xi = xi.reshape(L, d, d).copy()
dormant1 = [(i, j) for i in range(L) for j in range(d) if (i, j) not in st[1]['A']]
for n in dormant1:     # stage 0 up to s1, then stage-1 utilities up to s_check
    c, P = net.utility_coeffs(np.zeros(L*d*d), *n); Xi[n] = flow_for(c, P, Xi[n], k, s1)
    c, P = net.utility_coeffs(st[1]['theta'], *n);  Xi[n] = flow_for(c, P, Xi[n], k, s_check - s1)
for alpha in sorted(res, reverse=True):
    s_eval, losses, ths = res[alpha]
    i = np.argmin(abs(s_eval - s_check)); W = ths[i].reshape(L, d, d)
    err = max(np.linalg.norm(W[n] / alpha - Xi[n]) for n in dormant1)
    print(f"alpha={alpha:.0e}: max_n |w_n/alpha - Xi_n(0.25)| = {err:.2e}   (|Xi| ~ {max(np.linalg.norm(Xi[n]) for n in dormant1):.2f})")
