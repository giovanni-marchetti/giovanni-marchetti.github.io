import numpy as np, pickle
from setup2 import make
from limit import limit_process
net, xi = make()
print("initial loss", net.loss(np.zeros_like(xi)))
st = limit_process(net, xi, S_max=40.0)
for s in st:
    print(f"s={s['s']:.5f}  A={sorted(s['A'])}  loss={s['loss']:.6g}")
pickle.dump(st, open('stages2.pkl', 'wb'))
