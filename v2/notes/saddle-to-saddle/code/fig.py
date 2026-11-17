import numpy as np, pickle, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams.update({"font.family": "serif", "font.size": 9, "mathtext.fontset": "cm",
                     "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6})
res = pickle.load(open('sim2.pkl', 'rb')); st = pickle.load(open('stages2.pkl', 'rb'))
fig, ax = plt.subplots(figsize=(5.2, 2.6))
alphas = sorted(res, reverse=True)
greys = np.linspace(0.78, 0.0, len(alphas))
for a, g in zip(alphas, greys):
    s, F, _ = res[a]
    ax.plot(s, F, color=str(g), lw=0.9, label=rf"$\alpha = {a:.0e}$".replace("e-0", r"\cdot 10^{-") + "}$" if False else None)
labels = {3e-2: r"$3\cdot10^{-2}$", 1e-2: r"$10^{-2}$", 3e-3: r"$3\cdot10^{-3}$", 1e-3: r"$10^{-3}$", 3e-4: r"$3\cdot10^{-4}$"}
for line, a in zip(ax.get_lines(), alphas):
    line.set_label(r"$\alpha=$" + labels[a])
# limit step function
ss = [x['s'] for x in st] + [1.0]
Fs = [x['loss'] for x in st]
for i in range(len(Fs)):
    lo, hi = ss[i], min(ss[i + 1], 1.0)
    if lo < 1.0:
        ax.plot([lo, hi], [Fs[i], Fs[i]], color="#b03a2e", lw=1.4, ls=(0, (4, 2)), zorder=5,
                label="limit (Theorem 1)" if i == 0 else None)
ax.set_yscale("log"); ax.set_xlim(0, 1.0); ax.set_ylim(1e-3, 6)
ax.set_xlabel(r"rescaled time $s = \alpha^{k-2} t$"); ax.set_ylabel(r"loss $F(\theta^\alpha(t))$")
ax.legend(frameon=False, fontsize=7.5, loc="upper right", ncol=2)
for sp in ["top", "right"]: ax.spines[sp].set_visible(False)
fig.tight_layout(); fig.savefig("loss_curves.pdf"); fig.savefig("loss_curves.png", dpi=200)
