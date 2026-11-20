# Lean formalization of Theorem A of `saddle_short_new.tex`

This is a Lean 4 / Mathlib formalization of Theorem A of `../saddle_short_new.tex` (saddle-to-saddle dynamics at small initialization) and of its whole proof:
- Lemma 1 (Flatness), Lemma 2 (Plateau) and Lemma 3 (Escape);
- Definition 1 (the process);
- the induction (C_m);
- the conclusions (i)–(iii), the critical points and the saddles.

The main theorem is `S2S.theoremA` in `SaddleToSaddle/Main.lean`.

## Trusted base

`#print axioms S2S.theoremA` prints:

```
'S2S.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound,
  S2S.centre_manifold, S2S.unstable_manifold]
```

The first three are Lean's standard axioms. The other two are the results the note cites from the literature. `SaddleToSaddle/Axioms.lean` states each as a special case of the cited theorem.

* **`centre_manifold`**: Carr, *Applications of Centre Manifold Theory* (1981), Chapter 2, Theorem 1.
  - Setting: `ẋ = f(x,y)`, `ẏ = By + g(x,y)`, with `f, g ∈ C²` vanishing together with their first derivatives at `0`, and `B` negative definite.
  - Conclusion: a `C¹` function `h` with `h(0) = 0` and `Dh(0) = 0` that satisfies the invariance equation `Dh(x) f(x,h(x)) = B h(x) + g(x,h(x))` for `|x| < δ`.
* **`unstable_manifold`**: Teschl, *Ordinary Differential Equations and Dynamical Systems* (2012), Theorems 9.4 and 9.5.
  - Setting: an equilibrium `(0, w₀)` of a `C¹` field on `ℝ × W`, with linearization `(r, v) ↦ (λr, r b + Hv)`, where `λ > 0` and `H` is negative definite.
  - Conclusion: there is a graph `w = ψ(r)` through `(0, w₀)` such that every backward orbit that stays in a small ball lies on it. Conversely, every point of the graph near `(0, w₀)` has a backward orbit that stays in the ball and converges to `(0, w₀)`.

There are no other axioms and no `sorry`. Two classical results that the note uses implicitly are proved here from Mathlib rather than assumed:
- Hadamard's lemma with parameters (`Hadamard.lean`);
- existence of maximal solutions with the blow-up alternative (`MaxSol.lean`).

## Building

The project pins Lean `v4.36.0` and Mathlib `v4.36.0` in `lean-toolchain` and `lakefile.toml`. With [elan](https://github.com/leanprover/elan) installed, run in this directory:

```
lake exe cache get    # prebuilt Mathlib
lake build
```

Once Mathlib is downloaded, building the project's own files (about 8,100 lines) takes about two minutes. The build emits only linter warnings.

To check the trusted base, compile a file containing `import SaddleToSaddle` and `#print axioms S2S.theoremA` with `lake env lean`.

## Map from the note to the files

| Note | File | Main declarations |
|---|---|---|
| §1: setting, `S_A`, `π_A`, `θ^{∖n}`, `ι_n`, `ζ_A`, `U_n`, (H) | `Basic.lean`, `Coords.lean` | `Θ`, `S`, `proj`, `zeroAt`, `single`, `insertAt`, `zeta`, `U`, `Flat` |
| Lemma 1, and the polar form `-∇_{w_n}F = ρ^{k-1}G` used in Lemma 3 | `Flatness.lean` | `exists_polar`, `grad_apply_le`, `proj_grad_sub_proj_le`, `proj_grad_sub_zeroAt_le`, `euler`, `F_insertAt_expansion` |
| §1, *Consequences*: invariance of `S_A`, critical points | `GradFlow.lean` | `S_invariant`, `gradient_eq_zero_of_isNondegMin`, `strong_mono` |
| Definition 1 (process, (ND1)–(ND3), limit path) | `Process.lean` | `Process`, `Process.limitPath` |
| Remark after Definition 1 (`U(u_{m+1}) > 0`); `F(θ^{(m+1)}) < F(θ^{(m)})`; saddles | `ProcessFacts.lean` | `U_pos`, `F_lt`, `gradient_θs_eq_zero`, `isSaddle` |
| Lemma 2 (Plateau) | `Plateau.lean` | `PlateauProp`, `plateau` |
| Lemma 3, invariance step | `EscapeInvariance.lean` | `EscHyp`, `escape_invariance` |
| Lemma 3, centre manifold, blow-up and (⋆) | `EscapeUnique.lean` | `BackwardNear`, `escape_unique` |
| Lemma 3(b), shadowing | `Escape.lean` | `EscapeProp`, `escape` |
| Proof of Theorem A: the induction (C_m) | `Stages.lean` | `Claim`, `claim_zero`, `stage_plateau`, `stage_jump` |
| Theorem A | `Main.lean` | `theoremA` |
| ODE tools: continuity argument, Grönwall-type comparisons, time change | `Calculus.lean`, `GradFlow.lean` | `bootstrap`, `norm_le_two_mul_of_deriv_le_pow`, `time_change`, `gf_unique`, `gf_cont_dep` |
| Literature | `Axioms.lean`, `Hadamard.lean`, `MaxSol.lean` | `centre_manifold`, `unstable_manifold`, `hadamard`, `exists_isMaxFwd` |

## Modelling choices

**Abstract loss.** The note observes that the proof uses only smoothness and (H). The formalization works at that level of generality:
- `F : Θ ι E → ℝ` is any `C^∞` function with `Flat F k`;
- `Θ ι E = E^ι` carries the `ℓ²` norm;
- `ι` is a finite type of neurons, and `E` is a finite-dimensional real inner product space (`ℝ^p`).

The short derivation of (H) for polynomial ResNets (the paragraph *Flatness* in §1) is not formalized.

**The gradient flow.** `θ^α` enters as a hypothesis: any family of maximal forward solutions of `θ̇ = -∇F(θ)` with `θ^α(0) = αξ` (`IsMaxFwd`, i.e. a solution on `[0, T⁺)` with the blow-up alternative). Such solutions exist (`exists_isMaxFwd`), and solutions of the flow are unique (`gf_unique`), so the hypothesis is not vacuous and determines `θ^α`. Values outside the domain `D α` play no role. The first conclusion of `theoremA` is that `[0, α^{2-k}S] ⊆ D α` for small `α`.

**The process.** Definition 1 is recursive. The theorem instead takes a structure `Process F k ξ M S`, which bundles two things:
- the data `s_m, A_m, θ^{(m)}, n_m, u_m, γ_m, Ξ_n`;
- the properties that define them under the hypotheses of Theorem A: stages `0, …, M-1` are non-degenerate, and `S ∈ (s_M, s_{M+1})`.

Two of these properties are encoded indirectly:
- (ND1) says `Ξ_{n_{m+1}}` blows up at `s_{m+1}`, while every other dormant `Ξ_n` solves its equation on the closed interval `[s_m, s_{m+1}]`.
- `S < s_{M+1}` says the dormant states of stage `M` solve their equations on `[s_M, S']` for some `S' > S`.

The conclusions involve only parts of the process that `(F, k, ξ)` determine, together with the `γ_m` up to time translation, which the conclusions do not see. So this is the same as speaking about *the* process.

**Escape orbits.** (ND3) supplies `γ_{m+1}` as part of the process. So the existence half of Lemma 3(a) is not needed and is not formalized. Uniqueness up to time translation, (⋆), is proved (`escape_unique`); it is what the shadowing argument of Lemma 3(b) uses.

**Saddles.** `IsSaddle F θ` means that `∇F(θ) = 0` and `θ` is not a local minimum of `F`. This is the sense of the *Consequences* paragraph: a critical point with a direction of strict decrease. It should not be strengthened to "neither a local minimum nor a local maximum": for even `k`, `θ^{(0)} = 0` can be a strict local maximum of `F`. Example: one neuron, `σ(z) = z⁴`, and `y = x + 1` with `x` taking at least two values. Then `F(θ) = F(0) - E[(wx+b)⁴] + O(|θ|⁸)`.

**Statement.** The theorem is reformulated in three small ways:
- "For `α` small" and "as `α → 0`" refer to the filter `𝓝[>] 0`.
- (ii) is split into two cases. For `n ∉ A_M`, `s̄_n > S`, so convergence holds on all of `[0, S]`. For `n = n_m`, it holds on `[0, s_m - δ]`.
- The Hausdorff distance is Mathlib's `hausdorffDist`. Both sets are nonempty and bounded (`γ_m` converges at both ends), so this is the usual Hausdorff distance.

## Notes on the proof

The formal proof follows the note's proof. The points where it fills in details are below.

**Continuity arguments.** Every "continuity argument" goes through `bootstrap` (`Calculus.lean`), a continuous induction on closed sets.

**Lemma 2.** It is proved in a quantitative form that is uniform in the initial data (`PlateauProp`). For `α ≤ α₁` and initial dormant states within `δ₀ ≤ δ₁` of `Ξ(σ₀)`:
- the flow exists on the rescaled interval;
- the dormant error is at most `K(δ₀ + α)`;
- the active error is at most `e^{-μ(t-τ)}|π_Aθ(τ) - θ*| + Kα^k`.

**Lemma 3, centre manifold step.**
- `centre_manifold` is applied with `x = w_n ∈ E` and `y = a - θ* ∈ S_A`.
- A trajectory that stays near `θ*` for all `t ≤ t'` lies on `W^c = {a = θ* + h(w_n)}`. The reason is that `d = a - θ* - h(w_n)` satisfies `⟨d, ḋ⟩ ≤ -(μ/2)|d|²` (strong convexity of `F_A`), so `d` would grow backward in time unless `d ≡ 0`.

**Lemma 3, blow-up step.**
- It is done on `ℝ × E` rather than `ℝ × S^{p-1}`, with `X(ρ,u) = (ρ⟨u,G̃⟩, G̃ - ⟨u,G̃⟩u)`.
- The unit sphere is invariant under `X`.
- The radial eigenvalue at `(0, u*)` is `-2kU(u*) < 0`. So `(0, u*)` is a hyperbolic equilibrium in `ℝ × E`, with the same one-dimensional unstable direction, and `unstable_manifold` applies directly.
- The time change `dτ = ρ^{k-2}dt` is `time_change`.

**Lemma 3(b).**
- The compactness argument uses sequences (`tendsto_subseq_of_bounded`) and continuous dependence (`gf_cont_dep`).
- The normalization `γ(0) = lim θ(t₁)` uses the fact that `|γ_n|` increases strictly through `ρ₁`, since `D ≥ κ > 0`.

**Jumps.** In the induction, the jump time `t^α_m` is the first time after `τ^α_{m-1}` at which `|w_{n_m}|` reaches `ρ₁`.
