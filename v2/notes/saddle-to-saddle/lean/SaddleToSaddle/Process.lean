import SaddleToSaddle.Basic

/-!
# The saddle-to-saddle process (Definition 1)

`Process F k ξ M S` records the data of the saddle-to-saddle process started at `ξ`, up to
stage `M`, together with the properties that define it, under the assumptions of Theorem A:
stages `0, …, M-1` are non-degenerate, and `S ∈ (s_M, s_{M+1})`.

* Each dormant `Ξ_i`, `i ∉ A_m`, solves `dΞ_i/ds = ∇U^{(m)}_i(Ξ_i)` during stage `m`.
* (ND1) `s_{m+1}` is the blow-up time of `Ξ_{n_{m+1}}` only: `|Ξ_{n_{m+1}}(s)| → ∞` as
  `s ↑ s_{m+1}`, while every other dormant state solves its equation on the closed interval
  `[s_m, s_{m+1}]` (so its blow-up time is larger). `Ξ_i(s_{m+1})` is then the left limit, by
  continuity.
* (ND2) the direction of `Ξ_{n_{m+1}}` converges to a non-degenerate local maximum `u_{m+1}` of
  `U^{(m)}_{n_{m+1}}` on the sphere.
* (ND3) the escape orbit `γ_{m+1}` of `θ^{(m)}` along `(n_{m+1}, u_{m+1})` is defined for all
  times and converges to a non-degenerate local minimum `θ^{(m+1)}` of `F_{A_{m+1}}`.
* `S < s_{M+1}` means that the dormant states of the last stage solve their equation on
  `[s_M, S']` for some `S' > S` (the blow-up times are larger than `S - s_M`).

Since the process is uniquely determined by `F`, `k` and `ξ` (uniqueness of ODE solutions and of
escape orbits up to translation), quantifying over all such structures is the same as speaking
about *the* process.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The saddle-to-saddle process up to stage `M`, with stages `0, …, M-1` non-degenerate, and a
horizon `S ∈ (s_M, s_{M+1})`. -/
structure Process (F : Θ ι E → ℝ) (k : ℕ) (ξ : Θ ι E) (M : ℕ) (S : ℝ) where
  /-- jump times `0 = s_0 < s_1 < ⋯ < s_M` -/
  s : ℕ → ℝ
  /-- active sets `A_m` -/
  A : ℕ → Finset ι
  /-- plateaus `θ^{(m)}` -/
  θs : ℕ → Θ ι E
  /-- the neuron `n_m` activated at `s_m`, `1 ≤ m ≤ M` -/
  n : ℕ → ι
  /-- the escape direction `u_m` -/
  u : ℕ → E
  /-- the escape orbit `γ_m` -/
  γ : ℕ → ℝ → Θ ι E
  /-- the dormant states `Ξ_i` -/
  Ξ : ι → ℝ → E
  s_zero : s 0 = 0
  A_zero : A 0 = ∅
  θs_zero : θs 0 = 0
  Ξ_zero : ∀ i, Ξ i 0 = ξ i
  s_lt : ∀ m < M, s m < s (m + 1)
  s_lt_S : s M < S
  isMin : ∀ m ≤ M, IsNondegMin F (A m) (θs m)
  n_notMem : ∀ m < M, n (m + 1) ∉ A m
  A_succ : ∀ m < M, A (m + 1) = insert (n (m + 1)) (A m)
  /-- dormant dynamics during stage `m < M` of the neurons that stay dormant (ND1) -/
  dormant : ∀ m < M, ∀ i ∉ A (m + 1), ∀ σ ∈ Icc (s m) (s (m + 1)),
    HasDerivWithinAt (Ξ i) (gradient (U F k i (θs m)) (Ξ i σ)) (Icc (s m) (s (m + 1))) σ
  /-- dormant dynamics during stage `m < M` of the neuron `n_{m+1}`, up to its blow-up -/
  dormant_act : ∀ m < M, ∀ σ ∈ Ico (s m) (s (m + 1)),
    HasDerivWithinAt (Ξ (n (m + 1))) (gradient (U F k (n (m + 1)) (θs m)) (Ξ (n (m + 1)) σ))
      (Ico (s m) (s (m + 1))) σ
  /-- (ND1) `Ξ_{n_{m+1}}` blows up at `s_{m+1}` -/
  blowup : ∀ m < M, Tendsto (fun σ => ‖Ξ (n (m + 1)) σ‖) (𝓝[<] (s (m + 1))) atTop
  /-- (ND2) its direction converges to `u_{m+1}` … -/
  dir : ∀ m < M, Tendsto (fun σ => ‖Ξ (n (m + 1)) σ‖⁻¹ • Ξ (n (m + 1)) σ) (𝓝[<] (s (m + 1)))
    (𝓝 (u (m + 1)))
  /-- (ND2) … a non-degenerate local maximum of `U^{(m)}_{n_{m+1}}` on the sphere -/
  u_max : ∀ m < M, IsNondegMaxSphere (U F k (n (m + 1)) (θs m)) k (u (m + 1))
  /-- (ND3) the escape orbit `γ_{m+1}`, defined for all times … -/
  escape : ∀ m < M, IsEscapeOrbit F (A m) (θs m) (n (m + 1)) (u (m + 1)) (γ (m + 1))
  /-- (ND3) … converges to `θ^{(m+1)}` -/
  escape_lim : ∀ m < M, Tendsto (γ (m + 1)) atTop (𝓝 (θs (m + 1)))
  /-- `S < s_{M+1}`: the dormant states of the last stage do not blow up before some `S' > S` -/
  S' : ℝ
  S_lt_S' : S < S'
  /-- dormant dynamics during the last stage, up to `S'` -/
  dormant_last : ∀ i ∉ A M, ∀ σ ∈ Icc (s M) S',
    HasDerivWithinAt (Ξ i) (gradient (U F k i (θs M)) (Ξ i σ)) (Icc (s M) S') σ

namespace Process

variable {F : Θ ι E → ℝ} {k : ℕ} {ξ : Θ ι E} {M : ℕ} {S : ℝ}

/-- The limit path `θ̄(s) = θ^{(m)}` for `s_m ≤ s < s_{m+1}`, `m ≤ M`. -/
def limitPath (P : Process F k ξ M S) (σ : ℝ) : Θ ι E :=
  P.θs ((Finset.Icc 1 M).filter (fun j => P.s j ≤ σ)).card

end Process

end S2S
