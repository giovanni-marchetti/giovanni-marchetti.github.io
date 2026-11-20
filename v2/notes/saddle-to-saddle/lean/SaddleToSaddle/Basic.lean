import Mathlib

/-!
# Saddle-to-saddle dynamics: the setting

This file sets up the abstract setting of Theorem A of `saddle_short_new.tex`.

* `Θ ι E = (ℝ^p)^N` is the parameter space: one weight vector `w_n ∈ E` per neuron `n ∈ ι`,
  with the Euclidean norm (`PiLp 2`).
* `F : Θ ι E → ℝ` is a `C^∞` loss satisfying the flatness hypothesis `(H)` (`Flat F k`).
  As the note explains, depth, width and biases play no further role: the proof uses only
  smoothness and `(H)`.
* `U F k n θ w` is the utility `U_n(θ; w) = -(1/k!) D^k_{w_n} F(θ^{\n})[w,…,w]`.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

/-- The parameter space `Θ = (ℝ^p)^N`, with the Euclidean norm. -/
abbrev Θ (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type _ :=
  PiLp 2 (fun _ : ι => E)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Coordinates -/

/-- `ι_n(w)`: the parameter whose `n`-th component is `w` and whose other components vanish. -/
def single (n : ι) (w : E) : Θ ι E := WithLp.toLp 2 (Pi.single n w)

/-- The linear map setting the components in `B` to zero. -/
def zeroOut (B : Finset ι) : Θ ι E →L[ℝ] Θ ι E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ => WithLp.toLp 2 (fun m => if m ∈ B then 0 else θ m)
      map_add' := by
        intro x y
        ext m
        by_cases h : m ∈ B <;> simp [h]
      map_smul' := by
        intro c x
        ext m
        by_cases h : m ∈ B <;> simp [h] }

/-- `π_A`: the orthogonal projection onto `S_A`. -/
abbrev proj (A : Finset ι) : Θ ι E →L[ℝ] Θ ι E := zeroOut Aᶜ

/-- `θ^{\n}`: `θ` with `w_n` replaced by `0`. -/
abbrev zeroAt (n : ι) : Θ ι E →L[ℝ] Θ ι E := zeroOut {n}

/-- `θ` with `w_n` replaced by `w`, i.e. `θ^{\n} + ι_n(w)`. -/
def insertAt (θ : Θ ι E) (n : ι) (w : E) : Θ ι E := zeroAt n θ + single n w

/-- The subspace `S_A = {θ : w_n = 0 for all n ∉ A}`. -/
def S (A : Finset ι) : Set (Θ ι E) := {θ | ∀ m ∉ A, θ m = 0}

/-- `ζ_A(θ) = ∑_{n ∉ A} |w_n|^k`. -/
def zeta (k : ℕ) (A : Finset ι) (θ : Θ ι E) : ℝ := ∑ m ∈ Aᶜ, ‖θ m‖ ^ k

/-! ### The loss -/

/-- The flatness hypothesis `(H)`: for every neuron `n`, all partial derivatives of `F` of orders
`1, …, k-1` with respect to the coordinates of `w_n` vanish on `{w_n = 0}`. Equivalently, the
iterated derivatives of order `1 ≤ j ≤ k-1` of `w ↦ F(θ^{\n} + ι_n(w))` vanish at `w = 0`. -/
def Flat (F : Θ ι E → ℝ) (k : ℕ) : Prop :=
  ∀ (n : ι) (θ : Θ ι E) (j : ℕ), 1 ≤ j → j < k →
    iteratedFDeriv ℝ j (fun w : E => F (insertAt θ n w)) 0 = 0

/-- The utility of neuron `n` at `θ`: the `k`-form
`U_n(θ; w) = -(1/k!) D^k_{w_n} F(θ^{\n})[w, …, w]`. -/
def U (F : Θ ι E → ℝ) (k : ℕ) (n : ι) (θ : Θ ι E) (w : E) : ℝ :=
  -((k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k (fun v : E => F (insertAt θ n v)) 0 (fun _ => w))

/-- The gradient-flow vector field `θ ↦ -∇F(θ)`. -/
def gf (F : Θ ι E → ℝ) (θ : Θ ι E) : Θ ι E := -gradient F θ

/-! ### Non-degenerate critical points -/

/-- `θ₀` is a non-degenerate local minimum of `F_A = F|_{S_A}`: `θ₀ ∈ S_A`, `∇F_A(θ₀) = 0`, and
`∇²F_A(θ₀)` is positive definite. -/
structure IsNondegMin (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) : Prop where
  mem : θ₀ ∈ S A
  crit : ∀ v ∈ S A, fderiv ℝ F θ₀ v = 0
  posdef : ∃ c > 0, ∀ v ∈ S A, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) θ₀ v v

/-- `u` is a non-degenerate local maximum of the restriction of the `k`-form `U` to the unit
sphere: a critical point of `U|_{S^{p-1}}` at which the Riemannian Hessian
`(∇²U(u) - k U(u) I)|_{u^⊥}` is negative definite. -/
structure IsNondegMaxSphere (U : E → ℝ) (k : ℕ) (u : E) : Prop where
  norm_eq : ‖u‖ = 1
  crit : ∀ v, ⟪v, u⟫ = 0 → fderiv ℝ U u v = 0
  hess : ∃ c > 0, ∀ v, ⟪v, u⟫ = 0 →
    fderiv ℝ (fderiv ℝ U) u v v - k * U u * ‖v‖ ^ 2 ≤ -c * ‖v‖ ^ 2

/-- A saddle point of `F`: a critical point which is not a local minimum. -/
def IsSaddle (F : Θ ι E → ℝ) (θ₀ : Θ ι E) : Prop :=
  gradient F θ₀ = 0 ∧ ¬ IsLocalMin F θ₀

/-! ### Trajectories -/

/-- `γ` is a maximal forward solution of `ẋ = V(x)` defined on `D`, where `D` is an interval
`[0, T)` with `0 < T ≤ ∞`: if `γ` is bounded on `[0, b) ⊆ D`, then `D` contains `[0, b + ε)`
for some `ε > 0` (blow-up alternative). -/
structure IsMaxFwd {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : X → X) (γ : ℝ → X) (D : Set ℝ) : Prop where
  zero_mem : (0 : ℝ) ∈ D
  subset_Ici : D ⊆ Ici 0
  ordConnected : D.OrdConnected
  sol : ∀ t ∈ D, HasDerivWithinAt γ (V (γ t)) (Ici 0) t
  maximal : ∀ b, 0 ≤ b → Ico 0 b ⊆ D → Bornology.IsBounded (γ '' Ico 0 b) →
    ∃ ε > 0, Ico 0 (b + ε) ⊆ D

/-- The escape orbit of `θ₀` along `(n, u)`, here required to be defined for all times: a
gradient-flow trajectory `γ : ℝ → S_{A ∪ {n}}` with `γ(t) → θ₀` and `γ_n(t)/|γ_n(t)| → u` as
`t → -∞`. -/
structure IsEscapeOrbit (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) (u : E)
    (γ : ℝ → Θ ι E) : Prop where
  mem : ∀ t, γ t ∈ S (insert n A)
  sol : ∀ t, HasDerivAt γ (gf F (γ t)) t
  tendsto : Tendsto γ atBot (𝓝 θ₀)
  dir : Tendsto (fun t => ‖γ t n‖⁻¹ • γ t n) atBot (𝓝 u)

end S2S
