import SaddleToSaddle.Hadamard
import SaddleToSaddle.MaxSol

/-!
# Results from the literature

The proof of Theorem A uses four classical results that are not in Mathlib:

* Hadamard's lemma with parameters (`hadamard`, proved in `Hadamard.lean`);
* existence of maximal solutions of ODEs and the blow-up alternative (`exists_isMaxFwd`, proved
  in `MaxSol.lean`);
* the centre manifold theorem (`centre_manifold`, axiom below);
* the local unstable manifold theorem (`unstable_manifold`, axiom below).

The last two are stated as axioms, each as a special case of the cited theorem. No intermediate
step of the proof of Theorem A is axiomatized: Lemmas 1–3 and the induction are proved in the
other files.

Everything else (uniqueness of ODE solutions, Grönwall's lemma, comparison principles, Taylor's
formula, Bolzano–Weierstrass, …) is taken from Mathlib.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

/-- **The centre manifold theorem** (Carr, *Applications of Centre Manifold Theory*, Chapter 2,
Theorem 1), in the case where the linear part is `0 ⊕ B` with `B` negative definite (so that all
eigenvalues of `B` have negative real part). For `ẋ = f(x, y)`, `ẏ = B y + g(x, y)` with
`f, g ∈ C²` vanishing together with their first derivatives at `0`, there is a centre manifold
`y = h(x)`, with `h(0) = 0`, `Dh(0) = 0`, which is locally invariant; for a `C¹` graph, local
invariance is the tangency equation `Dh(x) f(x, h(x)) = B h(x) + g(x, h(x))` for `|x| < δ`
(Carr, eq. (2.1.4)). Carr's `h` is `C²` on `|x| < δ`; after multiplication by a cut-off equal to
`1` on `|x| < δ/2` it is `C¹` on all of `X`, which is the form stated here. -/
axiom centre_manifold {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (f : X × Y → X) (g : X × Y → Y) (B : Y →L[ℝ] Y)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hDf : fderiv ℝ f 0 = 0) (hDg : fderiv ℝ g 0 = 0)
    (hB : ∃ c > 0, ∀ y, ⟪B y, y⟫ ≤ -c * ‖y‖ ^ 2) :
    ∃ (h : X → Y) (δ : ℝ), 0 < δ ∧ ContDiff ℝ 1 h ∧ h 0 = 0 ∧ fderiv ℝ h 0 = 0 ∧
      ∀ x, ‖x‖ < δ → fderiv ℝ h x (f (x, h x)) = B (h x) + g (x, h x)

/-- **The local unstable manifold theorem** (Teschl, *Ordinary Differential Equations and
Dynamical Systems*, Theorems 9.4 and 9.5), at an equilibrium `(0, w₀)` of a `C¹` vector field on
`ℝ × W` whose linearization is `(r, v) ↦ (λ r, r b + H v)` with `λ > 0` and `H` negative
definite. The equilibrium is hyperbolic, `E^s = {0} × W`, and `E^u` is spanned by
`(1, (λ - H)⁻¹ b)`, which is transverse to `E^s`; so the local unstable manifold is a graph
`w = ψ(ρ)` over the first coordinate.
(i) A solution on `(-∞, 0]` that stays in a small ball around `(0, w₀)` lies on this graph.
(ii) Points of the graph close to `(0, w₀)` have backward orbits that stay in the ball and
converge to `(0, w₀)`. -/
axiom unstable_manifold {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    (X : ℝ × W → ℝ × W) (hX : ContDiff ℝ 1 X) (w₀ : W) (hX0 : X (0, w₀) = 0)
    (lam : ℝ) (hlam : 0 < lam) (b : W) (H : W →L[ℝ] W)
    (hH : ∃ c > 0, ∀ v, ⟪H v, v⟫ ≤ -c * ‖v‖ ^ 2)
    (hDX : ∀ r v, fderiv ℝ X (0, w₀) (r, v) = (lam * r, r • b + H v)) :
    ∃ δ > 0, ∃ ψ : ℝ → W, Continuous ψ ∧ ψ 0 = w₀ ∧
      (∀ y : ℝ → ℝ × W, (∀ τ ≤ 0, HasDerivWithinAt y (X (y τ)) (Iic 0) τ) →
        (∀ τ ≤ 0, dist (y τ) (0, w₀) < δ) → (y 0).2 = ψ (y 0).1) ∧
      (∃ δ' > 0, ∀ r, |r| < δ' → ∃ y : ℝ → ℝ × W, y 0 = (r, ψ r) ∧
        (∀ τ ≤ 0, HasDerivWithinAt y (X (y τ)) (Iic 0) τ) ∧
        (∀ τ ≤ 0, dist (y τ) (0, w₀) < δ) ∧ Tendsto y atBot (𝓝 (0, w₀)))

end S2S
