import SaddleToSaddle.EscapeUnique

/-!
# Lemma 3 (Escape)

Given an escape orbit `γ` of `θ*` along `(n, u*)` (Lemma 3(a) gives its existence and
uniqueness up to translation; in Theorem A it is provided by (ND3)), we prove:

* `|γ_n|` reaches `ρ₁`; we normalize `γ` by the first time `c` at which `|γ_n(c)| = ρ₁`
  (proof of (a));
* Lemma 3(b), invariance: under the assumptions of (b) at `t₀`, `ρ` increases and reaches `ρ₁`
  at a time `t₁ ≤ t₀ + C ρ₀^{2-k}`, and `|z| ≤ 2η` on `[t₀, t₁]`;
* Lemma 3(b), shadowing: as `ρ₀ → 0`, uniformly in the trajectory, `θ(t₁) → γ(c)` and
  `sup_{[t₀, t₁]} dist(θ, γ((-∞, c])) → 0` (compactness, continuous dependence and `(⋆)`).
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- The conclusion of Lemma 3(b), for a given escape orbit `γ`, with constants
`ρ₁, r, ε₁, C` and normalization time `c`. -/
def EscapeProp (F : Θ ι E → ℝ) (k : ℕ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) (u₀ : E)
    (γ : ℝ → Θ ι E) (ρ₁ r ε₁ C c : ℝ) : Prop :=
  0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < r ∧ 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < C ∧
    -- normalization of `γ`: `|γ_n|` first reaches `ρ₁` at time `c`
    ‖γ c n‖ = ρ₁ ∧ (∀ t < c, ‖γ t n‖ < ρ₁) ∧
    -- (b): `ρ` increases to `ρ₁` in time `O(ρ₀^{2-k})`, and `|z| ≤ 2η`
    (∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
      EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) →
      ∃ t₁ ∈ D, t₀ < t₁ ∧ ‖θ t₁ n‖ = ρ₁ ∧ (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) ∧
        t₁ - t₀ ≤ C * (‖θ t₀ n‖ ^ (k - 2))⁻¹ ∧
        ∀ t ∈ Icc t₀ t₁,
          ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
          ‖θ t - θ₀‖ ≤ 1) ∧
    -- (b): shadowing, uniformly in the trajectory as `ρ₀ → 0`
    (∀ ε > 0, ∃ δ > 0, ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
      EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) → ‖θ t₀ n‖ < δ →
      ∀ t₁ ∈ D, t₀ < t₁ → ‖θ t₁ n‖ = ρ₁ → (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) →
        ‖θ t₁ - γ c‖ < ε ∧ ∀ t ∈ Icc t₀ t₁, ∃ s ≤ c, ‖θ t - γ s‖ < ε)

/-! ### Auxiliary lemmas -/

/-- The conclusion of `escape_invariance`, for fixed constants `ρ₁, r, ε₁, C`. -/
private abbrev InvProp (F : Θ ι E → ℝ) (k : ℕ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) (u₀ : E)
    (ρ₁ r ε₁ C : ℝ) : Prop :=
  ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
    EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) →
    ∃ t₁ ∈ D, t₀ < t₁ ∧ ‖θ t₁ n‖ = ρ₁ ∧ (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) ∧
      ∀ t ∈ Icc t₀ t₁,
        ‖θ t₀ n‖ ≤ ‖θ t n‖ ∧
        t₁ - t ≤ C * (‖θ t n‖ ^ (k - 2))⁻¹ ∧
        (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁ - t) ∧
        ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
        ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧
        ‖proj A (θ t) - θ₀‖ ≤ ‖θ t₀ n‖ + C * ‖θ t n‖ ^ k

/-- The first time at which `‖θ t n‖ = ρ₁` is unique, so the bounds of the invariance step hold
for any such time `t₁`. -/
private lemma inv_bounds {A : Finset ι} {θ₀ : Θ ι E} {n : ι} {u₀ : E} {ρ₁ r ε₁ C : ℝ}
    (hinv : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C) {θ : ℝ → Θ ι E} {D : Set ℝ}
    (hmax : IsMaxFwd (gf F) θ D) {t₀ : ℝ} (ht₀ : t₀ ∈ D)
    (hesc : EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀)) {t₁ : ℝ} (ht₁ : t₀ < t₁)
    (hρt₁ : ‖θ t₁ n‖ = ρ₁) (hfirst : ∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) :
    ∀ t ∈ Icc t₀ t₁,
      ‖θ t₀ n‖ ≤ ‖θ t n‖ ∧
      t₁ - t ≤ C * (‖θ t n‖ ^ (k - 2))⁻¹ ∧
      (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁ - t) ∧
      ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
      ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧
      ‖proj A (θ t) - θ₀‖ ≤ ‖θ t₀ n‖ + C * ‖θ t n‖ ^ k := by
  obtain ⟨t₁', -, ht₁', hρ', hfirst', hb⟩ := hinv θ D hmax t₀ ht₀ hesc
  have heq : t₁' = t₁ := by
    rcases lt_trichotomy t₁' t₁ with h | h | h
    · exact absurd hρ' (hfirst t₁' ⟨ht₁'.le, h⟩).ne
    · exact h
    · exact absurd hρt₁ (hfirst' t₁ ⟨ht₁.le, h⟩).ne
  subst heq
  exact hb

private lemma norm_le_of_first {θ : ℝ → Θ ι E} {n : ι} {ρ₁ t₀ t₁ : ℝ} (hρt₁ : ‖θ t₁ n‖ = ρ₁)
    (hfirst : ∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) : ∀ t ∈ Icc t₀ t₁, ‖θ t n‖ ≤ ρ₁ := by
  intro t ht
  rcases ht.2.lt_or_eq with h | h
  · exact (hfirst t ⟨ht.1, h⟩).le
  · rw [h, hρt₁]

/-- `‖θ - θ*‖ ≤ ‖a - θ*‖ + ρ + ‖z‖`. -/
private lemma norm_sub_le_parts {A : Finset ι} {n : ι} (hn : n ∉ A) (θ₀ x : Θ ι E) :
    ‖x - θ₀‖ ≤ ‖proj A x - θ₀‖ + ‖x n‖ + ‖x - proj (insert n A) x‖ := by
  have h := decomp hn x
  have e : x - θ₀ = (proj A x - θ₀) + single n (x n) + (x - proj (insert n A) x) := by
    calc x - θ₀ = (proj A x + single n (x n) + (x - proj (insert n A) x)) - θ₀ := by rw [← h]
      _ = (proj A x - θ₀) + single n (x n) + (x - proj (insert n A) x) := by abel
  rw [e]
  calc ‖(proj A x - θ₀) + single n (x n) + (x - proj (insert n A) x)‖
      ≤ ‖(proj A x - θ₀) + single n (x n)‖ + ‖x - proj (insert n A) x‖ := norm_add_le _ _
    _ ≤ ‖proj A x - θ₀‖ + ‖single n (x n)‖ + ‖x - proj (insert n A) x‖ := by
        gcongr; exact norm_add_le _ _
    _ = ‖proj A x - θ₀‖ + ‖x n‖ + ‖x - proj (insert n A) x‖ := by rw [norm_single]

/-- A trajectory as in (b), shifted so that `t₁ = 0`, on `[-L, 0]`, with `ρ₀ = ρ0`. -/
private structure Shifted (F : Θ ι E → ℝ) (k : ℕ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) (u₀ : E)
    (ρ₁ r C rU : ℝ) (ψ : ℝ → Θ ι E) (L ρ0 : ℝ) : Prop where
  sol : ∀ s ∈ Icc (-L) 0, HasDerivWithinAt ψ (gf F (ψ s)) (Icc (-L) 0) s
  end_eq : ‖ψ 0 n‖ = ρ₁
  pos : ∀ s ∈ Icc (-L) 0, 0 < ‖ψ s n‖
  le : ∀ s ∈ Icc (-L) 0, ‖ψ s n‖ ≤ ρ₁
  low : ∀ s ∈ Icc (-L) 0, ((ρ₁ ^ (k - 2))⁻¹ + C * (-s))⁻¹ ≤ ‖ψ s n‖ ^ (k - 2)
  z : ∀ s ∈ Icc (-L) 0, ‖ψ s - proj (insert n A) (ψ s)‖ ≤ 2 * ρ0
  u : ∀ s ∈ Icc (-L) 0, ‖‖ψ s n‖⁻¹ • ψ s n - u₀‖ ≤ r
  a : ∀ s ∈ Icc (-L) 0, ‖proj A (ψ s) - θ₀‖ ≤ rU
  near : ∀ s ∈ Icc (-L) 0, ‖ψ s - θ₀‖ ≤ 1

private lemma shifted_of_data {A : Finset ι} {n : ι} (hn : n ∉ A) {θ₀ : Θ ι E}
    {u₀ : E} {ρ₁ r ε₁ C rU : ℝ} (hinv : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C)
    (hC : 0 < C) (hε₁ : ε₁ ≤ 1)
    (hrU : ρ₁ + C * ρ₁ ^ k ≤ rU) (h1 : 4 * ρ₁ + C * ρ₁ ^ k ≤ 1)
    {θ : ℝ → Θ ι E} {D : Set ℝ} (hmax : IsMaxFwd (gf F) θ D) {t₀ : ℝ} (ht₀ : t₀ ∈ D)
    (hesc : EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀)) {t₁ : ℝ} (ht₁D : t₁ ∈ D) (ht₁ : t₀ < t₁)
    (hρt₁ : ‖θ t₁ n‖ = ρ₁) (hfirst : ∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) :
    Shifted F k A θ₀ n u₀ ρ₁ r C rU (fun s => θ (t₁ + s)) (t₁ - t₀) ‖θ t₀ n‖ ∧
      (‖θ t₀ n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁ - t₀) := by
  have hb := inv_bounds hinv hmax ht₀ hesc ht₁ hρt₁ hfirst
  have hρle := norm_le_of_first hρt₁ hfirst
  have hlow₀ := (hb t₀ ⟨le_rfl, ht₁.le⟩).2.2.1
  obtain ⟨hρ0pos, hρ0lt, -, hz0, -⟩ := hesc
  have hε₁ρ : ε₁ * ‖θ t₀ n‖ ≤ ‖θ t₀ n‖ := mul_le_of_le_one_left (norm_nonneg _) hε₁
  have hmt : ∀ s ∈ Icc (-(t₁ - t₀)) 0, t₁ + s ∈ Icc t₀ t₁ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ha' : ∀ s ∈ Icc (-(t₁ - t₀)) 0, ‖proj A (θ (t₁ + s)) - θ₀‖ ≤ ρ₁ + C * ρ₁ ^ k := by
    intro s hs
    have h := (hb _ (hmt s hs)).2.2.2.2.2
    have hpow : ‖θ (t₁ + s) n‖ ^ k ≤ ρ₁ ^ k := pow_le_pow_left₀ (norm_nonneg _) (hρle _ (hmt s hs)) k
    have hCp : C * ‖θ (t₁ + s) n‖ ^ k ≤ C * ρ₁ ^ k := mul_le_mul_of_nonneg_left hpow hC.le
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hlow₀⟩
  · intro s hs
    have h1 := hmax.hasDerivWithinAt_Icc ht₀ ht₁D (t₁ + s) (hmt s hs)
    have h2 : HasDerivWithinAt (fun s : ℝ => t₁ + s) 1 (Icc (-(t₁ - t₀)) 0) s :=
      ((hasDerivAt_id s).const_add t₁).hasDerivWithinAt
    have h3 := h1.scomp s h2 hmt
    rw [one_smul] at h3
    exact h3
  · simpa using hρt₁
  · intro s hs
    exact lt_of_lt_of_le hρ0pos (hb _ (hmt s hs)).1
  · intro s hs
    exact hρle _ (hmt s hs)
  · intro s hs
    have hpos : 0 < ‖θ (t₁ + s) n‖ := lt_of_lt_of_le hρ0pos (hb _ (hmt s hs)).1
    have h := (hb _ (hmt s hs)).2.2.1
    have e : t₁ - (t₁ + s) = -s := by ring
    rw [e] at h
    exact inv_le_of_inv_le₀ (pow_pos hpos _) h
  · intro s hs
    have h := (hb _ (hmt s hs)).2.2.2.1
    show ‖θ (t₁ + s) - proj (insert n A) (θ (t₁ + s))‖ ≤ 2 * ‖θ t₀ n‖
    linarith
  · intro s hs
    exact (hb _ (hmt s hs)).2.2.2.2.1
  · intro s hs
    exact (ha' s hs).trans hrU
  · intro s hs
    have h := norm_sub_le_parts hn θ₀ (θ (t₁ + s))
    have hz := (hb _ (hmt s hs)).2.2.2.1
    have ha := ha' s hs
    have hle := hρle _ (hmt s hs)
    show ‖θ (t₁ + s) - θ₀‖ ≤ 1
    linarith

/-- **The limit trajectory.** If shifted trajectories as in (b) with `ρ₀ → 0` have endpoints
converging to `x`, then `x = γ(c)`: the backward solution through `x` is a locally uniform limit
of the trajectories, satisfies the assumptions of `(⋆)`, hence is a time translate of `γ`, and
the normalization fixes the translation. -/
private lemma limit_eq (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) {A : Finset ι} {n : ι}
    {θ₀ : Θ ι E} {u₀ : E} {ρ₁ r C rU ρU : ℝ} (hρ₁ : 0 < ρ₁) (hC : 0 < C) (hrrU : r ≤ rU)
    (hρ₁ρU : ρ₁ ≤ ρU)
    (huniq : ∀ (θa θb : ℝ → Θ ι E) (t₁' t₂' : ℝ),
        BackwardNear F A n θ₀ u₀ ρU rU θa t₁' → BackwardNear F A n θ₀ u₀ ρU rU θb t₂' →
        ∃ s₁ ≤ t₁', ∃ s₂ ≤ t₂', θa s₁ = θb s₂)
    {γ : ℝ → Θ ι E} (hγsol : ∀ t, HasDerivAt γ (gf F (γ t)) t) {T₁ c : ℝ}
    (hγB : BackwardNear F A n θ₀ u₀ ρU rU γ T₁) (hc : ∀ t < c, ‖γ t n‖ < ρ₁)
    (hstrict : ∀ c' > c, ∃ t < c', ρ₁ < ‖γ t n‖)
    {ψ : ℕ → ℝ → Θ ι E} {L ρ0 : ℕ → ℝ}
    (hS : ∀ j, Shifted F k A θ₀ n u₀ ρ₁ r C rU (ψ j) (L j) (ρ0 j))
    (hL : Tendsto L atTop atTop) (hρ0 : Tendsto ρ0 atTop (𝓝 0))
    {x : Θ ι E} (hx : Tendsto (fun j => ψ j 0) atTop (𝓝 x)) : x = γ c := by
  -- the backward maximal solution through `x`
  have hV : ContDiff ℝ 1 (fun y => -gf F y) := ((gf_contDiff hF).neg).of_le (by simp)
  obtain ⟨β, Dβ, hβ, hβ0⟩ := exists_isMaxFwd (fun y => -gf F y) hV x
  set θi : ℝ → Θ ι E := fun t => β (-t) with hθi
  have hθi0 : θi 0 = x := by simp [hθi, hβ0]
  -- `θi` solves the gradient flow on `[-T, 0]` for `T ∈ Dβ`
  have hder : ∀ T ∈ Dβ, ∀ t ∈ Icc (-T) 0,
      HasDerivWithinAt θi (gf F (θi t)) (Icc (-T) 0) t := by
    intro T hT t ht
    have hmt : MapsTo (Neg.neg : ℝ → ℝ) (Icc (-T) 0) (Icc 0 T) := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hsub : Icc 0 T ⊆ Dβ := hβ.Icc_zero_subset hT
    have h1 : HasDerivWithinAt β (-gf F (β (-t))) (Icc 0 T) (-t) :=
      (hβ.sol (-t) (hsub (hmt ht))).mono (hsub.trans hβ.subset_Ici)
    have h2 : HasDerivWithinAt (Neg.neg : ℝ → ℝ) (-1) (Icc (-T) 0) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    have h3 := h1.scomp t h2 hmt
    rw [neg_one_smul, neg_neg] at h3
    exact h3
  -- the shifted trajectories converge to `θi` on `[-T, 0]`
  have hconv : ∀ T ∈ Dβ, ∀ t ∈ Icc (-T) 0, Tendsto (fun j => ψ j t) atTop (𝓝 (θi t)) := by
    intro T hT t ht
    have hT0 : 0 ≤ T := hβ.nonneg hT
    obtain ⟨δ₀, hδ₀, K, hK, hdep⟩ := gf_cont_dep hF (by linarith : -T ≤ 0) (hder T hT)
    have hx' : Tendsto (fun j => ‖ψ j 0 - x‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hx
    have hev : ∀ᶠ j in atTop, ‖ψ j t - θi t‖ ≤ K * ‖ψ j 0 - x‖ := by
      filter_upwards [hL.eventually_ge_atTop T, hx'.eventually (eventually_le_nhds hδ₀)]
        with j hj1 hj2
      have hsol : ∀ s ∈ Icc (-T) 0,
          HasDerivWithinAt (ψ j) (gf F (ψ j s)) (Icc (-T) 0) s := fun s hs =>
        ((hS j).sol s ⟨by linarith [hs.1], hs.2⟩).mono (Icc_subset_Icc (by linarith) le_rfl)
      have h := hdep (ψ j) hsol 0 ⟨by linarith, le_rfl⟩ (by rw [hθi0]; exact hj2) t ht
      rwa [hθi0] at h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) hev ?_
    simpa using hx'.const_mul K
  -- hence `θi` is bounded on its domain, which is therefore `[0, ∞)`
  have hbd : ∀ T ∈ Dβ, ‖β T - θ₀‖ ≤ 1 := by
    intro T hT
    have hT0 : 0 ≤ T := hβ.nonneg hT
    have h1 := hconv T hT (-T) ⟨le_rfl, by linarith⟩
    have h2 : θi (-T) = β T := by simp [hθi]
    rw [h2] at h1
    refine le_of_tendsto (h1.sub_const θ₀).norm ?_
    filter_upwards [hL.eventually_ge_atTop T] with j hj
    exact (hS j).near (-T) ⟨by linarith, by linarith⟩
  have hall : ∀ T, 0 ≤ T → T ∈ Dβ := by
    intro T hT
    refine hβ.Icc_subset_of_bounded (b := T) (R := ‖θ₀‖ + 1) hβ.zero_mem
      (fun t _ htD => ?_) ⟨hT, le_rfl⟩
    have h := hbd t htD
    calc ‖β t‖ = ‖(β t - θ₀) + θ₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖β t - θ₀‖ + ‖θ₀‖ := norm_add_le _ _
      _ ≤ ‖θ₀‖ + 1 := by linarith
  have hconv' : ∀ t ≤ 0, Tendsto (fun j => ψ j t) atTop (𝓝 (θi t)) := fun t ht =>
    hconv (-t) (hall (-t) (by linarith)) t ⟨(neg_neg t).le, ht⟩
  have hevS : ∀ t ≤ 0, ∀ᶠ j in atTop, t ∈ Icc (-L j) 0 := fun t ht => by
    filter_upwards [hL.eventually_ge_atTop (-t)] with j hj
    exact ⟨by linarith, ht⟩
  have hcn : ∀ t ≤ 0, Tendsto (fun j => ψ j t n) atTop (𝓝 (θi t n)) := fun t ht =>
    ((PiLp.continuous_apply 2 (fun _ : ι => E) n).tendsto _).comp (hconv' t ht)
  -- the bounds pass to the limit
  have hn_le : ∀ t ≤ 0, ‖θi t n‖ ≤ ρ₁ := by
    intro t ht
    refine le_of_tendsto (hcn t ht).norm ?_
    filter_upwards [hevS t ht] with j hj
    exact (hS j).le t hj
  have hn_pos : ∀ t ≤ 0, 0 < ‖θi t n‖ := by
    intro t ht
    have hM : 0 < ((ρ₁ ^ (k - 2))⁻¹ + C * (-t))⁻¹ := by
      have h1 : 0 ≤ C * (-t) := mul_nonneg hC.le (by linarith)
      have h2 : 0 < (ρ₁ ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos hρ₁ _)
      exact inv_pos.mpr (by linarith)
    have h2 : ((ρ₁ ^ (k - 2))⁻¹ + C * (-t))⁻¹ ≤ ‖θi t n‖ ^ (k - 2) := by
      refine ge_of_tendsto ((hcn t ht).norm.pow (k - 2)) ?_
      filter_upwards [hevS t ht] with j hj
      exact (hS j).low t hj
    rcases (norm_nonneg (θi t n)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (by omega)] at h2
      linarith
  have hS_mem : ∀ t ≤ 0, θi t ∈ S (insert n A) := by
    intro t ht
    have h1 : Tendsto (fun j => ‖ψ j t - proj (insert n A) (ψ j t)‖) atTop
        (𝓝 ‖θi t - proj (insert n A) (θi t)‖) :=
      ((hconv' t ht).sub (((proj (insert n A)).continuous.tendsto _).comp (hconv' t ht))).norm
    have h2 : Tendsto (fun j => 2 * ρ0 j) atTop (𝓝 0) := by simpa using hρ0.const_mul 2
    have h3 : ‖θi t - proj (insert n A) (θi t)‖ ≤ 0 := by
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [hevS t ht] with j hj
      exact (hS j).z t hj
    have h4 : θi t = proj (insert n A) (θi t) := sub_eq_zero.mp (norm_le_zero_iff.mp h3)
    rw [h4]
    exact proj_mem_S _ _
  have hu_lim : ∀ t ≤ 0, ‖‖θi t n‖⁻¹ • θi t n - u₀‖ ≤ r := by
    intro t ht
    have h1 : Tendsto (fun j => ‖ψ j t n‖⁻¹ • ψ j t n - u₀) atTop
        (𝓝 (‖θi t n‖⁻¹ • θi t n - u₀)) :=
      (((hcn t ht).norm.inv₀ (hn_pos t ht).ne').smul (hcn t ht)).sub_const u₀
    refine le_of_tendsto h1.norm ?_
    filter_upwards [hevS t ht] with j hj
    exact (hS j).u t hj
  have ha_lim : ∀ t ≤ 0, ‖proj A (θi t) - θ₀‖ ≤ rU := by
    intro t ht
    have h1 : Tendsto (fun j => proj A (ψ j t) - θ₀) atTop (𝓝 (proj A (θi t) - θ₀)) :=
      (((proj A).continuous.tendsto _).comp (hconv' t ht)).sub_const θ₀
    refine le_of_tendsto h1.norm ?_
    filter_upwards [hevS t ht] with j hj
    exact (hS j).a t hj
  -- `θi` satisfies the assumptions of `(⋆)` on `(-∞, 0]`
  have hθiB : BackwardNear F A n θ₀ u₀ ρU rU θi 0 := by
    refine ⟨fun t ht => ?_, fun t ht => ⟨hS_mem t ht, hn_pos t ht, (hn_le t ht).trans hρ₁ρU,
      (hu_lim t ht).trans hrrU, ha_lim t ht⟩⟩
    have hmt : MapsTo (Neg.neg : ℝ → ℝ) (Iic 0) (Ici 0) := fun s hs => by
      simp only [mem_Iic] at hs
      simp only [mem_Ici]
      linarith
    have h1 : HasDerivWithinAt β (-gf F (β (-t))) (Ici 0) (-t) :=
      hβ.sol (-t) (hall (-t) (by linarith))
    have h2 : HasDerivWithinAt (Neg.neg : ℝ → ℝ) (-1) (Iic 0) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    have h3 := h1.scomp t h2 hmt
    rw [neg_one_smul, neg_neg] at h3
    exact h3
  -- `(⋆)`: `θi` is a time translate of `γ`
  obtain ⟨s₁, hs₁, s₂, -, heq⟩ := huniq θi γ 0 T₁ hθiB hγB
  have htrans : ∀ t ≤ 0, θi t = γ (t + (s₂ - s₁)) := by
    intro t ht
    refine gf_unique hF (γ₁ := θi) (γ₂ := fun s => γ (s + (s₂ - s₁))) (a := min t s₁) (b := 0)
      (c := s₁) ⟨min_le_right _ _, hs₁⟩
      (fun s hs => (hθiB.1 s hs.2).mono Icc_subset_Iic_self)
      (fun s _ => ((hγsol (s + (s₂ - s₁))).comp_add_const s (s₂ - s₁)).hasDerivWithinAt)
      ?_ ⟨min_le_left _ _, ht⟩
    show θi s₁ = γ (s₁ + (s₂ - s₁))
    rw [heq, add_sub_cancel]
  -- the normalization fixes the translation
  have hxn : ‖x n‖ = ρ₁ := by
    have h1 : Tendsto (fun j => ‖ψ j 0 n‖) atTop (𝓝 ‖x n‖) :=
      (((PiLp.continuous_apply 2 (fun _ : ι => E) n).tendsto _).comp hx).norm
    have h2 : (fun j => ‖ψ j 0 n‖) = fun _ => ρ₁ := funext fun j => (hS j).end_eq
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hγc' : ‖γ (s₂ - s₁) n‖ = ρ₁ := by
    have h := htrans 0 le_rfl
    rw [zero_add, hθi0] at h
    rw [← h, hxn]
  have hle : ∀ s ≤ s₂ - s₁, ‖γ s n‖ ≤ ρ₁ := by
    intro s hs
    have h := htrans (s - (s₂ - s₁)) (by linarith)
    rw [sub_add_cancel] at h
    rw [← h]
    exact hn_le _ (by linarith)
  have hcc : s₂ - s₁ = c := by
    rcases lt_trichotomy (s₂ - s₁) c with h | h | h
    · exact absurd hγc' (hc _ h).ne
    · exact h
    · obtain ⟨t, ht, hlt⟩ := hstrict _ h
      exact absurd (hle t ht.le) (not_le.mpr hlt)
  have h := htrans 0 le_rfl
  rw [zero_add, hθi0, hcc] at h
  exact h

/-- Shadowing at the endpoint: `θ(t₁) → γ(c)` as `ρ₀ → 0`, uniformly in the trajectory
(by contradiction, with sequences and `limit_eq`). -/
private lemma shadow_end (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) {A : Finset ι} {n : ι}
    (hn : n ∉ A) {θ₀ : Θ ι E} {u₀ : E} {ρ₁ r ε₁ C rU ρU : ℝ}
    (hinv : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C)
    (hρ₁ : 0 < ρ₁) (hC : 0 < C) (hε₁ : ε₁ ≤ 1) (hrU : ρ₁ + C * ρ₁ ^ k ≤ rU)
    (h1 : 4 * ρ₁ + C * ρ₁ ^ k ≤ 1) (hrrU : r ≤ rU) (hρ₁ρU : ρ₁ ≤ ρU)
    (huniq : ∀ (θa θb : ℝ → Θ ι E) (t₁' t₂' : ℝ),
        BackwardNear F A n θ₀ u₀ ρU rU θa t₁' → BackwardNear F A n θ₀ u₀ ρU rU θb t₂' →
        ∃ s₁ ≤ t₁', ∃ s₂ ≤ t₂', θa s₁ = θb s₂)
    {γ : ℝ → Θ ι E} (hγsol : ∀ t, HasDerivAt γ (gf F (γ t)) t) {T₁ c : ℝ}
    (hγB : BackwardNear F A n θ₀ u₀ ρU rU γ T₁) (hc : ∀ t < c, ‖γ t n‖ < ρ₁)
    (hstrict : ∀ c' > c, ∃ t < c', ρ₁ < ‖γ t n‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
      EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) → ‖θ t₀ n‖ < δ →
      ∀ t₁ ∈ D, t₀ < t₁ → ‖θ t₁ n‖ = ρ₁ → (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) →
        ‖θ t₁ - γ c‖ < ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hseq : ∀ j : ℕ, ∃ θ : ℝ → Θ ι E, ∃ D : Set ℝ, ∃ t₀ t₁ : ℝ,
      IsMaxFwd (gf F) θ D ∧ t₀ ∈ D ∧ EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) ∧
      ‖θ t₀ n‖ < 1 / ((j : ℝ) + 1) ∧ t₁ ∈ D ∧ t₀ < t₁ ∧ ‖θ t₁ n‖ = ρ₁ ∧
      (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) ∧ ε ≤ ‖θ t₁ - γ c‖ := by
    intro j
    obtain ⟨θ, D, hmax, t₀, ht₀, hesc, hδ, t₁, ht₁D, hlt, hρ, hfirst, hbad⟩ :=
      hcon (1 / ((j : ℝ) + 1)) (by positivity)
    exact ⟨θ, D, t₀, t₁, hmax, ht₀, hesc, hδ, ht₁D, hlt, hρ, hfirst, hbad⟩
  choose θs Ds t₀s t₁s hmax ht₀ hesc hδ ht₁D hlt hρ hfirst hbad using hseq
  have hsh : ∀ j, Shifted F k A θ₀ n u₀ ρ₁ r C rU (fun s => θs j (t₁s j + s))
      (t₁s j - t₀s j) ‖θs j (t₀s j) n‖ ∧
      (‖θs j (t₀s j) n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁s j - t₀s j) :=
    fun j => shifted_of_data hn hinv hC hε₁ hrU h1 (hmax j) (ht₀ j) (hesc j) (ht₁D j)
      (hlt j) (hρ j) (hfirst j)
  have hρ0 : Tendsto (fun j => ‖θs j (t₀s j) n‖) atTop (𝓝 0) :=
    squeeze_zero (fun j => norm_nonneg _) (fun j => (hδ j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hL : Tendsto (fun j => t₁s j - t₀s j) atTop atTop := by
    have hlow : ∀ j : ℕ, ((j : ℝ) + (1 - (ρ₁ ^ (k - 2))⁻¹)) / C ≤ t₁s j - t₀s j := by
      intro j
      have hpos : 0 < ‖θs j (t₀s j) n‖ := (hesc j).1
      have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
      have hle1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have hpow : ‖θs j (t₀s j) n‖ ^ (k - 2) ≤ ‖θs j (t₀s j) n‖ :=
        pow_le_of_le_one (norm_nonneg _) ((hδ j).le.trans hle1) (by omega)
      have hinv1 : (j : ℝ) + 1 < (‖θs j (t₀s j) n‖ ^ (k - 2))⁻¹ := by
        have h2 : ‖θs j (t₀s j) n‖ ^ (k - 2) < 1 / ((j : ℝ) + 1) := lt_of_le_of_lt hpow (hδ j)
        have h3 := inv_strictAnti₀ (pow_pos hpos (k - 2)) h2
        rwa [one_div, inv_inv] at h3
      have h4 := (hsh j).2
      rw [div_le_iff₀' hC]
      linarith
    refine tendsto_atTop_mono hlow ?_
    exact Tendsto.atTop_div_const hC
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  -- extract a convergent subsequence of the endpoints
  have hbdd : ∀ j, θs j (t₁s j + 0) ∈ closedBall θ₀ 1 := by
    intro j
    rw [mem_closedBall, dist_eq_norm]
    exact (hsh j).1.near 0 ⟨by linarith [hlt j], le_rfl⟩
  obtain ⟨x, -, φ, hφ, hx⟩ := tendsto_subseq_of_bounded (x := fun j => θs j (t₁s j + 0))
    isBounded_closedBall hbdd
  have hxγ : x = γ c := limit_eq hF hk hρ₁ hC hrrU hρ₁ρU huniq hγsol hγB hc hstrict
    (ψ := fun j s => θs (φ j) (t₁s (φ j) + s)) (L := fun j => t₁s (φ j) - t₀s (φ j))
    (ρ0 := fun j => ‖θs (φ j) (t₀s (φ j)) n‖) (fun j => (hsh (φ j)).1)
    (hL.comp hφ.tendsto_atTop) (hρ0.comp hφ.tendsto_atTop) hx
  -- contradiction
  have h2 : Tendsto (fun j => ‖θs (φ j) (t₁s (φ j) + 0) - γ c‖) atTop (𝓝 0) := by
    rw [← hxγ]
    exact tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h3 : ε ≤ 0 := by
    refine ge_of_tendsto h2 (Eventually.of_forall fun j => ?_)
    simpa using hbad (φ j)
  linarith

/-- Shadowing on `[t₀, t₁]`: `sup_{[t₀, t₁]} dist(θ, γ((-∞, c])) → 0` as `ρ₀ → 0`. Below a
small `ρ'`, the trajectory is close to `θ*` (slaving), which is a limit point of `γ`; above
`ρ'`, it is within a bounded time `T` of `t₁`, and continuous dependence applies. -/
private lemma shadow_sup (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) {A : Finset ι} {n : ι}
    (hn : n ∉ A) {θ₀ : Θ ι E} {u₀ : E} {ρ₁ r ε₁ C : ℝ}
    (hinv : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C) (hρ₁ : 0 < ρ₁) (hC : 0 < C) (hε₁ : ε₁ ≤ 1)
    {γ : ℝ → Θ ι E} (hγsol : ∀ t, HasDerivAt γ (gf F (γ t)) t)
    (hγlim : Tendsto γ atBot (𝓝 θ₀)) {c : ℝ}
    (hend : ∀ ε > 0, ∃ δ > 0, ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D →
      ∀ t₀ ∈ D, EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) → ‖θ t₀ n‖ < δ →
      ∀ t₁ ∈ D, t₀ < t₁ → ‖θ t₁ n‖ = ρ₁ → (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) →
        ‖θ t₁ - γ c‖ < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
      EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) → ‖θ t₀ n‖ < δ →
      ∀ t₁ ∈ D, t₀ < t₁ → ‖θ t₁ n‖ = ρ₁ → (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) →
        ∀ t ∈ Icc t₀ t₁, ∃ s ≤ c, ‖θ t - γ s‖ < ε := by
  intro ε hε
  -- a point of `γ((-∞, c])` close to `θ₀`
  obtain ⟨S₀, hS₀⟩ := eventually_atBot.mp (hγlim.eventually (ball_mem_nhds θ₀ (half_pos hε)))
  have hs₀ : ‖γ (min S₀ c) - θ₀‖ < ε / 2 := by
    have h := hS₀ (min S₀ c) (min_le_left _ _)
    rwa [dist_eq_norm] at h
  -- below `ρ'`, the trajectory is `ε/2`-close to `θ₀`
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : ℝ, ρ' = min 1 (ε / (4 * (4 + C))) := ⟨_, rfl⟩
  have hρ' : 0 < ρ' := by rw [hρ'def]; exact lt_min one_pos (by positivity)
  have hρ'1 : ρ' ≤ 1 := by rw [hρ'def]; exact min_le_left _ _
  have hρ'ε : 4 * ρ' + C * ρ' ≤ ε / 4 := by
    have h := min_le_right 1 (ε / (4 * (4 + C)))
    rw [← hρ'def] at h
    have h4C : (0 : ℝ) < 4 + C := by linarith
    have h' : (4 + C) * ρ' ≤ (4 + C) * (ε / (4 * (4 + C))) :=
      mul_le_mul_of_nonneg_left h h4C.le
    have e : (4 + C) * (ε / (4 * (4 + C))) = ε / 4 := by field_simp
    linarith
  -- above `ρ'`, the trajectory is within time `T` of `t₁`
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = C * (ρ' ^ (k - 2))⁻¹ := ⟨_, rfl⟩
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  obtain ⟨δ₀, hδ₀, K, hK, hdep⟩ := gf_cont_dep hF (by linarith : c - T ≤ c)
    (fun t _ => (hγsol t).hasDerivWithinAt)
  obtain ⟨δ₁, hδ₁, hend'⟩ := hend (min δ₀ (ε / (2 * K))) (lt_min hδ₀ (by positivity))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (ρ₁ ^ (k - 2))⁻¹ + C * T := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  refine ⟨min (min δ₁ ρ') (min 1 M⁻¹), lt_min (lt_min hδ₁ hρ') (lt_min one_pos (inv_pos.mpr hM)),
    ?_⟩
  intro θ D hmax t₀ ht₀ hesc hδ t₁ ht₁D ht₁ hρt₁ hfirst t ht
  have hb := inv_bounds hinv hmax ht₀ hesc ht₁ hρt₁ hfirst
  have hρ0pos : 0 < ‖θ t₀ n‖ := hesc.1
  have hδ₁' : ‖θ t₀ n‖ < δ₁ := lt_of_lt_of_le hδ ((min_le_left _ _).trans (min_le_left _ _))
  have hρ'' : ‖θ t₀ n‖ < ρ' := lt_of_lt_of_le hδ ((min_le_left _ _).trans (min_le_right _ _))
  have h1' : ‖θ t₀ n‖ < 1 := lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_left _ _))
  have hM' : ‖θ t₀ n‖ < M⁻¹ := lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, htime, -, hz, -, ha⟩ := hb t ht
  by_cases hsmall : ‖θ t n‖ ≤ ρ'
  · -- close to `θ₀`
    refine ⟨min S₀ c, min_le_right _ _, ?_⟩
    have hz0 : ‖θ t₀ - proj (insert n A) (θ t₀)‖ ≤ ε₁ * ‖θ t₀ n‖ := hesc.2.2.2.1
    have hε₁ρ : ε₁ * ‖θ t₀ n‖ ≤ ‖θ t₀ n‖ := mul_le_of_le_one_left (norm_nonneg _) hε₁
    have hpow : ‖θ t n‖ ^ k ≤ ‖θ t n‖ :=
      pow_le_of_le_one (norm_nonneg _) (hsmall.trans hρ'1) (by omega)
    have hCpow : C * ‖θ t n‖ ^ k ≤ C * ρ' := mul_le_mul_of_nonneg_left (hpow.trans hsmall) hC.le
    have hnear : ‖θ t - θ₀‖ ≤ ε / 4 := by
      have := norm_sub_le_parts hn θ₀ (θ t)
      linarith
    calc ‖θ t - γ (min S₀ c)‖ = ‖(θ t - θ₀) - (γ (min S₀ c) - θ₀)‖ := by congr 1; abel
      _ ≤ ‖θ t - θ₀‖ + ‖γ (min S₀ c) - θ₀‖ := norm_sub_le _ _
      _ < ε := by linarith
  · -- in the last `T` units of time: continuous dependence
    push Not at hsmall
    have htT : t₁ - t ≤ T := by
      refine htime.trans ?_
      have : (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (ρ' ^ (k - 2))⁻¹ :=
        inv_anti₀ (pow_pos hρ' _) (pow_le_pow_left₀ hρ'.le hsmall.le _)
      rw [hTdef]
      exact mul_le_mul_of_nonneg_left this hC.le
    have hLT : T ≤ t₁ - t₀ := by
      have h0 := (hb t₀ ⟨le_rfl, ht₁.le⟩).2.2.1
      have hpow : ‖θ t₀ n‖ ^ (k - 2) ≤ ‖θ t₀ n‖ :=
        pow_le_of_le_one (norm_nonneg _) h1'.le (by omega)
      have h2 : M < (‖θ t₀ n‖ ^ (k - 2))⁻¹ := by
        have h3 : ‖θ t₀ n‖ ^ (k - 2) < M⁻¹ := lt_of_le_of_lt hpow hM'
        have h4 := inv_strictAnti₀ (pow_pos hρ0pos _) h3
        rwa [inv_inv] at h4
      have h5 : C * T < C * (t₁ - t₀) := by rw [hMdef] at h2; linarith
      exact (lt_of_mul_lt_mul_left h5 hC.le).le
    have hT₀D : t₁ - T ∈ D := hmax.Icc_subset ht₀ ht₁D ⟨by linarith, by linarith⟩
    have hsol : ∀ s ∈ Icc (c - T) c, HasDerivWithinAt (fun s => θ (s + (t₁ - c)))
        (gf F (θ (s + (t₁ - c)))) (Icc (c - T) c) s := by
      intro s hs
      have hmt : MapsTo (fun s : ℝ => s + (t₁ - c)) (Icc (c - T) c) (Icc (t₁ - T) t₁) :=
        fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h1 := hmax.hasDerivWithinAt_Icc hT₀D ht₁D (s + (t₁ - c)) (hmt hs)
      have h2 : HasDerivWithinAt (fun s : ℝ => s + (t₁ - c)) 1 (Icc (c - T) c) s :=
        ((hasDerivAt_id s).add_const (t₁ - c)).hasDerivWithinAt
      have h3 := HasDerivWithinAt.scomp (h := fun s : ℝ => s + (t₁ - c)) (x := s) h1 h2 hmt
      rw [one_smul] at h3
      exact h3
    have hend1 : ‖θ t₁ - γ c‖ < min δ₀ (ε / (2 * K)) :=
      hend' θ D hmax t₀ ht₀ hesc hδ₁' t₁ ht₁D ht₁ hρt₁ hfirst
    have hc_eq : θ (c + (t₁ - c)) = θ t₁ := by rw [add_sub_cancel]
    have key := hdep (fun s => θ (s + (t₁ - c))) hsol c ⟨by linarith, le_rfl⟩
      (by
        show ‖θ (c + (t₁ - c)) - γ c‖ ≤ δ₀
        rw [hc_eq]
        exact hend1.le.trans (min_le_left _ _))
      (t - (t₁ - c)) ⟨by linarith [htT], by linarith [ht.2]⟩
    simp only [sub_add_cancel, hc_eq] at key
    refine ⟨t - (t₁ - c), by linarith [ht.2], ?_⟩
    have hK' : K * ‖θ t₁ - γ c‖ < K * (ε / (2 * K)) :=
      mul_lt_mul_of_pos_left (hend1.trans_le (min_le_right _ _)) hK
    have e : K * (ε / (2 * K)) = ε / 2 := by field_simp
    linarith

/-- Normalization of the escape orbit (proof of (a)): for `t ≪ 0`, `γ` satisfies the assumptions
of `(⋆)` and of the invariance step, so `‖γ_n‖` reaches `ρ₁`, first at a time `c`. -/
private lemma normalize {A : Finset ι} {n : ι} (hn : n ∉ A) {θ₀ : Θ ι E}
    (hθ₀ : θ₀ ∈ S A) {u₀ : E} (hu₀ : ‖u₀‖ = 1) {γ : ℝ → Θ ι E}
    (hγ : IsEscapeOrbit F A θ₀ n u₀ γ) {ρ₁ r ε₁ C rU ρU : ℝ}
    (hinv : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C)
    (hslav : ∀ (θ : ℝ → Θ ι E) (t' : ℝ), BackwardNear F A n θ₀ u₀ ρU rU θ t' →
        ∀ t ≤ t', ‖proj A (θ t) - θ₀‖ ≤ ‖θ t n‖)
    (hρ₁ : 0 < ρ₁) (hr : 0 < r) (hε₁ : 0 < ε₁) (hρ₁ρU : ρ₁ ≤ ρU) (hrrU : r ≤ rU) :
    ∃ T₁ c : ℝ, BackwardNear F A n θ₀ u₀ ρU rU γ T₁ ∧ ‖γ c n‖ = ρ₁ ∧
      (∀ t < c, ‖γ t n‖ < ρ₁) ∧ ‖‖γ c n‖⁻¹ • γ c n - u₀‖ ≤ r ∧
      ‖proj A (γ c) - θ₀‖ ≤ ρ₁ + C * ρ₁ ^ k := by
  have hθ₀n : θ₀ n = 0 := hθ₀ n hn
  have h1 : ∀ᶠ t in atBot, ‖γ t - θ₀‖ < min ρ₁ r := by
    filter_upwards [hγ.tendsto.eventually (ball_mem_nhds θ₀ (lt_min hρ₁ hr))] with t ht
    rwa [dist_eq_norm] at ht
  have h2 : ∀ᶠ t in atBot, ‖‖γ t n‖⁻¹ • γ t n - u₀‖ < min r 1 := by
    filter_upwards [hγ.dir.eventually (ball_mem_nhds u₀ (lt_min hr one_pos))] with t ht
    rwa [dist_eq_norm] at ht
  obtain ⟨T₁, hT₁⟩ := eventually_atBot.mp (h1.and h2)
  have hpt : ∀ t ≤ T₁, 0 < ‖γ t n‖ ∧ ‖γ t n‖ < ρ₁ ∧ ‖‖γ t n‖⁻¹ • γ t n - u₀‖ ≤ r ∧
      ‖proj A (γ t) - θ₀‖ < r := by
    intro t ht
    obtain ⟨ha, hb⟩ := hT₁ t ht
    have hnle : ‖γ t n‖ ≤ ‖γ t - θ₀‖ := by
      have h := norm_apply_le (γ t - θ₀) n
      rwa [PiLp.sub_apply, hθ₀n, sub_zero] at h
    have hproj : ‖proj A (γ t) - θ₀‖ ≤ ‖γ t - θ₀‖ := by
      have e : proj A (γ t) - θ₀ = proj A (γ t - θ₀) := by
        rw [map_sub, proj_eq_self_of_mem_S hθ₀]
      rw [e]
      exact norm_zeroOut_le _ _
    have hmin1 := min_le_left ρ₁ r
    have hmin2 := min_le_right ρ₁ r
    have hmin3 := min_le_left r 1
    have hmin4 := min_le_right r 1
    refine ⟨?_, by linarith, by linarith, by linarith⟩
    rcases (norm_nonneg (γ t n)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : γ t n = 0 := norm_eq_zero.mp h.symm
      rw [h0, smul_zero, zero_sub, norm_neg, hu₀] at hb
      linarith
  have hγB : BackwardNear F A n θ₀ u₀ ρU rU γ T₁ := by
    refine ⟨fun t _ => (hγ.sol t).hasDerivWithinAt, fun t ht => ?_⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpt t ht
    exact ⟨hγ.mem t, p1, by linarith, p3.trans hrrU, by linarith⟩
  obtain ⟨p1, p2, p3, -⟩ := hpt T₁ le_rfl
  have hz : γ T₁ - proj (insert n A) (γ T₁) = 0 := by
    rw [proj_eq_self_of_mem_S (hγ.mem T₁), sub_self]
  have hesc : EscHyp A n θ₀ u₀ ρ₁ r ε₁ ((fun t => γ (T₁ + t)) 0) := by
    simp only [add_zero]
    refine ⟨p1, p2, p3, ?_, hslav γ T₁ hγB T₁ le_rfl⟩
    rw [hz, norm_zero]
    positivity
  have hmax : IsMaxFwd (gf F) (fun t => γ (T₁ + t)) (Ici 0) :=
    { zero_mem := mem_Ici.mpr le_rfl
      subset_Ici := subset_rfl
      ordConnected := ordConnected_Ici
      sol := fun t _ => ((hγ.sol (T₁ + t)).comp_const_add T₁ t).hasDerivWithinAt
      maximal := fun b _ _ _ => ⟨1, one_pos, Ico_subset_Ici_self⟩ }
  obtain ⟨t₁, -, ht₁, hρt₁, hfirst, hb⟩ := hinv _ _ hmax 0 (mem_Ici.mpr le_rfl) hesc
  obtain ⟨-, -, -, -, hu₁, ha₁⟩ := hb t₁ ⟨ht₁.le, le_rfl⟩
  beta_reduce at hρt₁ hfirst hu₁ ha₁
  refine ⟨T₁, T₁ + t₁, hγB, hρt₁, fun t ht => ?_, hu₁, ?_⟩
  · by_cases htT : t ≤ T₁
    · exact (hpt t htT).2.1
    · push Not at htT
      have h := hfirst (t - T₁) ⟨by linarith, by linarith⟩
      rwa [add_sub_cancel] at h
  · rw [hρt₁, add_zero] at ha₁
    linarith

/-- If `‖γ_n‖` has positive derivative at `c`, it exceeds `‖γ_n(c)‖` right after `c`. -/
private lemma strict_of_deriv {n : ι} {γ : ℝ → Θ ι E}
    (hγsol : ∀ t, HasDerivAt γ (gf F (γ t)) t) {c ρ₁ : ℝ} (hc : ‖γ c n‖ = ρ₁)
    (hpos : 0 < ⟪γ c n, (gf F (γ c)) n⟫) : ∀ c' > c, ∃ t < c', ρ₁ < ‖γ t n‖ := by
  intro c' hc'
  by_contra h
  push Not at h
  have hd : HasDerivAt (fun t => ‖γ t n‖ ^ 2) (2 * ⟪γ c n, (gf F (γ c)) n⟫) c := by
    have h1 : HasDerivAt (fun t => γ t n) ((gf F (γ c)) n) c :=
      (PiLp.proj 2 (fun _ : ι => E) n).hasFDerivAt.comp_hasDerivAt c (hγsol c)
    exact h1.norm_sq
  have hmax : IsLocalMax (fun t => ‖γ t n‖ ^ 2) c :=
    Filter.eventually_of_mem (Iio_mem_nhds hc') fun t ht => by
      have h2 := h t ht
      show ‖γ t n‖ ^ 2 ≤ ‖γ c n‖ ^ 2
      rw [hc]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Near `(ρ, u, θ) = (0, u*, θ*)`, the radial velocity `D = ⟨u, G⟩` is positive, since
`D(0, u*, θ*) = k U(u*) > 0` (Euler). Hence `⟨w_n, -∇_{w_n} F⟩ > 0` there. -/
private lemma exists_D_pos (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k) (n : ι)
    (θ₀ : Θ ι E) (u₀ : E) (hU : 0 < U F k n θ₀ u₀) :
    ∃ δ > 0, ∀ x : Θ ι E, ‖x - θ₀‖ < δ → 0 < ‖x n‖ → ‖x n‖ < δ →
      ‖‖x n‖⁻¹ • x n - u₀‖ < δ → 0 < ⟪x n, (gf F x) n⟫ := by
  obtain ⟨G, hG, hpol, hG0, -⟩ := exists_polar hF hk hH n
  have hfc : Continuous (fun q : ℝ × E × Θ ι E => ⟪q.2.1, G q⟫) :=
    (continuous_snd.fst).inner hG.continuous
  have hf0 : 0 < ⟪(((0 : ℝ), u₀, θ₀) : ℝ × E × Θ ι E).2.1, G (0, u₀, θ₀)⟫ := by
    show 0 < ⟪u₀, G (0, u₀, θ₀)⟫
    rw [hG0, euler]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    exact mul_pos hk0 hU
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hfc.continuousAt.eventually (lt_mem_nhds hf0))
  refine ⟨δ, hδ, fun x hx hpos hρ hu => ?_⟩
  have hq : dist ((‖x n‖, ‖x n‖⁻¹ • x n, x) : ℝ × E × Θ ι E) (0, u₀, θ₀) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm, dist_eq_norm, dist_eq_norm]
    simp only [sub_zero, norm_norm]
    exact max_lt hρ (max_lt hu hx)
  have h1 : 0 < ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ := hball hq
  have hxu : ‖x n‖ • (‖x n‖⁻¹ • x n) = x n := smul_inv_smul₀ hpos.ne' (x n)
  have h2 : (gf F x) n = ‖x n‖ ^ (k - 1) • G (‖x n‖, ‖x n‖⁻¹ • x n, x) := by
    have h := hpol ‖x n‖ (‖x n‖⁻¹ • x n) x
    rw [hxu, insertAt_self] at h
    rw [← h]
    simp [gf]
  rw [h2, real_inner_smul_right]
  rw [real_inner_smul_left] at h1
  have h3 : 0 < ⟪x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ :=
    (mul_pos_iff_of_pos_left (inv_pos.mpr hpos)).mp h1
  exact mul_pos (pow_pos hpos _) h3

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

/-- **Lemma 3 (Escape)**, part (b), for a given escape orbit `γ`. -/
theorem escape {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι} (hn : n ∉ A)
    {u₀ : E} (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀)
    {γ : ℝ → Θ ι E} (hγ : IsEscapeOrbit F A θ₀ n u₀ γ) :
    ∃ ρ₁ r ε₁ C c : ℝ, EscapeProp F k A θ₀ n u₀ γ ρ₁ r ε₁ C c := by
  obtain ⟨rI, hrI, hinvI⟩ := escape_invariance hF hk hH hmin hn hu hU
  obtain ⟨rU, hrU, ρU, hρU, huniq, hslav⟩ := escape_unique hF hk hH hmin hn hu hU
  obtain ⟨δD, hδD, hDpos⟩ := exists_D_pos hF hk hH n θ₀ u₀ hU
  -- the constants: first `r`, then `ρ₁` and `ε₁`
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (min rI rU) (δD / 2) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; exact lt_min (lt_min hrI hrU) (half_pos hδD)
  have hrI' : r ≤ rI := by rw [hr_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrrU : r ≤ rU := by rw [hr_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrδ : r ≤ δD / 2 := by rw [hr_def]; exact min_le_right _ _
  obtain ⟨ρI, hρI, εI, hεI, C, hC, hinv⟩ := hinvI r ⟨hr, hrI'⟩
  have h4C : (0 : ℝ) < 4 + C := by linarith
  have h8C : (0 : ℝ) < 8 + 2 * C := by linarith
  obtain ⟨ρ₁, hρ₁_def⟩ : ∃ ρ₁ : ℝ,
      ρ₁ = min (min ρI ρU) (min (rU / (4 + C)) (min (1 / (4 + C)) (δD / (8 + 2 * C)))) :=
    ⟨_, rfl⟩
  have hρ₁ : 0 < ρ₁ := by
    rw [hρ₁_def]
    exact lt_min (lt_min hρI hρU) (lt_min (div_pos hrU h4C)
      (lt_min (div_pos one_pos h4C) (div_pos hδD h8C)))
  have hρ₁I : ρ₁ ≤ ρI := by rw [hρ₁_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρ₁U : ρ₁ ≤ ρU := by rw [hρ₁_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρ₁rU : ρ₁ * (4 + C) ≤ rU := by
    have h : ρ₁ ≤ rU / (4 + C) := by
      rw [hρ₁_def]; exact (min_le_right _ _).trans (min_le_left _ _)
    exact (le_div_iff₀ h4C).mp h
  have hρ₁one : ρ₁ * (4 + C) ≤ 1 := by
    have h : ρ₁ ≤ 1 / (4 + C) := by
      rw [hρ₁_def]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (le_div_iff₀ h4C).mp h
  have hρ₁δ : ρ₁ * (8 + 2 * C) ≤ δD := by
    have h : ρ₁ ≤ δD / (8 + 2 * C) := by
      rw [hρ₁_def]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    exact (le_div_iff₀ h8C).mp h
  have hCρ : 0 ≤ C * ρ₁ := mul_nonneg hC.le hρ₁.le
  have hρ₁1 : ρ₁ ≤ 1 := by nlinarith
  have hpowk : ρ₁ ^ k ≤ ρ₁ := pow_le_of_le_one hρ₁.le hρ₁1 (by omega)
  have hCpow : C * ρ₁ ^ k ≤ C * ρ₁ := mul_le_mul_of_nonneg_left hpowk hC.le
  have hrU' : ρ₁ + C * ρ₁ ^ k ≤ rU := by nlinarith
  have h1' : 4 * ρ₁ + C * ρ₁ ^ k ≤ 1 := by nlinarith
  obtain ⟨ε₁, hε₁_def⟩ : ∃ ε₁ : ℝ, ε₁ = min εI 1 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁_def]; exact lt_min hεI one_pos
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁_def]; exact min_le_right _ _
  have hε₁I : ε₁ ≤ εI := by rw [hε₁_def]; exact min_le_left _ _
  have hinv' : InvProp F k A θ₀ n u₀ ρ₁ r ε₁ C := hinv ρ₁ ⟨hρ₁, hρ₁I⟩ ε₁ ⟨hε₁, hε₁I⟩
  -- normalization of `γ`
  obtain ⟨T₁, c, hγB, hγc, hγlt, hγu, hγa⟩ :=
    normalize hn hmin.mem hu.norm_eq hγ hinv' hslav hρ₁ hr hε₁ hρ₁U hrrU
  -- `‖γ_n‖` increases strictly at `c`
  have hγS : γ c - proj (insert n A) (γ c) = 0 := by
    rw [proj_eq_self_of_mem_S (hγ.mem c), sub_self]
  have hγnear : ‖γ c - θ₀‖ ≤ (ρ₁ + C * ρ₁ ^ k) + ρ₁ := by
    have h := norm_sub_le_parts hn θ₀ (γ c)
    rw [hγS, norm_zero, hγc] at h
    linarith
  have hpos : 0 < ⟪γ c n, (gf F (γ c)) n⟫ :=
    hDpos (γ c) (by nlinarith) (by rw [hγc]; exact hρ₁) (by rw [hγc]; nlinarith)
      (by linarith)
  have hstrict := strict_of_deriv hγ.sol hγc hpos
  -- shadowing
  have hend := shadow_end hF hk hn hinv' hρ₁ hC hε₁1 hrU' h1' hrrU hρ₁U huniq hγ.sol hγB hγlt
    hstrict
  have hsup := shadow_sup hF hk hn hinv' hρ₁ hC hε₁1 hγ.sol hγ.tendsto hend
  refine ⟨ρ₁, r, ε₁, C, c, hρ₁, hρ₁1, hr, hε₁, hε₁1, hC, hγc, hγlt, ?_, ?_⟩
  · -- invariance
    intro θ D hmax t₀ ht₀ hesc
    obtain ⟨t₁, ht₁D, ht₁, hρt₁, hfirst, hb⟩ := hinv' θ D hmax t₀ ht₀ hesc
    refine ⟨t₁, ht₁D, ht₁, hρt₁, hfirst, (hb t₀ ⟨le_rfl, ht₁.le⟩).2.1,
      fun t ht => ⟨(hb t ht).2.2.2.1, ?_⟩⟩
    obtain ⟨-, -, -, hz, -, ha⟩ := hb t ht
    have hle := norm_le_of_first hρt₁ hfirst t ht
    have hz0 := hesc.2.2.2.1
    have hρ0 := hesc.2.1
    have hε := mul_le_of_le_one_left (norm_nonneg (θ t₀ n)) hε₁1
    have hpow : ‖θ t n‖ ^ k ≤ ρ₁ ^ k := pow_le_pow_left₀ (norm_nonneg _) hle k
    have hCp : C * ‖θ t n‖ ^ k ≤ C * ρ₁ ^ k := mul_le_mul_of_nonneg_left hpow hC.le
    have := norm_sub_le_parts hn θ₀ (θ t)
    linarith
  · -- shadowing
    intro ε hε
    obtain ⟨δ₁, hδ₁, h1⟩ := hend ε hε
    obtain ⟨δ₂, hδ₂, h2⟩ := hsup ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
      fun θ D hmax t₀ ht₀ hesc hδ t₁ ht₁D ht₁ hρt₁ hfirst => ⟨?_, ?_⟩⟩
    · exact h1 θ D hmax t₀ ht₀ hesc (lt_of_lt_of_le hδ (min_le_left _ _)) t₁ ht₁D ht₁ hρt₁
        hfirst
    · exact h2 θ D hmax t₀ ht₀ hesc (lt_of_lt_of_le hδ (min_le_right _ _)) t₁ ht₁D ht₁ hρt₁
        hfirst

end S2S
