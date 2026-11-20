import SaddleToSaddle.GradFlow
import SaddleToSaddle.Process

/-!
# Facts about the saddle-to-saddle process

* Bookkeeping: monotonicity of the jump times and active sets, continuity of the dormant states,
  the dormant equation on each stage, the limit path.
* The Remark after Definition 1: `U^{(m)}_{n_{m+1}}(u_{m+1}) > 0` automatically in (ND2). Along a
  dormant trajectory `U(Ξ)/|Ξ|^k` is non-decreasing (Cauchy–Schwarz and Euler's identity), and
  `d|Ξ|²/ds = 2k U(Ξ)`; so if the limit `U(u_{m+1})` were `≤ 0`, `|Ξ|` would be non-increasing
  and could not blow up.
* The last assertions of Theorem A: `F(θ^{(m)}) > F(θ^{(m+1)})`, each `θ^{(m)}` is a critical
  point of `F`, and a saddle for `m < M`.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ} {ξ : Θ ι E} {M : ℕ} {S : ℝ}

/-- The Remark after Definition 1, for an abstract `k`-homogeneous utility `V`: if a solution of
`Ξ' = ∇V(Ξ)` blows up at `b` while its direction converges to `u`, then `V(u) > 0`. Indeed
`q = V(Ξ)/|Ξ|^k = V(Ξ/|Ξ|)` is non-decreasing near `b` (Euler and Cauchy–Schwarz) and tends to
`V(u)`; if `V(u) ≤ 0`, then `V(Ξ) ≤ 0` and `d|Ξ|²/ds = 2kV(Ξ) ≤ 0`, so `Ξ` stays bounded. -/
private lemma pos_of_blowup {V : E → ℝ} (hk : 3 ≤ k) (hVc : ContDiff ℝ ∞ V)
    (hsmul : ∀ (c : ℝ) (w : E), V (c • w) = c ^ k * V w)
    (heuler : ∀ w : E, ⟪w, gradient V w⟫ = k * V w)
    {Ξ : ℝ → E} {a b : ℝ} {u : E} (hab : a < b)
    (hΞ : ∀ σ ∈ Ico a b, HasDerivWithinAt Ξ (gradient V (Ξ σ)) (Ico a b) σ)
    (hblow : Tendsto (fun σ => ‖Ξ σ‖) (𝓝[<] b) atTop)
    (hdir : Tendsto (fun σ => ‖Ξ σ‖⁻¹ • Ξ σ) (𝓝[<] b) (𝓝 u)) : 0 < V u := by
  have hVd : Differentiable ℝ V := hVc.differentiable (by simp)
  have hΞd : ∀ σ ∈ Ioo a b, HasDerivAt Ξ (gradient V (Ξ σ)) σ := fun σ hσ =>
    (hΞ σ (Ioo_subset_Ico_self hσ)).hasDerivAt (Ico_mem_nhds hσ.1 hσ.2)
  have hev0 : ∀ᶠ σ in 𝓝[<] b, σ ∈ Ioo a b := Ioo_mem_nhdsLT hab
  have hev : ∀ᶠ σ in 𝓝[<] b, σ ∈ Ioo a b ∧ 1 ≤ ‖Ξ σ‖ :=
    hev0.and (hblow.eventually (eventually_ge_atTop 1))
  obtain ⟨c, hc, hcsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hcb : c < b := hc
  have hI : ∀ σ ∈ Ioo c b, σ ∈ Ioo a b ∧ 1 ≤ ‖Ξ σ‖ := fun σ hσ => hcsub hσ
  have hpos : ∀ σ ∈ Ioo c b, 0 < ‖Ξ σ‖ := fun σ hσ => by linarith [(hI σ hσ).2]
  -- the derivative of `‖Ξ‖`
  have hNd : ∀ σ ∈ Ioo c b,
      HasDerivAt (fun σ => ‖Ξ σ‖) (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖) σ := by
    intro σ hσ
    have h1 := (hΞd σ (hI σ hσ).1).norm_sq
    have h2 := h1.sqrt (by have := hpos σ hσ; positivity)
    simp only [Real.sqrt_sq_eq_abs, abs_norm] at h2
    convert h2 using 1
    rw [mul_div_mul_left _ _ two_ne_zero]
  -- the derivative of `V ∘ Ξ`
  have hVΞd : ∀ σ ∈ Ioo c b, HasDerivAt (fun σ => V (Ξ σ)) (‖gradient V (Ξ σ)‖ ^ 2) σ := by
    intro σ hσ
    have h1 : HasDerivAt (fun σ => V (Ξ σ)) (fderiv ℝ V (Ξ σ) (gradient V (Ξ σ))) σ :=
      (hVd (Ξ σ)).hasFDerivAt.comp_hasDerivAt σ (hΞd σ (hI σ hσ).1)
    rwa [← inner_gradient_E, real_inner_self_eq_norm_sq] at h1
  -- `q = V(Ξ)/‖Ξ‖^k` is non-decreasing
  have hqd : ∀ σ ∈ Ioo c b, HasDerivAt (fun σ => V (Ξ σ) / ‖Ξ σ‖ ^ k)
      ((‖gradient V (Ξ σ)‖ ^ 2 * ‖Ξ σ‖ ^ k - V (Ξ σ) * (k * ‖Ξ σ‖ ^ (k - 1) *
        (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖))) / (‖Ξ σ‖ ^ k) ^ 2) σ := fun σ hσ =>
    (hVΞd σ hσ).fun_div ((hNd σ hσ).fun_pow k) (pow_ne_zero _ (hpos σ hσ).ne')
  have hq'nn : ∀ σ ∈ Ioo c b, 0 ≤ (‖gradient V (Ξ σ)‖ ^ 2 * ‖Ξ σ‖ ^ k - V (Ξ σ) *
      (k * ‖Ξ σ‖ ^ (k - 1) * (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖))) / (‖Ξ σ‖ ^ k) ^ 2 := by
    intro σ hσ
    have hp := hpos σ hσ
    apply div_nonneg _ (by positivity)
    have hE : ⟪Ξ σ, gradient V (Ξ σ)⟫ = k * V (Ξ σ) := heuler _
    have hCS : ⟪Ξ σ, gradient V (Ξ σ)⟫ ^ 2 ≤ ‖Ξ σ‖ ^ 2 * ‖gradient V (Ξ σ)‖ ^ 2 := by
      have h := abs_real_inner_le_norm (Ξ σ) (gradient V (Ξ σ))
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hk1 : ‖Ξ σ‖ ^ k = ‖Ξ σ‖ ^ (k - 2) * ‖Ξ σ‖ ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have hk2 : ‖Ξ σ‖ ^ (k - 1) = ‖Ξ σ‖ ^ (k - 2) * ‖Ξ σ‖ := by
      rw [← pow_succ]
      congr 1
      omega
    have hdiv : ‖Ξ σ‖ * (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖) = ⟪Ξ σ, gradient V (Ξ σ)⟫ := by
      field_simp
    have heq : ‖gradient V (Ξ σ)‖ ^ 2 * ‖Ξ σ‖ ^ k - V (Ξ σ) * (k * ‖Ξ σ‖ ^ (k - 1) *
        (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖)) =
        ‖Ξ σ‖ ^ (k - 2) * (‖Ξ σ‖ ^ 2 * ‖gradient V (Ξ σ)‖ ^ 2 - ⟪Ξ σ, gradient V (Ξ σ)⟫ ^ 2) := by
      rw [hk1, hk2]
      calc _ = ‖gradient V (Ξ σ)‖ ^ 2 * (‖Ξ σ‖ ^ (k - 2) * ‖Ξ σ‖ ^ 2) - (k * V (Ξ σ)) *
            ‖Ξ σ‖ ^ (k - 2) * (‖Ξ σ‖ * (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖)) := by ring
        _ = _ := by rw [hdiv, ← hE]; ring
    rw [heq]
    exact mul_nonneg (pow_nonneg hp.le _) (by linarith)
  have hmono : MonotoneOn (fun σ => V (Ξ σ) / ‖Ξ σ‖ ^ k) (Ioo c b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo c b)
      (f' := fun σ => (‖gradient V (Ξ σ)‖ ^ 2 * ‖Ξ σ‖ ^ k - V (Ξ σ) *
        (k * ‖Ξ σ‖ ^ (k - 1) * (⟪Ξ σ, gradient V (Ξ σ)⟫ / ‖Ξ σ‖))) / (‖Ξ σ‖ ^ k) ^ 2)
      (fun σ hσ => (hqd σ hσ).continuousAt.continuousWithinAt) (fun σ hσ => ?_)
      (fun σ hσ => ?_)
    · rw [interior_Ioo] at hσ ⊢
      exact (hqd σ hσ).hasDerivWithinAt
    · rw [interior_Ioo] at hσ
      exact hq'nn σ hσ
  -- `q(σ) = V(Ξ/‖Ξ‖) → V(u)`
  have htend : Tendsto (fun σ => V (Ξ σ) / ‖Ξ σ‖ ^ k) (𝓝[<] b) (𝓝 (V u)) := by
    have h1 := (hVc.continuous.tendsto u).comp hdir
    refine Tendsto.congr (fun σ => ?_) h1
    simp only [Function.comp_apply]
    rw [hsmul, inv_pow, div_eq_inv_mul]
  have hqle : ∀ σ ∈ Ioo c b, V (Ξ σ) / ‖Ξ σ‖ ^ k ≤ V u := by
    intro σ hσ
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT hσ.2] with τ hτ
    exact hmono hσ ⟨hσ.1.trans hτ.1, hτ.2⟩ hτ.1.le
  by_contra hneg
  rw [not_lt] at hneg
  -- then `V(Ξ) ≤ 0`, so `‖Ξ‖²` is non-increasing near `b`
  have hVle : ∀ σ ∈ Ioo c b, V (Ξ σ) ≤ 0 := by
    intro σ hσ
    have h1 := (hqle σ hσ).trans hneg
    have hpk : 0 < ‖Ξ σ‖ ^ k := pow_pos (hpos σ hσ) k
    by_contra h2
    rw [not_le] at h2
    have := div_pos h2 hpk
    linarith
  have hanti : AntitoneOn (fun σ => ‖Ξ σ‖ ^ 2) (Ioo c b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo c b)
      (f' := fun σ => 2 * ⟪Ξ σ, gradient V (Ξ σ)⟫)
      (fun σ hσ => ((hΞd σ (hI σ hσ).1).norm_sq).continuousAt.continuousWithinAt)
      (fun σ hσ => ?_) (fun σ hσ => ?_)
    · rw [interior_Ioo] at hσ ⊢
      exact ((hΞd σ (hI σ hσ).1).norm_sq).hasDerivWithinAt
    · rw [interior_Ioo] at hσ
      have h1 := hVle σ hσ
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h2 : ⟪Ξ σ, gradient V (Ξ σ)⟫ ≤ 0 := by
        rw [heuler]
        exact mul_nonpos_of_nonneg_of_nonpos hk0 h1
      linarith
  -- this contradicts the blow-up
  have hσ₁ : (c + b) / 2 ∈ Ioo c b := ⟨by linarith, by linarith⟩
  have hev1 : ∀ᶠ σ in 𝓝[<] b, σ ∈ Ioo ((c + b) / 2) b := Ioo_mem_nhdsLT hσ₁.2
  have hev2 : ∀ᶠ σ in 𝓝[<] b, σ ∈ Ioo ((c + b) / 2) b ∧ ‖Ξ ((c + b) / 2)‖ + 1 ≤ ‖Ξ σ‖ :=
    hev1.and (hblow.eventually (eventually_ge_atTop _))
  obtain ⟨σ, hσ, hσbig⟩ := hev2.exists
  have h1 : ‖Ξ σ‖ ^ 2 ≤ ‖Ξ ((c + b) / 2)‖ ^ 2 :=
    hanti hσ₁ ⟨hσ₁.1.trans hσ.1, hσ.2⟩ hσ.1.le
  nlinarith [norm_nonneg (Ξ ((c + b) / 2))]

namespace Process

variable (P : Process F k ξ M S)

/-! ### Bookkeeping -/

theorem s_lt_s {i j : ℕ} (hij : i < j) (hj : j ≤ M) : P.s i < P.s j := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h (by omega)).trans (P.s_lt j (by omega))
    · subst h
      exact P.s_lt i (by omega)

theorem s_le_s {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) : P.s i ≤ P.s j := by
  rcases hij.lt_or_eq with h | h
  · exact (P.s_lt_s h hj).le
  · rw [h]

theorem s_nonneg {m : ℕ} (hm : m ≤ M) : 0 ≤ P.s m := by
  rw [← P.s_zero]
  exact P.s_le_s (Nat.zero_le m) hm

theorem s_lt_S_of_le {m : ℕ} (hm : m ≤ M) : P.s m < S :=
  (P.s_le_s hm le_rfl).trans_lt P.s_lt_S

theorem A_subset {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) : P.A i ⊆ P.A j := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.of_le_succ hij with h | h
    · rw [P.A_succ j (by omega)]
      exact (ih h (by omega)).trans (Finset.subset_insert _ _)
    · rw [h]

theorem n_mem_A {m j : ℕ} (hm : 1 ≤ m) (hmj : m ≤ j) (hj : j ≤ M) : P.n m ∈ P.A j := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  apply P.A_subset hmj hj
  rw [P.A_succ m' (by omega)]
  exact Finset.mem_insert_self _ _

theorem n_notMem_A {m j : ℕ} (hm : m ≤ M) (hjm : j < m) : P.n m ∉ P.A j := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  intro h
  exact P.n_notMem m' (by omega) (P.A_subset (by omega) (by omega) h)

theorem mem_A_iff {m : ℕ} (hm : m ≤ M) (i : ι) : i ∈ P.A m ↔ ∃ j ∈ Finset.Icc 1 m, P.n j = i := by
  induction m with
  | zero => simp [P.A_zero]
  | succ m ih =>
    rw [P.A_succ m (by omega), Finset.mem_insert, ih (by omega)]
    constructor
    · rintro (h | ⟨j, hj, hji⟩)
      · exact ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, h.symm⟩
      · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        exact ⟨j, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, hji⟩
    · rintro ⟨j, hj, hji⟩
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      rcases Nat.of_le_succ hj2 with h | h
      · exact Or.inr ⟨j, Finset.mem_Icc.mpr ⟨hj1, h⟩, hji⟩
      · subst h
        exact Or.inl hji.symm

/-- The dormant equation of stage `m`, for a neuron dormant at stage `m`, on `[s_m, σ₁]` with
`σ₁ < s_{m+1}` (or `σ₁ ≤ S'` at the last stage). -/
theorem dormant_on {m : ℕ} (hm : m ≤ M) {i : ι} (hi : i ∉ P.A m) {σ₁ : ℝ}
    (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ ≤ P.S')) :
    ∀ σ ∈ Icc (P.s m) σ₁,
      HasDerivWithinAt (P.Ξ i) (gradient (U F k i (P.θs m)) (P.Ξ i σ)) (Icc (P.s m) σ₁) σ := by
  intro σ hσ
  rcases hm.lt_or_eq with hlt | heq
  · have hσ₁' := hσ₁.1 hlt
    by_cases hi' : i ∈ P.A (m + 1)
    · rw [P.A_succ m hlt, Finset.mem_insert] at hi'
      rcases hi' with rfl | hi'
      · exact (P.dormant_act m hlt σ ⟨hσ.1, hσ.2.trans_lt hσ₁'⟩).mono
          (fun x hx => ⟨hx.1, hx.2.trans_lt hσ₁'⟩)
      · exact absurd hi' hi
    · exact (P.dormant m hlt i hi' σ ⟨hσ.1, hσ.2.trans hσ₁'.le⟩).mono
        (Icc_subset_Icc_right hσ₁'.le)
  · subst heq
    exact (P.dormant_last i hi σ ⟨hσ.1, hσ.2.trans (hσ₁.2 rfl)⟩).mono
      (Icc_subset_Icc_right (hσ₁.2 rfl))

/-- Continuity of the dormant states up to the jump time of the current stage. -/
private lemma Ξ_continuousOn_aux : ∀ m ≤ M, ∀ i ∉ P.A m, ContinuousOn (P.Ξ i) (Icc 0 (P.s m)) := by
  intro m
  induction m with
  | zero =>
    intro _ i _
    rw [P.s_zero, Icc_self]
    exact continuousOn_singleton _ _
  | succ m ih =>
    intro hm i hi
    have hi' : i ∉ P.A m := fun h => hi (P.A_subset (Nat.le_succ m) hm h)
    have h1 := ih (by omega) i hi'
    have h2 : ContinuousOn (P.Ξ i) (Icc (P.s m) (P.s (m + 1))) := fun σ hσ =>
      (P.dormant m (by omega) i hi σ hσ).continuousWithinAt
    rw [← Icc_union_Icc_eq_Icc (P.s_nonneg (by omega)) (P.s_lt m (by omega)).le]
    exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc

/-- A neuron dormant at stage `m` has a continuous dormant state up to any `σ₁ < s_{m+1}`
(or `σ₁ ≤ S'` at the last stage). -/
theorem Ξ_continuousOn {m : ℕ} (hm : m ≤ M) {i : ι} (hi : i ∉ P.A m) {σ₁ : ℝ}
    (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ ≤ P.S')) :
    ContinuousOn (P.Ξ i) (Icc 0 σ₁) := by
  have h1 := P.Ξ_continuousOn_aux m hm i hi
  have h2 : ContinuousOn (P.Ξ i) (Icc (P.s m) σ₁) := fun σ hσ =>
    (P.dormant_on hm hi hσ₁ σ hσ).continuousWithinAt
  exact (h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).mono Icc_subset_Icc_union_Icc

theorem limitPath_eq {m : ℕ} (hm : m ≤ M) {σ : ℝ} (h₁ : P.s m ≤ σ)
    (h₂ : m < M → σ < P.s (m + 1)) : P.limitPath σ = P.θs m := by
  have hfilt : (Finset.Icc 1 M).filter (fun j => P.s j ≤ σ) = Finset.Icc 1 m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hjM⟩, hjs⟩
      refine ⟨hj1, ?_⟩
      by_contra hjm
      rw [not_le] at hjm
      have hmM : m < M := lt_of_lt_of_le hjm hjM
      have := P.s_le_s (show m + 1 ≤ j by omega) hjM
      linarith [h₂ hmM]
    · rintro ⟨hj1, hjm⟩
      exact ⟨⟨hj1, hjm.trans hm⟩, (P.s_le_s hjm hm).trans h₁⟩
  unfold limitPath
  rw [hfilt, Nat.card_Icc, Nat.add_sub_cancel]

/-! ### The Remark, and the last assertions of Theorem A -/

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

/-- The Remark after Definition 1: `U^{(m)}_{n_{m+1}}(u_{m+1}) > 0`. -/
theorem U_pos {m : ℕ} (hm : m < M) : 0 < U F k (P.n (m + 1)) (P.θs m) (P.u (m + 1)) :=
  pos_of_blowup hk (U_contDiff _ _) (U_smul _ _) (euler _ _) (P.s_lt m hm) (P.dormant_act m hm)
    (P.blowup m hm) (P.dir m hm)

/-- `F(θ^{(m+1)}) < F(θ^{(m)})`, because `F` decreases strictly along `γ_{m+1}`. -/
theorem F_lt {m : ℕ} (hm : m < M) : F (P.θs (m + 1)) < F (P.θs m) := by
  have hesc := P.escape m hm
  have hderiv : ∀ t, HasDerivAt (fun t => F (P.γ (m + 1) t))
      (-‖gradient F (P.γ (m + 1) t)‖ ^ 2) t := fun t =>
    hasDerivWithinAt_univ.mp (hasDerivWithinAt_F_comp hF (hesc.sol t).hasDerivWithinAt)
  have hanti : Antitone (fun t => F (P.γ (m + 1) t)) :=
    antitone_of_hasDerivAt_nonpos hderiv (fun t => by
      have := sq_nonneg ‖gradient F (P.γ (m + 1) t)‖
      simp only [Pi.zero_apply]
      linarith)
  have hbot : Tendsto (fun t => F (P.γ (m + 1) t)) atBot (𝓝 (F (P.θs m))) :=
    (hF.continuous.tendsto _).comp hesc.tendsto
  have htop : Tendsto (fun t => F (P.γ (m + 1) t)) atTop (𝓝 (F (P.θs (m + 1)))) :=
    (hF.continuous.tendsto _).comp (P.escape_lim m hm)
  have hle1 : ∀ t, F (P.γ (m + 1) t) ≤ F (P.θs m) := hanti.ge_of_tendsto hbot
  have hle2 : ∀ t, F (P.θs (m + 1)) ≤ F (P.γ (m + 1) t) := hanti.le_of_tendsto htop
  by_contra hcon
  rw [not_lt] at hcon
  have hconst : ∀ t, F (P.γ (m + 1) t) = F (P.θs m) := fun t =>
    le_antisymm (hle1 t) (hcon.trans (hle2 t))
  have hgrad : ∀ t, gradient F (P.γ (m + 1) t) = 0 := by
    intro t
    have h1 : HasDerivAt (fun t => F (P.γ (m + 1) t)) 0 t := by
      have : (fun t => F (P.γ (m + 1) t)) = fun _ => F (P.θs m) := funext hconst
      rw [this]
      exact hasDerivAt_const _ _
    have h2 := (hderiv t).unique h1
    have h3 : ‖gradient F (P.γ (m + 1) t)‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  have hd : ∀ t, HasDerivAt (P.γ (m + 1)) 0 t := fun t => by
    have := hesc.sol t
    rwa [gf, hgrad t, neg_zero] at this
  have hγconst : ∀ t, P.γ (m + 1) t = P.γ (m + 1) 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hγ0 : P.γ (m + 1) 0 = P.θs m := by
    have : Tendsto (P.γ (m + 1)) atBot (𝓝 (P.γ (m + 1) 0)) := by
      have : P.γ (m + 1) = fun _ => P.γ (m + 1) 0 := funext hγconst
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique this hesc.tendsto
  have hn0 : P.θs m (P.n (m + 1)) = 0 := (P.isMin m hm.le).mem _ (P.n_notMem m hm)
  have hdir := hesc.dir
  have hzero : (fun t => ‖P.γ (m + 1) t (P.n (m + 1))‖⁻¹ • P.γ (m + 1) t (P.n (m + 1))) =
      fun _ => 0 := by
    funext t
    rw [hγconst t, hγ0, hn0, smul_zero]
  rw [hzero] at hdir
  have hu0 : P.u (m + 1) = 0 := tendsto_nhds_unique hdir tendsto_const_nhds
  have hnorm := (P.u_max m hm).norm_eq
  rw [hu0, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- Each `θ^{(m)}` is a critical point of `F`. -/
theorem gradient_θs_eq_zero {m : ℕ} (hm : m ≤ M) : gradient F (P.θs m) = 0 :=
  gradient_eq_zero_of_isNondegMin hF hk hH (P.isMin m hm)

/-- `θ^{(m)}` is a saddle point of `F` for `m < M`. -/
theorem isSaddle {m : ℕ} (hm : m < M) : IsSaddle F (P.θs m) := by
  refine ⟨P.gradient_θs_eq_zero hF hk hH hm.le, fun hmin => ?_⟩
  obtain ⟨Ψ, hΨc, hΨ, hΨ0⟩ := F_insertAt_expansion hF hk hH (P.n (m + 1))
  have hθn : P.θs m (P.n (m + 1)) = 0 := (P.isMin m hm.le).mem _ (P.n_notMem m hm)
  have hzero : zeroAt (P.n (m + 1)) (P.θs m) = P.θs m := by
    rw [← insertAt_zero, ← hθn, insertAt_self]
  have hUpos := P.U_pos hF hk hH hm
  have hg0 : insertAt (P.θs m) (P.n (m + 1)) ((0 : ℝ) • P.u (m + 1)) = P.θs m := by
    rw [zero_smul, insertAt_zero, hzero]
  have hgc : Continuous (fun ρ : ℝ => insertAt (P.θs m) (P.n (m + 1)) (ρ • P.u (m + 1))) := by
    simp only [insertAt]
    exact continuous_const.add
      ((singleL (P.n (m + 1))).continuous.comp (continuous_id.smul continuous_const))
  have h1 : ∀ᶠ ρ in 𝓝 (0 : ℝ),
      F (P.θs m) ≤ F (insertAt (P.θs m) (P.n (m + 1)) (ρ • P.u (m + 1))) := by
    have := hgc.tendsto 0
    rw [hg0] at this
    exact this.eventually hmin
  have h2 : ∀ᶠ ρ in 𝓝 (0 : ℝ), Ψ (ρ, P.u (m + 1), P.θs m) < 0 := by
    have hc : Continuous (fun ρ : ℝ => Ψ (ρ, P.u (m + 1), P.θs m)) :=
      hΨc.comp (continuous_id.prodMk continuous_const)
    have : Ψ (0, P.u (m + 1), P.θs m) < 0 := by
      rw [hΨ0]
      linarith
    exact hc.continuousAt.eventually (gt_mem_nhds this)
  obtain ⟨ρ, ⟨hρ1, hρ2⟩, hρpos⟩ :=
    (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hexp := hΨ ρ (P.u (m + 1)) (P.θs m)
  rw [hzero] at hexp
  have hρk : 0 < ρ ^ k := pow_pos hρpos k
  have : ρ ^ k * Ψ (ρ, P.u (m + 1), P.θs m) < 0 := mul_neg_of_pos_of_neg hρk hρ2
  linarith

end Process

end S2S
