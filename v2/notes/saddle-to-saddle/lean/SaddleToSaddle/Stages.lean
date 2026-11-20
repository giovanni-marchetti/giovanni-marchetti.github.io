import SaddleToSaddle.Plateau
import SaddleToSaddle.Escape
import SaddleToSaddle.ProcessFacts

/-!
# Proof of Theorem A: the induction on stages

We prove by induction on `m ≤ M` the claim `(C_m)` of the note: there are times `τ_m^α` with
`α^{k-2} τ_m^α → s_m`, `|π_{A_m} θ^α(τ_m^α) - θ^{(m)}| ≤ r₀`, and `α⁻¹ w_n^α(τ_m^α) → Ξ_n(s_m)`
for `n ∉ A_m`. We strengthen the last condition to uniform convergence on `[0, τ_m^α]` in the
time `s = α^{k-2} t`, which gives part (ii) of the theorem directly.

* `claim_zero`: `(C_0)` holds with `τ_0^α = 0`.
* `stage_plateau`: the plateau step (Lemma 2 from `(C_m)`).
* `stage_jump`: the jump step (Lemma 3 from `(C_m)` and the plateau step), which gives the jump
  times `t_{m+1}^α`, the convergence to the escape orbit, the shadowing estimate used for the
  Hausdorff convergence, and `(C_{m+1})`.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ} {ξ : Θ ι E} {M : ℕ} {S : ℝ}

/-- The inductive claim `(C_m)`, strengthened by the uniform convergence of the rescaled dormant
weights up to time `τ_m^α`. -/
structure Claim (P : Process F k ξ M S) (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ) (m : ℕ) (r₀ : ℝ)
    (τ : ℝ → ℝ) : Prop where
  mem : ∀ᶠ α in 𝓝[>] 0, τ α ∈ D α
  near : ∀ᶠ α in 𝓝[>] 0, ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ ≤ r₀
  time : Tendsto (fun α => α ^ (k - 2) * τ α) (𝓝[>] 0) (𝓝 (P.s m))
  dormant : ∀ i ∉ P.A m, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc 0 (τ α),
    ‖α⁻¹ • θ α t i - P.Ξ i (α ^ (k - 2) * t)‖ ≤ ε

/-! ### Auxiliary lemmas -/

/-- A slightly larger horizon on which the dormant states of stage `m` are still defined. -/
private lemma exists_gt_horizon (P : Process F k ξ M S) {m : ℕ} {σ₁ : ℝ}
    (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ < P.S')) :
    ∃ σ₂, σ₁ < σ₂ ∧ (m < M → σ₂ < P.s (m + 1)) ∧ (m = M → σ₂ ≤ P.S') := by
  by_cases h : m < M
  · have h1 := hσ₁.1 h
    exact ⟨(σ₁ + P.s (m + 1)) / 2, by linarith, fun _ => by linarith,
      fun h' => absurd h' (ne_of_lt h)⟩
  · by_cases h' : m = M
    · have h1 := hσ₁.2 h'
      exact ⟨(σ₁ + P.S') / 2, by linarith, fun h'' => absurd h'' h, fun _ => by linarith⟩
    · exact ⟨σ₁ + 1, by linarith, fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩

/-- The dormant states of stage `m` are bounded up to `σ₁`. -/
private lemma exists_bound_Ξ (P : Process F k ξ M S) {m : ℕ} (hm : m ≤ M) {σ₁ : ℝ}
    (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ ≤ P.S')) :
    ∃ R, 0 ≤ R ∧ ∀ i ∉ P.A m, ∀ σ ∈ Icc 0 σ₁, ‖P.Ξ i σ‖ ≤ R := by
  have hcont : ContinuousOn (fun σ => ∑ i ∈ (P.A m)ᶜ, ‖P.Ξ i σ‖) (Icc 0 σ₁) :=
    continuousOn_finsetSum _ fun i hi =>
      (P.Ξ_continuousOn hm (Finset.mem_compl.mp hi) hσ₁).norm
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max R 0, le_max_right _ _, fun i hi σ hσ => ?_⟩
  have h1 : ‖P.Ξ i σ‖ ≤ ∑ j ∈ (P.A m)ᶜ, ‖P.Ξ j σ‖ :=
    Finset.single_le_sum (f := fun j => ‖P.Ξ j σ‖) (fun j _ => norm_nonneg _)
      (Finset.mem_compl.mpr hi)
  have h2 := hR σ hσ
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h2
  exact h1.trans (h2.trans (le_max_left _ _))

/-- Uniform continuity on a compact interval, in `ε`-`η` form. -/
private lemma uc_Icc {f : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) {ε : ℝ}
    (hε : 0 < ε) : ∃ η > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| < η → ‖f x - f y‖ < ε := by
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨η, hη, fun x hx y hy hxy => ?_⟩
  have := h x hx y hy (by rwa [Real.dist_eq])
  rwa [dist_eq_norm] at this

/-- If `f α` is uniformly close to `g (s α)` and `s α → σ`, with `g` continuous at `σ` within
a set containing `s α`, then `f α → g σ`. -/
private lemma tendsto_of_close {f : ℝ → E} {g : ℝ → E} {s : ℝ → ℝ} {σ : ℝ} {I : Set ℝ}
    (hg : ContinuousWithinAt g I σ)
    (hfg : ∀ ε > 0, ∀ᶠ α in 𝓝[>] (0 : ℝ), ‖f α - g (s α)‖ ≤ ε)
    (hs : Tendsto s (𝓝[>] 0) (𝓝 σ)) (hsI : ∀ᶠ α in 𝓝[>] (0 : ℝ), s α ∈ I) :
    Tendsto f (𝓝[>] 0) (𝓝 (g σ)) := by
  have h1 : Tendsto (fun α => g (s α)) (𝓝[>] 0) (𝓝 (g σ)) :=
    hg.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hs, hsI⟩)
  rw [Metric.tendsto_nhds] at h1 ⊢
  intro ε hε
  filter_upwards [h1 (ε / 2) (by positivity), hfg (ε / 2) (by positivity)] with α h1α h2α
  rw [dist_eq_norm] at h1α ⊢
  calc ‖f α - g σ‖ ≤ ‖f α - g (s α)‖ + ‖g (s α) - g σ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-- Comparison of directions: `|x/|x| - y/|y|| ≤ 2|x - y|/|y|`. -/
private lemma norm_dir_sub_le {x y : E} (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, inv_zero, zero_smul, zero_sub, norm_neg, zero_sub]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy'.ne', le_div_iff₀ hy']
    linarith
  · have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have heq : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = ‖y‖⁻¹ • (((‖y‖ * ‖x‖⁻¹ - 1) • x) + (x - y)) := by
      rw [sub_smul, one_smul, smul_add, smul_sub, smul_sub, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ hy'.ne', one_mul]
      abel
    rw [heq, norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    gcongr
    calc ‖(‖y‖ * ‖x‖⁻¹ - 1) • x + (x - y)‖ ≤ ‖(‖y‖ * ‖x‖⁻¹ - 1) • x‖ + ‖x - y‖ :=
          norm_add_le _ _
      _ = |‖y‖ - ‖x‖| + ‖x - y‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          congr 1
          rw [← abs_norm x, ← abs_mul, abs_norm, sub_mul, mul_assoc, inv_mul_cancel₀ hx'.ne',
            mul_one, one_mul]
      _ ≤ ‖y - x‖ + ‖x - y‖ := by gcongr; exact abs_norm_sub_norm_le y x
      _ = 2 * ‖x - y‖ := by rw [norm_sub_rev]; ring

/-- `exp(-μ X α^{2-k}) r₀ + K α^k ≤ α` for small `α > 0`. -/
private lemma exp_bound_eventually {μ X r₀ K : ℝ} (hk : 3 ≤ k) (hμ : 0 < μ) (hX : 0 < X) :
    ∀ᶠ α in 𝓝[>] (0 : ℝ), Real.exp (-μ * ((α ^ (k - 2))⁻¹ * X)) * r₀ + K * α ^ k ≤ α := by
  set L : ℝ := 2 * |r₀| / (μ * X) ^ 2 + |K| + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ 2 * |r₀| / (μ * X) ^ 2 := by positivity
    linarith [abs_nonneg K]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < L⁻¹ by positivity)] with α hα
  obtain ⟨hα0, hαL⟩ := hα
  have hα1 : α ≤ 1 := by
    have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
    linarith
  have hpk : α ^ (k - 2) ≤ α := by
    calc α ^ (k - 2) ≤ α ^ 1 := pow_le_pow_of_le_one hα0.le hα1 (by omega)
      _ = α := pow_one α
  have hpk0 : 0 < α ^ (k - 2) := pow_pos hα0 _
  set y : ℝ := μ * ((α ^ (k - 2))⁻¹ * X) with hy
  have hy1 : μ * X / α ≤ y := by
    have : α⁻¹ ≤ (α ^ (k - 2))⁻¹ := inv_anti₀ hpk0 hpk
    have hμX : 0 < μ * X := mul_pos hμ hX
    calc μ * X / α = μ * X * α⁻¹ := div_eq_mul_inv _ _
      _ ≤ μ * X * (α ^ (k - 2))⁻¹ := by gcongr
      _ = y := by rw [hy]; ring
  have hy0 : 0 < μ * X / α := by positivity
  have hexp : Real.exp (-y) ≤ 2 * α ^ 2 / (μ * X) ^ 2 := by
    have h1 : y ^ 2 / 2 ≤ Real.exp y := by
      have := Real.quadratic_le_exp_of_nonneg (hy0.le.trans hy1)
      nlinarith [hy0.le.trans hy1]
    have h2 : (μ * X / α) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    rw [Real.exp_neg]
    have hy2 : 0 < y ^ 2 / 2 := by
      have : 0 < y := hy0.trans_le hy1
      positivity
    calc (Real.exp y)⁻¹ ≤ (y ^ 2 / 2)⁻¹ := inv_anti₀ hy2 h1
      _ ≤ ((μ * X / α) ^ 2 / 2)⁻¹ := by
          apply inv_anti₀ (by positivity); linarith
      _ = 2 * α ^ 2 / (μ * X) ^ 2 := by
          field_simp
  have hneg : -μ * ((α ^ (k - 2))⁻¹ * X) = -y := by rw [hy]; ring
  rw [hneg]
  have hT1 : Real.exp (-y) * r₀ ≤ 2 * |r₀| / (μ * X) ^ 2 * α ^ 2 := by
    calc Real.exp (-y) * r₀ ≤ Real.exp (-y) * |r₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
      _ ≤ 2 * α ^ 2 / (μ * X) ^ 2 * |r₀| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ = 2 * |r₀| / (μ * X) ^ 2 * α ^ 2 := by ring
  have hT2 : K * α ^ k ≤ |K| * α ^ 2 := by
    calc K * α ^ k ≤ |K| * α ^ k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |K| * α ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_of_le_one hα0.le hα1 (by omega)
  have hα2 : α ^ 2 * L ≤ α := by
    have : α * L < 1 := by
      calc α * L < L⁻¹ * L := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith
  have : 2 * |r₀| / (μ * X) ^ 2 * α ^ 2 + |K| * α ^ 2 ≤ α ^ 2 * L := by
    rw [hL]; nlinarith [sq_nonneg α]
  linarith

/-- The norm of a parameter is at most `N` times the largest norm of its components. -/
private lemma norm_le_card_mul {x : Θ ι E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, ‖x i‖ ≤ b) :
    ‖x‖ ≤ Fintype.card ι * b := by
  have h1 : ‖x‖ ^ 2 ≤ (Fintype.card ι * b) ^ 2 := by
    rw [norm_sq_eq_sum]
    have hN : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
      · simp [h0]
      · have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h0
        nlinarith
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, b ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = Fintype.card ι * b ^ 2 := by simp
      _ ≤ (Fintype.card ι * b) ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right hN (sq_nonneg b)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

private lemma hasDerivWithinAt_apply {f : ℝ → Θ ι E} {f' : Θ ι E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) (i : ι) : HasDerivWithinAt (fun t => f t i) (f' i) s t :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) i).hasFDerivAt.comp_hasDerivWithinAt t h

private lemma hasDerivAt_apply {f : ℝ → Θ ι E} {f' : Θ ι E} {t : ℝ}
    (h : HasDerivAt f f' t) (i : ι) : HasDerivAt (fun t => f t i) (f' i) t :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) i).hasFDerivAt.comp_hasDerivAt t h

/-- `α^{2-k} → ∞` as `α → 0⁺`. -/
private lemma tendsto_inv_pow_atTop (hk : 3 ≤ k) :
    Tendsto (fun α : ℝ => (α ^ (k - 2))⁻¹) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun α : ℝ => α ^ (k - 2)) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun α : ℝ => α ^ (k - 2)) (𝓝 0) (𝓝 (0 ^ (k - 2))) :=
        (continuous_pow _).tendsto 0
      rw [zero_pow (by omega)] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact pow_pos (show (0 : ℝ) < α from hα) _
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- `α^{k-2} (τ + α^{2-k} X) = α^{k-2} τ + X`. -/
private lemma rescale_shift {α τ X : ℝ} (hα : 0 < α) :
    α ^ (k - 2) * (τ + (α ^ (k - 2))⁻¹ * X) = α ^ (k - 2) * τ + X := by
  have : α ^ (k - 2) ≠ 0 := pow_ne_zero _ hα.ne'
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ this, one_mul]

private lemma tendsto_shift {τ : ℝ → ℝ} {s₀ X : ℝ}
    (h : Tendsto (fun α => α ^ (k - 2) * τ α) (𝓝[>] 0) (𝓝 s₀)) :
    Tendsto (fun α => α ^ (k - 2) * (τ α + (α ^ (k - 2))⁻¹ * X)) (𝓝[>] 0) (𝓝 (s₀ + X)) := by
  refine (h.add_const X).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (rescale_shift hα).symm

/-- The slow time `σ = s + α^{k-2}(t - τ)` of a time `t ∈ [τ, τ + α^{2-k}(σ₁ - s)]`. -/
private lemma slow_time {α τ t s σ₁ : ℝ} (hα : 0 < α)
    (ht : t ∈ Icc τ (τ + (α ^ (k - 2))⁻¹ * (σ₁ - s))) :
    s + α ^ (k - 2) * (t - τ) ∈ Icc s σ₁ ∧
      τ + (α ^ (k - 2))⁻¹ * (s + α ^ (k - 2) * (t - τ) - s) = t := by
  have hc : 0 < α ^ (k - 2) := pow_pos hα _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : 0 ≤ α ^ (k - 2) * (t - τ) := mul_nonneg hc.le (by linarith [ht.1])
    linarith
  · have h2 : t - τ ≤ (α ^ (k - 2))⁻¹ * (σ₁ - s) := by linarith [ht.2]
    have := mul_le_mul_of_nonneg_left h2 hc.le
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
    linarith
  · rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, add_sub_cancel]

/-- `s - δ → s⁻` as `δ → 0⁺`. -/
private lemma tendsto_sub_nhdsLT (a : ℝ) : Tendsto (fun δ : ℝ => a - δ) (𝓝[>] 0) (𝓝[<] a) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have : Tendsto (fun δ : ℝ => a - δ) (𝓝 0) (𝓝 (a - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact sub_lt_self a hδ

/-- `W (R - 1)^{2-k} → 0` as `R → ∞`. -/
private lemma tendsto_inv_pow_sub_one (hk : 3 ≤ k) {R : ℝ → ℝ} {l : Filter ℝ}
    (hR : Tendsto R l atTop) (W : ℝ) :
    Tendsto (fun δ => W * ((R δ - 1) ^ (k - 2))⁻¹) l (𝓝 0) := by
  have h1 : Tendsto (fun δ => R δ - 1) l atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1) hR
  have h2 : Tendsto (fun δ => (R δ - 1) ^ (k - 2)) l atTop :=
    (tendsto_pow_atTop (by omega)).comp h1
  have h4 := h2.inv_tendsto_atTop.const_mul W
  rw [mul_zero] at h4
  exact h4

/-- `a α^j → 0` as `α → 0⁺`, for `j ≥ 1`. -/
private lemma tendsto_mul_pow_zero (a : ℝ) {j : ℕ} (hj : j ≠ 0) :
    Tendsto (fun α : ℝ => a * α ^ j) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun α : ℝ => a * α ^ j) (𝓝 0) (𝓝 (a * 0 ^ j)) :=
    (continuous_const.mul (continuous_pow j)).tendsto 0
  rw [zero_pow hj, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The duration of the jump, in the slow time: if `ρ ≥ α(R - 1)` and `x ≤ C ρ^{2-k}`, then
`α^{k-2} x ≤ C (R - 1)^{2-k}`. -/
private lemma rescaled_time_le {α ρ R C x : ℝ} (hα : 0 < α) (hR : 1 < R)
    (hρ : α * (R - 1) ≤ ρ) (hC : 0 ≤ C) (hx : x ≤ C * (ρ ^ (k - 2))⁻¹) :
    α ^ (k - 2) * x ≤ C * ((R - 1) ^ (k - 2))⁻¹ := by
  have hR1 : 0 < R - 1 := by linarith
  have h1 : 0 < α * (R - 1) := mul_pos hα hR1
  have h2 : (α * (R - 1)) ^ (k - 2) ≤ ρ ^ (k - 2) := pow_le_pow_left₀ h1.le hρ _
  have h3 : (ρ ^ (k - 2))⁻¹ ≤ ((α * (R - 1)) ^ (k - 2))⁻¹ := inv_anti₀ (pow_pos h1 _) h2
  have hαk : α ^ (k - 2) ≠ 0 := pow_ne_zero _ hα.ne'
  have hRk : (R - 1) ^ (k - 2) ≠ 0 := pow_ne_zero _ hR1.ne'
  calc α ^ (k - 2) * x ≤ α ^ (k - 2) * (C * (ρ ^ (k - 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg hα.le _)
    _ ≤ α ^ (k - 2) * (C * ((α * (R - 1)) ^ (k - 2))⁻¹) := by gcongr
    _ = C * ((R - 1) ^ (k - 2))⁻¹ := by
        rw [mul_pow, mul_inv]; field_simp

/-- A component with `|ẇ| ≤ C_g |w|^{k-1}` and `|w| ≤ η` moves by at most `C_g η^{k-1}` per unit
time. -/
private lemma move_le {θ' : ℝ → Θ ι E} {D' : Set ℝ} (hmax : IsMaxFwd (gf F) θ' D') {a b : ℝ}
    (ha : a ∈ D') (hb : b ∈ D') {i : ι} {Cg Rb η : ℝ}
    (hCg : ∀ x : Θ ι E, ‖x‖ ≤ Rb → ‖(gradient F x) i‖ ≤ Cg * ‖x i‖ ^ (k - 1)) (hCg0 : 0 ≤ Cg)
    (hbd : ∀ t ∈ Icc a b, ‖θ' t‖ ≤ Rb ∧ ‖θ' t i‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖θ' t i - θ' a i‖ ≤ Cg * η ^ (k - 1) * (t - a) := by
  have hder := hmax.hasDerivWithinAt_Icc ha hb
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => θ' t i)
    (f' := fun t => (gf F (θ' t)) i) (fun t ht => hasDerivWithinAt_apply (hder t ht) i) ?_
  intro t ht
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  obtain ⟨h1, h2⟩ := hbd t ht'
  calc ‖(gf F (θ' t)) i‖ = ‖(gradient F (θ' t)) i‖ := by simp [gf]
    _ ≤ Cg * ‖θ' t i‖ ^ (k - 1) := hCg _ h1
    _ ≤ Cg * η ^ (k - 1) := by gcongr

/-- A component with `|ẇ| ≤ C_g |w|^{k-1}` at most doubles on a short time interval. -/
private lemma comp_le_two (hk : 3 ≤ k) {θ' : ℝ → Θ ι E} {D' : Set ℝ}
    (hmax : IsMaxFwd (gf F) θ' D') {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hD : Icc a b ⊆ D')
    {i : ι} {Cg Rb η : ℝ}
    (hCg : ∀ x : Θ ι E, ‖x‖ ≤ Rb → ‖(gradient F x) i‖ ≤ Cg * ‖x i‖ ^ (k - 1)) (hCg0 : 0 ≤ Cg)
    (hη : 0 ≤ η) (hRb : ∀ t ∈ Icc a b, ‖θ' t‖ ≤ Rb) (hia : ‖θ' a i‖ ≤ η)
    (hT : ((k : ℝ) - 2) * Cg * (b - a) * η ^ (k - 2) < 1 - (2 : ℝ)⁻¹ ^ (k - 2)) :
    ∀ t ∈ Icc a b, ‖θ' t i‖ ≤ 2 * η := by
  have hcont : ContinuousOn (fun t => θ' t i) (Icc a b) :=
    (PiLp.continuous_apply 2 (fun _ : ι => E) i).comp_continuousOn (hmax.continuousOn.mono hD)
  refine norm_le_two_mul_of_deriv_le_pow (f := fun t => θ' t i)
    (f' := fun t => (gf F (θ' t)) i) hk hCg0 hη hab hcont ?_ ?_ hia hT
  · intro t ht
    have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
    exact (hasDerivAt_apply (hmax.hasDerivAt (hD ht') (ha0.trans_le ht.1)) i).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
    calc ‖(gf F (θ' t)) i‖ = ‖(gradient F (θ' t)) i‖ := by simp [gf]
      _ ≤ Cg * ‖θ' t i‖ ^ (k - 1) := hCg _ (hRb t ht')

private lemma eventually_Ioo {b : ℝ} (hb : 0 < b) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 b :=
  Ioo_mem_nhdsGT hb

/-- The first time after `τ α` at which `|w_n| ≥ ρ₁`. -/
private def jumpTime (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ) (τ : ℝ → ℝ) (n : ι) (ρ₁ α : ℝ) : ℝ :=
  sInf {t | t ∈ D α ∧ τ α ≤ t ∧ ρ₁ ≤ ‖θ α t n‖}

/-- The outcome of the jump analysis for given `δ` and `α`: `t₀ = τ + α^{2-k}(s_{m+1} - δ - s_m)`,
`t₁` the jump time, `R = |Ξ_{n_{m+1}}(s_{m+1} - δ)|`. -/
private structure JumpGood (P : Process F k ξ M S) (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ) (m : ℕ)
    (ρ₁ r ε₁ C B₀ t₀ t₁ R α : ℝ) : Prop where
  pos : 0 < α
  le_one : α ≤ 1
  t₀_mem : t₀ ∈ D α
  hyp : EscHyp (P.A m) (P.n (m + 1)) (P.θs m) (P.u (m + 1)) ρ₁ r ε₁ (θ α t₀)
  lower : α * (R - 1) ≤ ‖θ α t₀ (P.n (m + 1))‖
  upper : ‖θ α t₀ (P.n (m + 1))‖ ≤ α * (R + 1)
  z₀ : ‖θ α t₀ - proj (P.A (m + 1)) (θ α t₀)‖ ≤ α * B₀
  t₁_mem : t₁ ∈ D α
  lt : t₀ < t₁
  at_t₁ : ‖θ α t₁ (P.n (m + 1))‖ = ρ₁
  before : ∀ t ∈ Ico t₀ t₁, ‖θ α t (P.n (m + 1))‖ < ρ₁
  time : t₁ - t₀ ≤ C * (‖θ α t₀ (P.n (m + 1))‖ ^ (k - 2))⁻¹
  inv : ∀ t ∈ Icc t₀ t₁, ‖θ α t - proj (P.A (m + 1)) (θ α t)‖ ≤
    2 * ‖θ α t₀ - proj (P.A (m + 1)) (θ α t₀)‖ ∧ ‖θ α t - P.θs m‖ ≤ 1

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
  (P : Process F k ξ M S) (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ)
  (hθ : ∀ α > 0, IsMaxFwd (gf F) (θ α) (D α) ∧ θ α 0 = α • ξ)
include hF hk hH hθ

/-- `(C_0)` holds with `τ_0^α = 0`. -/
theorem claim_zero {r₀ : ℝ} (hr₀ : 0 < r₀) : Claim P θ D 0 r₀ (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with α hα
    exact (hθ α hα).1.zero_mem
  · refine Filter.Eventually.of_forall fun α => ?_
    have : proj (P.A 0) (θ α 0) = 0 := by
      rw [P.A_zero]; ext m; simp
    rw [this, P.θs_zero, sub_zero, norm_zero]
    exact hr₀.le
  · simp only [mul_zero, P.s_zero]
    exact tendsto_const_nhds
  · intro i _ ε hε
    filter_upwards [self_mem_nhdsWithin] with α hα t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    have hα0 : α ≠ 0 := ne_of_gt hα
    rw [(hθ α hα).2, mul_zero, P.Ξ_zero, PiLp.smul_apply, inv_smul_smul₀ hα0, sub_self,
      norm_zero]
    exact hε.le

/-- The plateau step: from `(C_m)`, Lemma 2 on `[s_m, σ₁]` gives the existence of `θ^α` up to
`τ_m^α + α^{2-k}(σ₁ - s_m)`, the uniform convergence of the rescaled dormant weights up to that
time, the exponential relaxation of the active coordinates, and `w_n^α = O(α)` for `n ∉ A_m`. -/
theorem stage_plateau {m : ℕ} (hm : m ≤ M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {σ₁ : ℝ} (hσ : P.s m < σ₁) (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ < P.S')) :
    (∀ᶠ α in 𝓝[>] 0, Icc 0 (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)) ⊆ D α) ∧
    (∀ i ∉ P.A m, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0,
      ∀ t ∈ Icc 0 (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
        ‖α⁻¹ • θ α t i - P.Ξ i (α ^ (k - 2) * t)‖ ≤ ε) ∧
    (∃ K, ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
      ‖proj (P.A m) (θ α t) - P.θs m‖ ≤
        Real.exp (-μ * (t - τ α)) * ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ + K * α ^ k) ∧
    (∃ R, ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
      ∀ i ∉ P.A m, ‖θ α t i‖ ≤ α * R) := by
  obtain ⟨hr₀, hμ, hP⟩ := hpl
  have hσ₁' : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ ≤ P.S') :=
    ⟨hσ₁.1, fun h => (hσ₁.2 h).le⟩
  obtain ⟨σ₂, hσ₁₂, hσ₂⟩ := exists_gt_horizon P hσ₁
  have hsm : 0 ≤ P.s m := P.s_nonneg hm
  obtain ⟨α₁, δ₁, K, hα₁, hδ₁, hK, hmain⟩ :=
    hP (P.s m) σ₁ P.Ξ hσ (fun i hi => P.dormant_on hm hi hσ₁')
  obtain ⟨RΞ, hRΞ0, hRΞ⟩ := exists_bound_Ξ P hm hσ₁'
  have hτ0 : ∀ᶠ α in 𝓝[>] 0, 0 ≤ τ α := by
    filter_upwards [hC.mem, self_mem_nhdsWithin] with α h hα
    exact (hθ α hα).1.nonneg h
  -- convergence of the rescaled dormant weights at `τ`
  have hconv : ∀ i ∉ P.A m,
      Tendsto (fun α => α⁻¹ • θ α (τ α) i) (𝓝[>] 0) (𝓝 (P.Ξ i (P.s m))) := by
    intro i hi
    refine tendsto_of_close ((P.Ξ_continuousOn hm hi hσ₂).continuousWithinAt
      ⟨hsm, by linarith⟩) ?_ hC.time ?_
    · intro ε hε
      filter_upwards [hC.dormant i hi ε hε, hτ0] with α h1 h2
      exact h1 (τ α) ⟨h2, le_rfl⟩
    · filter_upwards [hτ0, self_mem_nhdsWithin,
        hC.time.eventually_lt_const (show P.s m < σ₂ by linarith)] with α h1 h2 h3
      exact ⟨mul_nonneg (pow_nonneg (le_of_lt h2) _) h1, h3.le⟩
  have hinit : ∀ δ₀ > 0, ∀ᶠ α in 𝓝[>] 0,
      ∀ i ∉ P.A m, ‖α⁻¹ • θ α (τ α) i - P.Ξ i (P.s m)‖ ≤ δ₀ := by
    intro δ₀ hδ₀
    have : ∀ i, ∀ᶠ α in 𝓝[>] (0 : ℝ),
        i ∉ P.A m → ‖α⁻¹ • θ α (τ α) i - P.Ξ i (P.s m)‖ ≤ δ₀ := by
      intro i
      by_cases hi : i ∈ P.A m
      · exact Filter.Eventually.of_forall fun α h => absurd hi h
      · filter_upwards [(Metric.tendsto_nhds.mp (hconv i hi)) δ₀ hδ₀] with α hα _
        rw [← dist_eq_norm]; exact hα.le
    exact Filter.eventually_all.mpr this
  -- the conclusions of Lemma 2, for a given `δ₀ ∈ (0, δ₁]`
  have hev : ∀ δ₀ ∈ Ioc 0 δ₁, ∀ᶠ α in 𝓝[>] 0, 0 < α ∧ α ≤ 1 ∧ τ α ∈ D α ∧
      Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)) ⊆ D α ∧
      (∀ σ ∈ Icc (P.s m) σ₁, ∀ i ∉ P.A m,
        ‖α⁻¹ • θ α (τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m)) i - P.Ξ i σ‖ ≤ K * (δ₀ + α)) ∧
      (∀ t ∈ Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
        ‖proj (P.A m) (θ α t) - P.θs m‖ ≤
          Real.exp (-μ * (t - τ α)) * ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ + K * α ^ k) := by
    intro δ₀ hδ₀
    filter_upwards [Ioo_mem_nhdsGT (lt_min hα₁ one_pos), hC.mem, hC.near, hinit δ₀ hδ₀.1]
      with α hα hmem hnear hini
    have hα0 : 0 < α := hα.1
    have hαα₁ : α ≤ α₁ := (hα.2.trans_le (min_le_left _ _)).le
    have hα1 : α ≤ 1 := (hα.2.trans_le (min_le_right _ _)).le
    exact ⟨hα0, hα1, hmem, hmain α ⟨hα0, hαα₁⟩ (θ α) (D α) (hθ α hα0).1 (τ α) hmem δ₀
      ⟨hδ₀.1.le, hδ₀.2⟩ hnear hini⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- existence
    filter_upwards [hev δ₁ ⟨hδ₁, le_rfl⟩] with α hα
    obtain ⟨hα0, -, hmem, hD, -, -⟩ := hα
    intro t ht
    by_cases htτ : t ≤ τ α
    · exact (hθ α hα0).1.Icc_zero_subset hmem ⟨ht.1, htτ⟩
    · exact hD ⟨(not_le.mp htτ).le, ht.2⟩
  · -- dormant weights
    intro i hi ε hε
    obtain ⟨η, hη, huc⟩ := uc_Icc (P.Ξ_continuousOn hm hi hσ₂) (show 0 < ε / 2 by positivity)
    set δ₀ := min δ₁ (ε / (4 * K)) with hδ₀
    have hδ₀pos : 0 < δ₀ := lt_min hδ₁ (by positivity)
    have hτclose : ∀ᶠ α in 𝓝[>] 0, |α ^ (k - 2) * τ α - P.s m| < min η (σ₂ - σ₁) := by
      have := Metric.tendsto_nhds.mp hC.time (min η (σ₂ - σ₁)) (lt_min hη (by linarith))
      filter_upwards [this] with α hα
      rwa [Real.dist_eq] at hα
    filter_upwards [hev δ₀ ⟨hδ₀pos, min_le_left _ _⟩, hC.dormant i hi ε hε, hτclose,
      Ioo_mem_nhdsGT (show (0 : ℝ) < ε / (4 * K) by positivity)] with α hα hdorm hcl hαs
    obtain ⟨hα0, -, -, -, hW, -⟩ := hα
    intro t ht
    by_cases htτ : t ≤ τ α
    · exact hdorm t ⟨ht.1, htτ⟩
    · have ht' : t ∈ Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)) :=
        ⟨(not_le.mp htτ).le, ht.2⟩
      obtain ⟨hσmem, hσt⟩ := slow_time hα0 ht'
      set σ := P.s m + α ^ (k - 2) * (t - τ α) with hσdef
      have h1 := hW σ hσmem i hi
      rw [hσt] at h1
      have hKb : K * (δ₀ + α) ≤ ε / 2 := by
        have h2 : δ₀ ≤ ε / (4 * K) := min_le_right _ _
        have h3 : α ≤ ε / (4 * K) := hαs.2.le
        calc K * (δ₀ + α) ≤ K * (ε / (4 * K) + ε / (4 * K)) := by gcongr
          _ = ε / 2 := by field_simp; ring
      have hct : α ^ (k - 2) * t = α ^ (k - 2) * τ α + (σ - P.s m) := by
        rw [hσdef]; ring
      have hσ0 : σ ∈ Icc 0 σ₂ := ⟨hsm.trans hσmem.1, hσmem.2.trans hσ₁₂.le⟩
      have hct0 : α ^ (k - 2) * t ∈ Icc 0 σ₂ := by
        refine ⟨mul_nonneg (pow_nonneg hα0.le _) ht.1, ?_⟩
        have := (abs_lt.mp (lt_of_lt_of_le hcl (min_le_right _ _))).2
        rw [hct]; linarith [hσmem.2]
      have h4 : ‖P.Ξ i σ - P.Ξ i (α ^ (k - 2) * t)‖ < ε / 2 := by
        apply huc σ hσ0 _ hct0
        rw [hct]
        have : σ - (α ^ (k - 2) * τ α + (σ - P.s m)) = -(α ^ (k - 2) * τ α - P.s m) := by ring
        rw [this, abs_neg]
        exact lt_of_lt_of_le hcl (min_le_left _ _)
      calc ‖α⁻¹ • θ α t i - P.Ξ i (α ^ (k - 2) * t)‖
          ≤ ‖α⁻¹ • θ α t i - P.Ξ i σ‖ + ‖P.Ξ i σ - P.Ξ i (α ^ (k - 2) * t)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε := by linarith
  · -- active coordinates
    refine ⟨K, ?_⟩
    filter_upwards [hev δ₁ ⟨hδ₁, le_rfl⟩] with α hα
    exact hα.2.2.2.2.2
  · -- inactive weights are `O(α)`
    refine ⟨RΞ + K * (δ₁ + 1), ?_⟩
    filter_upwards [hev δ₁ ⟨hδ₁, le_rfl⟩] with α hα
    obtain ⟨hα0, hα1, -, -, hW, -⟩ := hα
    intro t ht i hi
    obtain ⟨hσmem, hσt⟩ := slow_time hα0 ht
    have h1 := hW _ hσmem i hi
    rw [hσt] at h1
    have h2 : ‖P.Ξ i (P.s m + α ^ (k - 2) * (t - τ α))‖ ≤ RΞ :=
      hRΞ i hi _ ⟨hsm.trans hσmem.1, hσmem.2⟩
    have h3 : ‖α⁻¹ • θ α t i‖ ≤ RΞ + K * (δ₁ + 1) := by
      calc ‖α⁻¹ • θ α t i‖
          = ‖(α⁻¹ • θ α t i - P.Ξ i (P.s m + α ^ (k - 2) * (t - τ α))) +
              P.Ξ i (P.s m + α ^ (k - 2) * (t - τ α))‖ := by rw [sub_add_cancel]
        _ ≤ ‖α⁻¹ • θ α t i - P.Ξ i (P.s m + α ^ (k - 2) * (t - τ α))‖ +
            ‖P.Ξ i (P.s m + α ^ (k - 2) * (t - τ α))‖ := norm_add_le _ _
        _ ≤ K * (δ₁ + α) + RΞ := add_le_add h1 h2
        _ ≤ RΞ + K * (δ₁ + 1) := by nlinarith
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hα0.le)] at h3
    calc ‖θ α t i‖ = α * (α⁻¹ * ‖θ α t i‖) := by field_simp
      _ ≤ α * (RΞ + K * (δ₁ + 1)) := mul_le_mul_of_nonneg_left h3 hα0.le

/-- Local uniform convergence around times `t₁ α → ∞` at which `θ α (t₁ α) → γ c`, for a
reference trajectory `γ` defined for all times. -/
private lemma local_conv {t₁ : ℝ → ℝ} {γ : ℝ → Θ ι E} {c s' : ℝ}
    (hγ : ∀ t, HasDerivAt γ (gf F (γ t)) t) (hD : ∀ᶠ α in 𝓝[>] 0, t₁ α ∈ D α)
    (htime : Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 s')) (hs' : 0 < s')
    (hpt : Tendsto (fun α => θ α (t₁ α)) (𝓝[>] 0) (𝓝 (γ c))) :
    ∀ T > 0, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, Icc (t₁ α - T) (t₁ α + T) ⊆ D α ∧
      ∀ s ∈ Icc (-T) T, ‖θ α (t₁ α + s) - γ (s + c)‖ < ε := by
  intro T hT ε hε
  have hinf : Tendsto t₁ (𝓝[>] 0) atTop := by
    refine ((tendsto_inv_pow_atTop hk).atTop_mul_pos hs' htime).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    have : α ^ (k - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hα)
    field_simp
  obtain ⟨δa, hδa, Ka, hKa, hfwd⟩ := gf_cont_dep_maxFwd hF (show c ≤ c + T by linarith)
    (fun t _ => (hγ t).hasDerivWithinAt)
  obtain ⟨δb, hδb, Kb, hKb, hcd⟩ := gf_cont_dep hF (γ := fun s => γ (s + c))
    (show -T ≤ T by linarith) (fun t _ => ((hγ (t + c)).comp_add_const t c).hasDerivWithinAt)
  have hclose := Metric.tendsto_nhds.mp hpt (min (min δa δb) (ε / (2 * Kb))) (by positivity)
  filter_upwards [hD, hinf.eventually_gt_atTop T, hclose, self_mem_nhdsWithin]
    with α hD₁ hT₁ hcl hα
  have hmax := (hθ α hα).1
  rw [dist_eq_norm] at hcl
  have hcl1 : ‖θ α (t₁ α) - γ c‖ ≤ δa :=
    hcl.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcl2 : ‖θ α (t₁ α) - γ c‖ ≤ δb :=
    hcl.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcl3 : ‖θ α (t₁ α) - γ c‖ ≤ ε / (2 * Kb) := hcl.le.trans (min_le_right _ _)
  have hfw := (hfwd (θ α) (D α) hmax (t₁ α) hD₁ hcl1).1
  have hDsub : Icc (t₁ α - T) (t₁ α + T) ⊆ D α := by
    intro t ht
    by_cases htt : t ≤ t₁ α
    · exact hmax.Icc_zero_subset hD₁ ⟨by linarith [ht.1], htt⟩
    · exact hfw ⟨(not_le.mp htt).le, by linarith [ht.2]⟩
  refine ⟨hDsub, ?_⟩
  have hder : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => θ α (t₁ α + s))
      (gf F ((fun s => θ α (t₁ α + s)) s)) (Icc (-T) T) s := by
    intro s hs
    have hmem : t₁ α + s ∈ D α := hDsub ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hpos : 0 < t₁ α + s := by linarith [hs.1]
    exact ((hmax.hasDerivAt hmem hpos).comp_const_add (t₁ α) s).hasDerivWithinAt
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
  have hcl0 : ‖(fun s => θ α (t₁ α + s)) 0 - (fun s => γ (s + c)) 0‖ ≤ δb := by
    simpa using hcl2
  intro s hs
  have h1 := hcd (fun s => θ α (t₁ α + s)) hder 0 h0 hcl0 s hs
  simp only [add_zero, zero_add] at h1
  calc ‖θ α (t₁ α + s) - γ (s + c)‖ ≤ Kb * ‖θ α (t₁ α) - γ c‖ := h1
    _ ≤ Kb * (ε / (2 * Kb)) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The core of the jump step. For small `δ`, and then small `α`, the assumptions of Lemma 3(b)
hold at `t₀ = τ + α^{2-k}(s_{m+1} - δ - s_m)`, and the jump time `t₁` (which does not depend on
`δ`) is the time given by Lemma 3(b). -/
private lemma jump_core {m : ℕ} (hm : m < M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {ρ₁ r ε₁ C c : ℝ}
    (hesc : EscapeProp F k (P.A m) (P.θs m) (P.n (m + 1)) (P.u (m + 1)) (P.γ (m + 1))
      ρ₁ r ε₁ C c) :
    ∃ B₀, 0 ≤ B₀ ∧ ∀ᶠ δ in 𝓝[>] 0, 2 ≤ ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ ∧
      δ < P.s (m + 1) - P.s m ∧ ∀ᶠ α in 𝓝[>] 0,
      JumpGood P θ D m ρ₁ r ε₁ C B₀ (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m))
        (jumpTime θ D τ (P.n (m + 1)) ρ₁ α) ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ α := by
  obtain ⟨hρ₁, -, hr, hε₁, -, -, -, -, hinv, -⟩ := hesc
  have hμ : 0 < μ := hpl.2.1
  have hmM : m + 1 ≤ M := hm
  have hA' : P.A (m + 1) = insert (P.n (m + 1)) (P.A m) := P.A_succ m hm
  have hn : P.n (m + 1) ∉ P.A m := P.n_notMem m hm
  have hsm : 0 ≤ P.s m := P.s_nonneg hm.le
  have hss : P.s m < P.s (m + 1) := P.s_lt m hm
  have hσ' : (m + 1 < M → P.s (m + 1) < P.s (m + 1 + 1)) ∧
      (m + 1 = M → P.s (m + 1) ≤ P.S') := by
    refine ⟨fun h => P.s_lt (m + 1) h, fun h => ?_⟩
    have h1 := P.s_lt_S
    have h2 := P.S_lt_S'
    rw [h]; linarith
  obtain ⟨R', hR'0, hR'⟩ := exists_bound_Ξ P hmM hσ'
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * (R' + 1), by positivity, ?_⟩
  have hblow : Tendsto (fun δ => ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖) (𝓝[>] 0) atTop :=
    (P.blowup m hm).comp (tendsto_sub_nhdsLT _)
  have hdir : Tendsto (fun δ => ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖⁻¹ •
      P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)) (𝓝[>] 0) (𝓝 (P.u (m + 1))) :=
    (P.dir m hm).comp (tendsto_sub_nhdsLT _)
  set L : ℝ := max (max 2 (4 / r)) (1 + N * (R' + 1) / ε₁) with hL
  filter_upwards [hblow.eventually_ge_atTop L,
    Metric.tendsto_nhds.mp hdir (r / 2) (by positivity),
    Ioo_mem_nhdsGT (sub_pos.mpr hss)] with δ hRδ hdirδ hδ
  set σ := P.s (m + 1) - δ with hσdef
  set n := P.n (m + 1) with hndef
  set Rδ := ‖P.Ξ n σ‖ with hRδdef
  have hR2 : 2 ≤ Rδ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRδ
  have hR4 : 4 / r ≤ Rδ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRδ
  have hRε : 1 + N * (R' + 1) / ε₁ ≤ Rδ := le_trans (le_max_right _ _) hRδ
  refine ⟨hR2, hδ.2, ?_⟩
  have hσ₀ : P.s m < σ := by rw [hσdef]; linarith [hδ.2]
  have hσs : σ < P.s (m + 1) := by rw [hσdef]; linarith [hδ.1]
  have hσ₁ : (m < M → σ < P.s (m + 1)) ∧ (m = M → σ < P.S') :=
    ⟨fun _ => hσs, fun h => absurd h (ne_of_lt hm)⟩
  obtain ⟨SP1, SP2, ⟨K, SP3⟩, ⟨R4, SP4⟩⟩ :=
    stage_plateau hF hk hH P θ D hθ hm.le hpl hC hσ₀ hσ₁
  have hσ₂ : (m < M → P.s (m + 1) - δ / 2 < P.s (m + 1)) ∧
      (m = M → P.s (m + 1) - δ / 2 ≤ P.S') :=
    ⟨fun _ => by linarith [hδ.1], fun h => absurd h (ne_of_lt hm)⟩
  have hτ0 : ∀ᶠ α in 𝓝[>] 0, 0 ≤ τ α := by
    filter_upwards [hC.mem, self_mem_nhdsWithin] with α h hα
    exact (hθ α hα).1.nonneg h
  have hX : 0 < σ - P.s m := by linarith
  have ht0nn : ∀ᶠ α in 𝓝[>] 0, 0 ≤ τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m) := by
    filter_upwards [hτ0, self_mem_nhdsWithin] with α h hα
    have : 0 ≤ (α ^ (k - 2))⁻¹ * (σ - P.s m) :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hα) _)) hX.le
    linarith
  have htime0 : Tendsto (fun α => α ^ (k - 2) * (τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m)))
      (𝓝[>] 0) (𝓝 σ) := by
    have := tendsto_shift (k := k) (X := σ - P.s m) hC.time
    rwa [add_sub_cancel] at this
  have hconv : ∀ i ∉ P.A m, Tendsto (fun α => α⁻¹ • θ α (τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m)) i)
      (𝓝[>] 0) (𝓝 (P.Ξ i σ)) := by
    intro i hi
    refine tendsto_of_close ((P.Ξ_continuousOn hm.le hi hσ₂).continuousWithinAt
      ⟨by linarith, by rw [hσdef]; linarith [hδ.1]⟩) ?_ htime0 ?_
    · intro ε hε
      filter_upwards [SP2 i hi ε hε, ht0nn] with α h1 h2
      exact h1 _ ⟨h2, le_rfl⟩
    · filter_upwards [ht0nn, self_mem_nhdsWithin, htime0.eventually_lt_const
        (show σ < P.s (m + 1) - δ / 2 by rw [hσdef]; linarith [hδ.1])] with α h1 h2 h3
      exact ⟨mul_nonneg (pow_nonneg (le_of_lt h2) _) h1, h3.le⟩
  have hclose : ∀ᶠ α in 𝓝[>] 0, ∀ i ∉ P.A m,
      ‖α⁻¹ • θ α (τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m)) i - P.Ξ i σ‖ ≤ 1 := by
    have : ∀ i, ∀ᶠ α in 𝓝[>] (0 : ℝ), i ∉ P.A m →
        ‖α⁻¹ • θ α (τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m)) i - P.Ξ i σ‖ ≤ 1 := by
      intro i
      by_cases hi : i ∈ P.A m
      · exact Filter.Eventually.of_forall fun α h => absurd hi h
      · filter_upwards [(Metric.tendsto_nhds.mp (hconv i hi)) 1 one_pos] with α hα _
        rw [← dist_eq_norm]; exact hα.le
    exact Filter.eventually_all.mpr this
  have hR1 : 0 < Rδ + 1 := by linarith
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) <
      min 1 (min (ρ₁ / (Rδ + 1)) (ρ₁ / (|R4| + 1))) by positivity), hC.mem, hC.near, SP1, SP3,
      SP4, hclose, exp_bound_eventually (r₀ := r₀) (K := K) hk hμ hX]
    with α hα hαs hmem hnear hSP1 hSP3 hSP4 hcl hexp
  have hα0 : (0 : ℝ) < α := hα
  have hα1 : α ≤ 1 := (hαs.2.trans_le (min_le_left _ _)).le
  have hαρ : α * (Rδ + 1) < ρ₁ := by
    have : α < ρ₁ / (Rδ + 1) := hαs.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rwa [lt_div_iff₀ hR1] at this
  have hαR4 : α * R4 < ρ₁ := by
    have : α < ρ₁ / (|R4| + 1) := hαs.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith [le_abs_self R4]
  have hmax := (hθ α hα0).1
  set t0 := τ α + (α ^ (k - 2))⁻¹ * (σ - P.s m) with ht0def
  have hτ0α : 0 ≤ τ α := hmax.nonneg hmem
  have hXα : 0 ≤ (α ^ (k - 2))⁻¹ * (σ - P.s m) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hα0.le _)) hX.le
  have hτt0 : τ α ≤ t0 := le_add_of_nonneg_right hXα
  have ht0D : t0 ∈ D α := hSP1 ⟨hτ0α.trans hτt0, le_rfl⟩
  -- the escaping neuron at `t₀`
  set y := α⁻¹ • θ α t0 n with hydef
  have hy : ‖y - P.Ξ n σ‖ ≤ 1 := hcl n hn
  have hθn : θ α t0 n = α • y := (smul_inv_smul₀ hα0.ne' _).symm
  have hnorm : ‖θ α t0 n‖ = α * ‖y‖ := by rw [hθn, norm_smul_of_nonneg hα0.le]
  have hy1 : Rδ - 1 ≤ ‖y‖ := by
    have := norm_le_insert' (P.Ξ n σ) y
    rw [norm_sub_rev] at this
    linarith
  have hy2 : ‖y‖ ≤ Rδ + 1 := by
    have := norm_le_insert' y (P.Ξ n σ)
    linarith
  have hlower : α * (Rδ - 1) ≤ ‖θ α t0 n‖ := by
    rw [hnorm]; exact mul_le_mul_of_nonneg_left hy1 hα0.le
  have hupper : ‖θ α t0 n‖ ≤ α * (Rδ + 1) := by
    rw [hnorm]; exact mul_le_mul_of_nonneg_left hy2 hα0.le
  have hlowα : α ≤ ‖θ α t0 n‖ := le_trans (by nlinarith) hlower
  have hpos : 0 < ‖θ α t0 n‖ := hα0.trans_le hlowα
  have hltρ : ‖θ α t0 n‖ < ρ₁ := hupper.trans_lt hαρ
  -- direction
  have hΞ0 : P.Ξ n σ ≠ 0 := norm_pos_iff.mp (show (0 : ℝ) < Rδ by linarith)
  have hy0 : ‖y‖ ≠ 0 := by linarith
  have hdir' : ‖‖θ α t0 n‖⁻¹ • θ α t0 n - P.u (m + 1)‖ ≤ r := by
    have e1 : ‖θ α t0 n‖⁻¹ • θ α t0 n = ‖y‖⁻¹ • y := by
      rw [hnorm, hθn, smul_smul]
      congr 1
      field_simp
    rw [e1]
    have h1 : ‖‖y‖⁻¹ • y - ‖P.Ξ n σ‖⁻¹ • P.Ξ n σ‖ ≤ 2 * ‖y - P.Ξ n σ‖ / ‖P.Ξ n σ‖ :=
      norm_dir_sub_le hΞ0
    have h2 : ‖‖P.Ξ n σ‖⁻¹ • P.Ξ n σ - P.u (m + 1)‖ < r / 2 := by
      rw [← dist_eq_norm]; exact hdirδ
    have h3 : 2 * ‖y - P.Ξ n σ‖ / ‖P.Ξ n σ‖ ≤ r / 2 := by
      rw [div_le_iff₀ (show (0 : ℝ) < ‖P.Ξ n σ‖ by linarith)]
      have h4 : 4 ≤ r * Rδ := by
        rw [div_le_iff₀ hr] at hR4; linarith
      have h5 : 2 * ‖y - P.Ξ n σ‖ ≤ 2 := by linarith
      have h6 : (2 : ℝ) ≤ r / 2 * Rδ := by linarith
      exact h5.trans h6
    calc ‖‖y‖⁻¹ • y - P.u (m + 1)‖
        ≤ ‖‖y‖⁻¹ • y - ‖P.Ξ n σ‖⁻¹ • P.Ξ n σ‖ + ‖‖P.Ξ n σ‖⁻¹ • P.Ξ n σ - P.u (m + 1)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r := by linarith
  -- the other inactive neurons
  have hz : ‖θ α t0 - proj (P.A (m + 1)) (θ α t0)‖ ≤ α * (N * (R' + 1)) := by
    have hcomp : ∀ i, ‖(θ α t0 - proj (P.A (m + 1)) (θ α t0)) i‖ ≤ α * (R' + 1) := by
      intro i
      by_cases hi : i ∈ P.A (m + 1)
      · rw [sub_proj_apply_of_mem hi, norm_zero]; positivity
      · have hiA : i ∉ P.A m := fun h => hi (by rw [hA']; exact Finset.mem_insert_of_mem h)
        have h1 : ‖α⁻¹ • θ α t0 i - P.Ξ i σ‖ ≤ 1 := hcl i hiA
        have h2 : ‖P.Ξ i σ‖ ≤ R' := hR' i hi σ ⟨by linarith, hσs.le⟩
        have h3 : (θ α t0 - proj (P.A (m + 1)) (θ α t0)) i = θ α t0 i := by
          simp [hi]
        rw [h3]
        have h4 : ‖α⁻¹ • θ α t0 i‖ ≤ R' + 1 := by
          have := norm_le_insert' (α⁻¹ • θ α t0 i) (P.Ξ i σ)
          linarith
        rw [norm_smul_of_nonneg (inv_nonneg.mpr hα0.le)] at h4
        calc ‖θ α t0 i‖ = α * (α⁻¹ * ‖θ α t0 i‖) := by field_simp
          _ ≤ α * (R' + 1) := mul_le_mul_of_nonneg_left h4 hα0.le
    calc ‖θ α t0 - proj (P.A (m + 1)) (θ α t0)‖ ≤ N * (α * (R' + 1)) :=
          norm_le_card_mul (by positivity) hcomp
      _ = α * (N * (R' + 1)) := by ring
  have hzε : ‖θ α t0 - proj (insert n (P.A m)) (θ α t0)‖ ≤ ε₁ * ‖θ α t0 n‖ := by
    rw [← hA']
    have h1 : N * (R' + 1) ≤ ε₁ * (Rδ - 1) := by
      have h2 : N * (R' + 1) / ε₁ ≤ Rδ - 1 := by linarith
      rw [div_le_iff₀ hε₁] at h2; linarith
    calc ‖θ α t0 - proj (P.A (m + 1)) (θ α t0)‖ ≤ α * (N * (R' + 1)) := hz
      _ ≤ α * (ε₁ * (Rδ - 1)) := mul_le_mul_of_nonneg_left h1 hα0.le
      _ = ε₁ * (α * (Rδ - 1)) := by ring
      _ ≤ ε₁ * ‖θ α t0 n‖ := mul_le_mul_of_nonneg_left hlower hε₁.le
  -- the active coordinates
  have ha : ‖proj (P.A m) (θ α t0) - P.θs m‖ ≤ ‖θ α t0 n‖ := by
    have h1 := hSP3 t0 ⟨hτt0, le_rfl⟩
    have h2 : t0 - τ α = (α ^ (k - 2))⁻¹ * (σ - P.s m) := by rw [ht0def]; ring
    rw [h2] at h1
    calc ‖proj (P.A m) (θ α t0) - P.θs m‖
        ≤ Real.exp (-μ * ((α ^ (k - 2))⁻¹ * (σ - P.s m))) *
            ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ + K * α ^ k := h1
      _ ≤ Real.exp (-μ * ((α ^ (k - 2))⁻¹ * (σ - P.s m))) * r₀ + K * α ^ k := by gcongr
      _ ≤ α := hexp
      _ ≤ ‖θ α t0 n‖ := hlowα
  have hEsc : EscHyp (P.A m) n (P.θs m) (P.u (m + 1)) ρ₁ r ε₁ (θ α t0) :=
    ⟨hpos, hltρ, hdir', hzε, ha⟩
  obtain ⟨t₁', ht₁D, hlt, hat, hbefore, htime, hinvb⟩ := hinv (θ α) (D α) hmax t0 ht0D hEsc
  have hjt : jumpTime θ D τ n ρ₁ α = t₁' := by
    apply IsLeast.csInf_eq
    refine ⟨⟨ht₁D, hτt0.trans hlt.le, hat.ge⟩, ?_⟩
    rintro t ⟨-, hτt, hρt⟩
    by_contra hlt'
    replace hlt' : t < t₁' := not_le.mp hlt'
    by_cases htt0 : t < t0
    · have h1 := hSP4 t ⟨hτt, htt0.le⟩ n hn
      linarith
    · have h1 := hbefore t ⟨not_lt.mp htt0, hlt'⟩
      linarith
  rw [hjt]
  refine ⟨hα0, hα1, ht0D, hEsc, hlower, hupper, hz, ht₁D, hlt, hat, hbefore, htime, ?_⟩
  rw [hA']
  exact hinvb

/-- The jump times satisfy `α^{k-2} t₁ → s_{m+1}`: for every small `δ`,
`α^{k-2} t₁ ∈ [α^{k-2} t₀, α^{k-2} t₀ + C (R_δ - 1)^{2-k}]` and `α^{k-2} t₀ → s_{m+1} - δ`. -/
private lemma jump_time {m : ℕ} (hm : m < M) {r₀ : ℝ} {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {ρ₁ r ε₁ C B₀ : ℝ} (hC0 : 0 ≤ C) {t₁ : ℝ → ℝ}
    (hgood : ∀ᶠ δ in 𝓝[>] 0, 2 ≤ ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ ∧
      δ < P.s (m + 1) - P.s m ∧ ∀ᶠ α in 𝓝[>] 0,
      JumpGood P θ D m ρ₁ r ε₁ C B₀ (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m))
        (t₁ α) ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ α) :
    Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 (P.s (m + 1))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hblow : Tendsto (fun δ => ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖) (𝓝[>] 0) atTop :=
    (P.blowup m hm).comp (tendsto_sub_nhdsLT _)
  have hsmall := tendsto_inv_pow_sub_one hk hblow C
  obtain ⟨δ, ⟨hR2, -, hev⟩, hδε, hδC⟩ := (hgood.and
    ((eventually_Ioo (show (0 : ℝ) < ε / 2 by positivity)).and
      (hsmall.eventually_lt_const (show (0 : ℝ) < ε / 4 by positivity)))).exists
  have ht0 := tendsto_shift (k := k) (X := P.s (m + 1) - δ - P.s m) hC.time
  filter_upwards [hev, Metric.tendsto_nhds.mp ht0 (ε / 4) (by positivity)] with α hJ hcl
  rw [Real.dist_eq] at hcl ⊢
  have hα0 := hJ.pos
  set t0 := τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m) with ht0def
  have hb : α ^ (k - 2) * (t₁ α - t0) ≤
      C * ((‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ - 1) ^ (k - 2))⁻¹ :=
    rescaled_time_le hα0 (by linarith) hJ.lower hC0 hJ.time
  have hlt : α ^ (k - 2) * t0 < α ^ (k - 2) * t₁ α := mul_lt_mul_of_pos_left hJ.lt (pow_pos hα0 _)
  have heq : α ^ (k - 2) * (t₁ α - t0) = α ^ (k - 2) * t₁ α - α ^ (k - 2) * t0 := by ring
  rw [abs_lt] at hcl ⊢
  constructor <;> linarith [hδε.1, hδε.2]

/-- Shadowing of the escape orbit during the jump (Lemma 3(b)), for a given `δ`. -/
private lemma jump_shadow {m : ℕ} {τ : ℝ → ℝ} {ρ₁ r ε₁ C c B₀ δ : ℝ} {t₁ : ℝ → ℝ}
    (hesc : EscapeProp F k (P.A m) (P.θs m) (P.n (m + 1)) (P.u (m + 1)) (P.γ (m + 1))
      ρ₁ r ε₁ C c)
    (hev : ∀ᶠ α in 𝓝[>] 0, JumpGood P θ D m ρ₁ r ε₁ C B₀
      (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m)) (t₁ α)
      ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ α) :
    ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, ‖θ α (t₁ α) - P.γ (m + 1) c‖ < ε ∧
      ∀ t ∈ Icc (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m)) (t₁ α),
        ∃ s ≤ c, ‖θ α t - P.γ (m + 1) s‖ < ε := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hsh⟩ := hesc
  intro ε hε
  obtain ⟨δs, hδs, hsh'⟩ := hsh ε hε
  set R := ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ with hR
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < δs / (|R| + 2) by positivity)]
    with α hJ hα
  have hsmall : ‖θ α (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m)) (P.n (m + 1))‖ < δs := by
    have h1 := hJ.upper
    have h2 : α * (|R| + 2) < δs := by
      have := hα.2
      rwa [lt_div_iff₀ (by positivity)] at this
    have h3 : α * (R + 1) ≤ α * (|R| + 2) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self R]) hJ.pos.le
    linarith
  exact hsh' (θ α) (D α) (hθ α hJ.pos).1 _ hJ.t₀_mem hJ.hyp hsmall _ hJ.t₁_mem hJ.lt hJ.at_t₁
    hJ.before

/-- The dormant weights during and after the jump, up to `t₁ + T`: they move by
`O(R_δ^{2-k})` during the jump and by `O(α^{k-2} T)` afterwards, in rescaled units. -/
private lemma jump_dormant {m : ℕ} (hm : m < M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {ρ₁ r ε₁ C c B₀ : ℝ} (hC0 : 0 ≤ C) (hB₀ : 0 ≤ B₀) {t₁ : ℝ → ℝ}
    (hgood : ∀ᶠ δ in 𝓝[>] 0, 2 ≤ ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ ∧
      δ < P.s (m + 1) - P.s m ∧ ∀ᶠ α in 𝓝[>] 0,
      JumpGood P θ D m ρ₁ r ε₁ C B₀ (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m))
        (t₁ α) ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ α)
    (htime : Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 (P.s (m + 1))))
    (hloc : ∀ T > 0, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, Icc (t₁ α - T) (t₁ α + T) ⊆ D α ∧
      ∀ s ∈ Icc (-T) T, ‖θ α (t₁ α + s) - P.γ (m + 1) (s + c)‖ < ε)
    {T : ℝ} (hT : 0 < T) :
    ∀ i ∉ P.A (m + 1), ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc 0 (t₁ α + T),
      ‖α⁻¹ • θ α t i - P.Ξ i (α ^ (k - 2) * t)‖ ≤ ε := by
  intro i hi ε hε
  have hA' : P.A (m + 1) = insert (P.n (m + 1)) (P.A m) := P.A_succ m hm
  have hiA : i ∉ P.A m := fun h => hi (by rw [hA']; exact Finset.mem_insert_of_mem h)
  have hmM : m + 1 ≤ M := hm
  -- continuity of `Ξ_i` beyond `s_{m+1}`
  have hσ : (m + 1 < M → P.s (m + 1) < P.s (m + 1 + 1)) ∧
      (m + 1 = M → P.s (m + 1) < P.S') := by
    refine ⟨fun h => P.s_lt (m + 1) h, fun h => ?_⟩
    have h1 := P.s_lt_S
    have h2 := P.S_lt_S'
    rw [h]; linarith
  obtain ⟨σ₂, hσ₂, hσ₂'⟩ := exists_gt_horizon P hσ
  obtain ⟨η, hη, huc⟩ := uc_Icc (P.Ξ_continuousOn hmM hi hσ₂') (show 0 < ε / 4 by positivity)
  -- a bound on the trajectory after the jump
  have hγ := P.escape m hm
  obtain ⟨Bγ, hBγ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc c (c + T))
    (f := P.γ (m + 1)) (fun t _ => (hγ.sol t).continuousAt.continuousWithinAt)
  set Rb := max (‖P.θs m‖ + 1) (Bγ + 1) with hRb
  obtain ⟨Cg, hCg0, hCg⟩ := grad_apply_le hF hk hH Rb
  have hgradbd : ∀ x : Θ ι E, ‖x‖ ≤ Rb → ‖(gradient F x) i‖ ≤ Cg * ‖x i‖ ^ (k - 1) :=
    fun x hx => hCg i x hx
  -- choice of `δ`
  have hblow : Tendsto (fun δ => ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖) (𝓝[>] 0) atTop :=
    (P.blowup m hm).comp (tendsto_sub_nhdsLT _)
  set W : ℝ := Cg * (2 * B₀) ^ (k - 1) * C with hW
  have hsmall := tendsto_inv_pow_sub_one hk hblow W
  obtain ⟨δ, ⟨hR2, hδs, hev⟩, hδη, hδW⟩ := (hgood.and
    ((eventually_Ioo (show (0 : ℝ) < η / 2 by positivity)).and
      (hsmall.eventually_lt_const (show (0 : ℝ) < ε / 4 by positivity)))).exists
  set R := ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ with hRdef
  -- Lemma 2 up to `s_{m+1} - δ`
  have hσ₀ : P.s m < P.s (m + 1) - δ := by linarith
  have hσ₁ : (m < M → P.s (m + 1) - δ < P.s (m + 1)) ∧ (m = M → P.s (m + 1) - δ < P.S') :=
    ⟨fun _ => by linarith [hδη.1], fun h => absurd h (ne_of_lt hm)⟩
  obtain ⟨-, SP2, -, -⟩ := stage_plateau hF hk hH P θ D hθ hm.le hpl hC hσ₀ hσ₁
  -- time limits
  have hk2 : k - 2 ≠ 0 := by omega
  have ht0 := tendsto_shift (k := k) (X := P.s (m + 1) - δ - P.s m) hC.time
  have hT0 : Tendsto (fun α : ℝ => T * α ^ (k - 2)) (𝓝[>] 0) (𝓝 0) := tendsto_mul_pow_zero T hk2
  have hend : Tendsto (fun α => α ^ (k - 2) * (t₁ α + T)) (𝓝[>] 0) (𝓝 (P.s (m + 1))) := by
    have := htime.add hT0
    rw [add_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun α => ?_)
    ring
  have hdiff := hend.sub ht0
  have hdiffδ : P.s (m + 1) - (P.s m + (P.s (m + 1) - δ - P.s m)) < η := by linarith [hδη.2]
  have hTc : Tendsto (fun α : ℝ => ((k : ℝ) - 2) * Cg * T * (2 * B₀) ^ (k - 2) * α ^ (k - 2))
      (𝓝[>] 0) (𝓝 0) := tendsto_mul_pow_zero _ hk2
  have hhalf : (0 : ℝ) < 1 - (2 : ℝ)⁻¹ ^ (k - 2) := by
    have : (2 : ℝ)⁻¹ ^ (k - 2) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hk2
    linarith
  have hmv : Tendsto (fun α : ℝ => Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_pow_zero _ hk2
  filter_upwards [hev, SP2 i hiA (ε / 4) (by positivity), hloc T hT 1 one_pos,
    hend.eventually_lt_const hσ₂, hdiff.eventually_lt_const hdiffδ,
    hTc.eventually_lt_const hhalf, hmv.eventually_lt_const (show (0 : ℝ) < ε / 4 by positivity)]
    with α hJ hSP2 hL hend1 hdiff1 hTc1 hmv1
  intro t ht
  set t0 := τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m) with ht0def
  have hα0 := hJ.pos
  have hmax := (hθ α hα0).1
  have ht0nn : 0 ≤ t0 := hmax.nonneg hJ.t₀_mem
  by_cases htt0 : t ≤ t0
  · exact (hSP2 t ⟨ht.1, htt0⟩).trans (by linarith)
  have htt0' : t0 ≤ t := (not_le.mp htt0).le
  -- bounds during the jump
  have hbd1 : ∀ s ∈ Icc t0 (t₁ α), ‖θ α s‖ ≤ Rb ∧ ‖θ α s i‖ ≤ 2 * (α * B₀) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hJ.inv s hs
    constructor
    · have h3 := norm_le_insert' (θ α s) (P.θs m)
      have h4 : ‖P.θs m‖ + 1 ≤ Rb := le_max_left _ _
      linarith
    · calc ‖θ α s i‖ ≤ ‖θ α s - proj (P.A (m + 1)) (θ α s)‖ := norm_apply_le_norm_sub_proj hi _
        _ ≤ 2 * ‖θ α t0 - proj (P.A (m + 1)) (θ α t0)‖ := h1
        _ ≤ 2 * (α * B₀) := by linarith [hJ.z₀]
  have hmove1 := move_le hmax hJ.t₀_mem hJ.t₁_mem hgradbd hCg0 hbd1
  -- bounds after the jump
  have hRb2 : ∀ s ∈ Icc (t₁ α) (t₁ α + T), ‖θ α s‖ ≤ Rb := by
    intro s hs
    have h1 := hL.2 (s - t₁ α) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [add_sub_cancel] at h1
    have h2 : ‖P.γ (m + 1) (s - t₁ α + c)‖ ≤ Bγ :=
      hBγ _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h3 := norm_le_insert' (θ α s) (P.γ (m + 1) (s - t₁ α + c))
    have h4 : Bγ + 1 ≤ Rb := le_max_right _ _
    linarith
  have hD2 : Icc (t₁ α) (t₁ α + T) ⊆ D α := fun s hs => hL.1 ⟨by linarith [hs.1], hs.2⟩
  have ht₁pos : 0 < t₁ α := lt_of_le_of_lt ht0nn hJ.lt
  have hi₁ : ‖θ α (t₁ α) i‖ ≤ 2 * (α * B₀) := (hbd1 (t₁ α) ⟨hJ.lt.le, le_rfl⟩).2
  have hTc' : ((k : ℝ) - 2) * Cg * (t₁ α + T - t₁ α) * (2 * (α * B₀)) ^ (k - 2) <
      1 - (2 : ℝ)⁻¹ ^ (k - 2) := by
    have : ((k : ℝ) - 2) * Cg * (t₁ α + T - t₁ α) * (2 * (α * B₀)) ^ (k - 2) =
        ((k : ℝ) - 2) * Cg * T * (2 * B₀) ^ (k - 2) * α ^ (k - 2) := by
      rw [add_sub_cancel_left, show 2 * (α * B₀) = (2 * B₀) * α by ring, mul_pow]; ring
    rw [this]; exact hTc1
  have hcomp := comp_le_two hk hmax ht₁pos (by linarith) hD2 hgradbd hCg0
    (mul_nonneg zero_le_two (mul_nonneg hα0.le hB₀)) hRb2 hi₁ hTc'
  have hmove2 := move_le hmax hJ.t₁_mem (hD2 ⟨by linarith, le_rfl⟩) hgradbd hCg0
    (fun s hs => ⟨hRb2 s hs, hcomp s hs⟩)
  -- total movement of the `i`-th weight
  have hkk : k - 1 = (k - 2) + 1 := by omega
  have hbound1 : Cg * (2 * (α * B₀)) ^ (k - 1) * (t₁ α - t0) ≤
      α * (W * ((R - 1) ^ (k - 2))⁻¹) := by
    have h1 : α ^ (k - 2) * (t₁ α - t0) ≤ C * ((R - 1) ^ (k - 2))⁻¹ :=
      rescaled_time_le hα0 (by linarith) hJ.lower hC0 hJ.time
    have h2 : Cg * (2 * (α * B₀)) ^ (k - 1) * (t₁ α - t0) =
        α * (Cg * (2 * B₀) ^ (k - 1) * (α ^ (k - 2) * (t₁ α - t0))) := by
      rw [show 2 * (α * B₀) = α * (2 * B₀) by ring, mul_pow, hkk]; ring
    have h3 : 0 ≤ Cg * (2 * B₀) ^ (k - 1) := mul_nonneg hCg0 (pow_nonneg (by linarith) _)
    rw [h2, hW]
    calc α * (Cg * (2 * B₀) ^ (k - 1) * (α ^ (k - 2) * (t₁ α - t0)))
        ≤ α * (Cg * (2 * B₀) ^ (k - 1) * (C * ((R - 1) ^ (k - 2))⁻¹)) := by
          apply mul_le_mul_of_nonneg_left _ hα0.le
          exact mul_le_mul_of_nonneg_left h1 h3
      _ = α * (Cg * (2 * B₀) ^ (k - 1) * C * ((R - 1) ^ (k - 2))⁻¹) := by ring
  have hbound2 : Cg * (2 * (2 * (α * B₀))) ^ (k - 1) * T =
      α * (Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2)) := by
    rw [show 2 * (2 * (α * B₀)) = α * (4 * B₀) by ring, mul_pow, hkk]; ring
  have hc1 : 0 ≤ Cg * (2 * (α * B₀)) ^ (k - 1) :=
    mul_nonneg hCg0 (pow_nonneg (mul_nonneg zero_le_two (mul_nonneg hα0.le hB₀)) _)
  have hc2 : 0 ≤ Cg * (2 * (2 * (α * B₀))) ^ (k - 1) :=
    mul_nonneg hCg0 (pow_nonneg (mul_nonneg zero_le_two
      (mul_nonneg zero_le_two (mul_nonneg hα0.le hB₀))) _)
  have hmove : ‖θ α t i - θ α t0 i‖ ≤
      α * (W * ((R - 1) ^ (k - 2))⁻¹) + α * (Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2)) := by
    have hpos2 : 0 ≤ α * (Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2)) := by
      rw [← hbound2]; exact mul_nonneg hc2 hT.le
    by_cases htt1 : t ≤ t₁ α
    · have h1 := hmove1 t ⟨htt0', htt1⟩
      have h2 : Cg * (2 * (α * B₀)) ^ (k - 1) * (t - t0) ≤
          Cg * (2 * (α * B₀)) ^ (k - 1) * (t₁ α - t0) :=
        mul_le_mul_of_nonneg_left (by linarith) hc1
      linarith
    · have htt1' : t₁ α ≤ t := (not_le.mp htt1).le
      have h1 := hmove1 (t₁ α) ⟨hJ.lt.le, le_rfl⟩
      have h2 := hmove2 t ⟨htt1', ht.2⟩
      have h3 : Cg * (2 * (2 * (α * B₀))) ^ (k - 1) * (t - t₁ α) ≤
          Cg * (2 * (2 * (α * B₀))) ^ (k - 1) * T :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) hc2
      have h4 := norm_sub_le_norm_sub_add_norm_sub (θ α t i) (θ α (t₁ α) i) (θ α t0 i)
      linarith
  -- in rescaled units
  have hres : ‖α⁻¹ • θ α t i - α⁻¹ • θ α t0 i‖ ≤
      W * ((R - 1) ^ (k - 2))⁻¹ + Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2) := by
    rw [← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hα0.le)]
    calc α⁻¹ * ‖θ α t i - θ α t0 i‖
        ≤ α⁻¹ * (α * (W * ((R - 1) ^ (k - 2))⁻¹) +
            α * (Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2))) :=
          mul_le_mul_of_nonneg_left hmove (inv_nonneg.mpr hα0.le)
      _ = W * ((R - 1) ^ (k - 2))⁻¹ + Cg * (4 * B₀) ^ (k - 1) * T * α ^ (k - 2) := by
          rw [mul_add, inv_mul_cancel_left₀ hα0.ne', inv_mul_cancel_left₀ hα0.ne']
  -- the dormant state varies little
  have hΞ : ‖P.Ξ i (α ^ (k - 2) * t0) - P.Ξ i (α ^ (k - 2) * t)‖ < ε / 4 := by
    have hc : 0 < α ^ (k - 2) := pow_pos hα0 _
    have h1 : α ^ (k - 2) * t0 ≤ α ^ (k - 2) * t := mul_le_mul_of_nonneg_left htt0' hc.le
    have h2 : α ^ (k - 2) * t ≤ α ^ (k - 2) * (t₁ α + T) := mul_le_mul_of_nonneg_left ht.2 hc.le
    apply huc _ ⟨mul_nonneg hc.le ht0nn, by linarith⟩ _ ⟨mul_nonneg hc.le ht.1, by linarith⟩
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hSP2t0 := hSP2 t0 ⟨ht0nn, le_rfl⟩
  have e1 := norm_sub_le_norm_sub_add_norm_sub (α⁻¹ • θ α t i) (α⁻¹ • θ α t0 i)
    (P.Ξ i (α ^ (k - 2) * t))
  have e2 := norm_sub_le_norm_sub_add_norm_sub (α⁻¹ • θ α t0 i) (P.Ξ i (α ^ (k - 2) * t0))
    (P.Ξ i (α ^ (k - 2) * t))
  linarith

/-- `(C_{m+1})` at `τ_{m+1} = t₁ + T`, for every large `T`. -/
private lemma jump_claim {m : ℕ} (hm : m < M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {r₀' : ℝ} (hr₀' : 0 < r₀') {ρ₁ r ε₁ C c B₀ : ℝ} (hC0 : 0 ≤ C) (hB₀ : 0 ≤ B₀)
    {t₁ : ℝ → ℝ}
    (hgood : ∀ᶠ δ in 𝓝[>] 0, 2 ≤ ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ ∧
      δ < P.s (m + 1) - P.s m ∧ ∀ᶠ α in 𝓝[>] 0,
      JumpGood P θ D m ρ₁ r ε₁ C B₀ (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m))
        (t₁ α) ‖P.Ξ (P.n (m + 1)) (P.s (m + 1) - δ)‖ α)
    (htime : Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 (P.s (m + 1))))
    (hloc : ∀ T > 0, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0, Icc (t₁ α - T) (t₁ α + T) ⊆ D α ∧
      ∀ s ∈ Icc (-T) T, ‖θ α (t₁ α + s) - P.γ (m + 1) (s + c)‖ < ε) :
    ∃ T₀, ∀ T ≥ T₀, Claim P θ D (m + 1) r₀' (fun α => t₁ α + T) := by
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp (P.escape_lim m hm) (r₀' / 2) (by positivity)
  refine ⟨max 1 (T₁ - c), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTpos : 0 < T := by linarith
  have hTc : T₁ ≤ T + c := by
    have := le_trans (le_max_right _ _) hT
    linarith
  have hA' : P.A (m + 1) = insert (P.n (m + 1)) (P.A m) := P.A_succ m hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hloc T hTpos 1 one_pos] with α h
    exact h.1 ⟨by linarith, le_rfl⟩
  · filter_upwards [hloc T hTpos (r₀' / 2) (by positivity)] with α h
    have h1 := h.2 T ⟨by linarith, le_rfl⟩
    have h2 := hT₁ (T + c) hTc
    rw [dist_eq_norm] at h2
    have hγmem : P.γ (m + 1) (T + c) ∈ S2S.S (P.A (m + 1)) := by
      rw [hA']; exact (P.escape m hm).mem _
    have heq : proj (P.A (m + 1)) (θ α (t₁ α + T)) - P.θs (m + 1) =
        proj (P.A (m + 1)) (θ α (t₁ α + T) - P.γ (m + 1) (T + c)) +
          (P.γ (m + 1) (T + c) - P.θs (m + 1)) := by
      rw [map_sub, proj_eq_self_of_mem_S hγmem]; abel
    show ‖proj (P.A (m + 1)) (θ α (t₁ α + T)) - P.θs (m + 1)‖ ≤ r₀'
    rw [heq]
    have h3 : ‖proj (P.A (m + 1)) (θ α (t₁ α + T) - P.γ (m + 1) (T + c))‖ ≤
        ‖θ α (t₁ α + T) - P.γ (m + 1) (T + c)‖ := norm_zeroOut_le _ _
    have h4 := norm_add_le (proj (P.A (m + 1)) (θ α (t₁ α + T) - P.γ (m + 1) (T + c)))
      (P.γ (m + 1) (T + c) - P.θs (m + 1))
    linarith
  · show Tendsto (fun α => α ^ (k - 2) * (t₁ α + T)) (𝓝[>] 0) (𝓝 (P.s (m + 1)))
    have := htime.add (tendsto_mul_pow_zero T (show k - 2 ≠ 0 by omega))
    rw [add_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun α => ?_)
    ring
  · exact jump_dormant hF hk hH P θ D hθ hm hpl hC hC0 hB₀ hgood htime hloc hTpos

/-- The jump step: from `(C_m)`, `m < M`, Lemma 3 gives the jump times `t_{m+1}^α` (the first
time after `τ_m^α` at which `|w_{n_{m+1}}| = ρ₁`), the local uniform convergence of
`θ^α(t_{m+1}^α + ·)` to a time translate of `γ_{m+1}`, the shadowing of the escape orbit
during the escape, and `(C_{m+1})` with `τ_{m+1}^α = t_{m+1}^α + T` for every large `T`. -/
theorem stage_jump {m : ℕ} (hm : m < M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {r₀' μ' : ℝ} (hpl' : PlateauProp F k (P.A (m + 1)) (P.θs (m + 1)) r₀' μ') :
    ∃ (t₁ : ℝ → ℝ) (c : ℝ),
      Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 (P.s (m + 1))) ∧
      (∀ T > 0, ∀ᶠ α in 𝓝[>] 0, Icc (t₁ α - T) (t₁ α + T) ⊆ D α) ∧
      (∀ T > 0, TendstoUniformlyOn (fun α t => θ α (t₁ α + t)) (fun t => P.γ (m + 1) (t + c))
        (𝓝[>] 0) (Icc (-T) T)) ∧
      (∃ T₀, ∀ T ≥ T₀, Claim P θ D (m + 1) r₀' (fun α => t₁ α + T)) ∧
      (∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∀ ε > 0, ∀ᶠ α in 𝓝[>] 0,
        ∀ t ∈ Icc (τ α + (α ^ (k - 2))⁻¹ * (P.s (m + 1) - δ - P.s m)) (t₁ α),
          ∃ s ≤ 0, ‖θ α t - P.γ (m + 1) (s + c)‖ < ε) := by
  have hmin := P.isMin m hm.le
  have hn := P.n_notMem m hm
  have hu := P.u_max m hm
  have hU := P.U_pos hF hk hH hm
  have hγ := P.escape m hm
  obtain ⟨ρ₁, r, ε₁, C, c, hesc⟩ := escape hF hk hH hmin hn hu hU hγ
  have hC0 : 0 < C := hesc.2.2.2.2.2.1
  obtain ⟨B₀, hB₀, hgood⟩ := jump_core hF hk hH P θ D hθ hm hpl hC hesc
  set t₁ := jumpTime θ D τ (P.n (m + 1)) ρ₁ with ht₁
  have htime : Tendsto (fun α => α ^ (k - 2) * t₁ α) (𝓝[>] 0) (𝓝 (P.s (m + 1))) :=
    jump_time hF hk hH P θ D hθ hm hC hC0.le hgood
  obtain ⟨δ₁, hδ₁⟩ := hgood.exists
  have hev₁ := hδ₁.2.2
  have hD₁ : ∀ᶠ α in 𝓝[>] 0, t₁ α ∈ D α := hev₁.mono fun α h => h.t₁_mem
  have hpt : Tendsto (fun α => θ α (t₁ α)) (𝓝[>] 0) (𝓝 (P.γ (m + 1) c)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [jump_shadow hF hk hH P θ D hθ hesc hev₁ ε hε] with α h
    rw [dist_eq_norm]
    exact h.1
  have hs' : 0 < P.s (m + 1) := lt_of_le_of_lt (P.s_nonneg hm.le) (P.s_lt m hm)
  have hloc := local_conv hF hk hH θ D hθ hγ.sol hD₁ htime hs' hpt
  refine ⟨t₁, c, htime, ?_, ?_, ?_, ?_⟩
  · intro T hT
    filter_upwards [hloc T hT 1 one_pos] with α h
    exact h.1
  · intro T hT
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hloc T hT ε hε] with α h s hs
    rw [dist_comm, dist_eq_norm]
    exact h.2 s hs
  · exact jump_claim hF hk hH P θ D hθ hm hpl hC hpl'.1 hC0.le hB₀ hgood htime hloc
  · obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
    have hu0' : (0 : ℝ) < u := hu0
    refine ⟨u / 2, half_pos hu0', fun δ hδ ε hε => ?_⟩
    have hδu : δ ∈ Ioo 0 u := ⟨hδ.1, by linarith [hδ.2]⟩
    obtain ⟨-, -, hev⟩ := hu hδu
    filter_upwards [jump_shadow hF hk hH P θ D hθ hesc hev ε hε] with α h t ht
    obtain ⟨s, hs, hs'⟩ := h.2 t ht
    exact ⟨s - c, by linarith, by rwa [sub_add_cancel]⟩

end S2S
