import SaddleToSaddle.GradFlow

/-!
# Lemma 3 (Escape): polar coordinates and the invariance step

Write `θ = a + ι_n(ρ u) + z` with `a = π_A θ`, `ρ = |w_n|`, `|u| = 1`, and
`z = θ - π_{A ∪ {n}} θ`. In polar coordinates the gradient flow reads
`ρ̇ = ρ^{k-1} D`, `u̇ = ρ^{k-2} (G - D u)`, `ȧ = -∇_A F`, with `D = ⟨u, G⟩`.

This file proves the invariance step of the proof of Lemma 3: under the assumptions of
Lemma 3(b) at time `t₀`, `ρ` increases and reaches `ρ₁` at a time `t₁ ≤ t₀ + C ρ₀^{2-k}`,
`|z| ≤ 2η`, `|u - u*| ≤ r`, and `|a - θ*| ≤ ρ₀ + C ρ^k` (the slaving estimate) on `[t₀, t₁]`.
The constants are chosen in the order of the note: first `r`, then `ρ₁` and `ε₁`.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- The assumptions of Lemma 3(b) at the point `x = θ(t₀)`: `ρ₀ := |w_n| ∈ (0, ρ₁)`,
`|u - u*| ≤ r`, `η := |z| ≤ ε₁ ρ₀`, and `|a - θ*| ≤ ρ₀`. -/
def EscHyp (A : Finset ι) (n : ι) (θ₀ : Θ ι E) (u₀ : E) (ρ₁ r ε₁ : ℝ) (x : Θ ι E) : Prop :=
  0 < ‖x n‖ ∧ ‖x n‖ < ρ₁ ∧ ‖‖x n‖⁻¹ • x n - u₀‖ ≤ r ∧
    ‖x - proj (insert n A) x‖ ≤ ε₁ * ‖x n‖ ∧ ‖proj A x - θ₀‖ ≤ ‖x n‖

/-! ### Polar coordinates along a trajectory -/

private lemma escinv_hasDerivWithinAt_apply {θ : ℝ → Θ ι E} {θ' : Θ ι E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt θ θ' s t) (n : ι) :
    HasDerivWithinAt (fun s => θ s n) (θ' n) s t := by
  have := (PiLp.proj 2 (fun _ : ι => E) n).hasFDerivAt.comp_hasDerivWithinAt t h
  convert this using 1
  · funext s; simp
  · simp

private lemma escinv_hasDerivWithinAt_clm {θ : ℝ → Θ ι E} {θ' : Θ ι E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt θ θ' s t) (L : Θ ι E →L[ℝ] Θ ι E) :
    HasDerivWithinAt (fun s => L (θ s)) (L θ') s t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t h

/-- Polar form of the flow in `w_n`. -/
private lemma escinv_polar_ode {G : ℝ × E × Θ ι E → E} {n : ι}
    (hG : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    (hk : 3 ≤ k) {θ : ℝ → Θ ι E} {s : Set ℝ} {t : ℝ}
    (hθ : HasDerivWithinAt θ (gf F (θ t)) s t) (h0 : θ t n ≠ 0) :
    HasDerivWithinAt (fun s => ‖θ s n‖)
      (‖θ t n‖ ^ (k - 1) * ⟪‖θ t n‖⁻¹ • θ t n, G (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n, θ t)⟫) s t ∧
    HasDerivWithinAt (fun s => ‖θ s n‖⁻¹ • θ s n)
      (‖θ t n‖ ^ (k - 2) • (G (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n, θ t) -
        ⟪‖θ t n‖⁻¹ • θ t n, G (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n, θ t)⟫ • (‖θ t n‖⁻¹ • θ t n))) s t := by
  set ρ := ‖θ t n‖ with hρdef
  set u := ρ⁻¹ • θ t n with hudef
  set g := G (ρ, u, θ t) with hgdef
  have hρ0 : ρ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hρpos : 0 < ρ := norm_pos_iff.mpr h0
  have hw : ρ • u = θ t n := by rw [hudef, smul_smul, mul_inv_cancel₀ hρ0, one_smul]
  -- derivative of `w`
  have hw' : (gf F (θ t)) n = ρ ^ (k - 1) • g := by
    have h1 := hG ρ u (θ t)
    rw [hw, insertAt_self] at h1
    rw [← h1, gf]
    simp
  have hwd : HasDerivWithinAt (fun s => θ s n) (ρ ^ (k - 1) • g) s t := by
    rw [← hw']; exact escinv_hasDerivWithinAt_apply hθ n
  -- derivative of `ρ`
  have hsq : HasDerivWithinAt (fun s => ‖θ s n‖ ^ 2) (2 * ⟪θ t n, ρ ^ (k - 1) • g⟫) s t :=
    hwd.norm_sq
  have hsq0 : ‖θ t n‖ ^ 2 ≠ 0 := pow_ne_zero _ hρ0
  have hρd0 := hsq.sqrt hsq0
  have hρfun : (fun s => √(‖θ s n‖ ^ 2)) = fun s => ‖θ s n‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [hρfun, Real.sqrt_sq (norm_nonneg _)] at hρd0
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  have hρ' : 2 * ⟪θ t n, ρ ^ (k - 1) • g⟫ / (2 * ρ) = ρ ^ (k - 1) * ⟪u, g⟫ := by
    rw [← hw, real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hρ'] at hρd0
  refine ⟨hρd0, ?_⟩
  -- derivative of `u`
  have hinv := hρd0.inv hρ0
  have hud := hinv.smul hwd
  have hfun : ((fun s => ‖θ s n‖)⁻¹ • fun s => θ s n) = fun s => ‖θ s n‖⁻¹ • θ s n := by
    funext s; simp
  rw [hfun] at hud
  convert hud using 1
  have h1 : ρ⁻¹ * ρ ^ (k - 1) = ρ ^ (k - 2) := by
    rw [hk1, pow_succ]; field_simp
  have h2 : (-(ρ ^ (k - 1) * ⟪u, g⟫) / ρ ^ 2) * ρ = -(ρ ^ (k - 2) * ⟪u, g⟫) := by
    rw [hk1, pow_succ]; field_simp
  simp only [Pi.inv_apply, ← hρdef]
  rw [← hw]
  simp only [smul_sub, smul_smul]
  rw [h1, h2, neg_smul, ← sub_eq_add_neg]



/-- Basic facts on `ρ = ‖w_n‖` along a trajectory staying in a region where `κ ≤ D ≤ D₁`. -/
private lemma escinv_rho {G : ℝ × E × Θ ι E → E} {n : ι} (hk : 3 ≤ k)
    (hG : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    {K : Set (Θ ι E)} {κ D₁ : ℝ} (hpos : ∀ x ∈ K, 0 < ‖x n‖)
    (hD : ∀ x ∈ K, κ ≤ ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ∧
      ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ≤ D₁)
    {θ : ℝ → Θ ι E} {D : Set ℝ} (hθ : IsMaxFwd (gf F) θ D) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D)
    (hK : ∀ s ∈ Icc a b, θ s ∈ K) :
    ContinuousOn (fun s => ‖θ s n‖) (Icc a b) ∧
    (∀ s ∈ Icc a b, 0 < ‖θ s n‖) ∧
    (∀ s ∈ Ico a b, HasDerivWithinAt (fun s => ‖θ s n‖)
      (‖θ s n‖ ^ (k - 1) * ⟪‖θ s n‖⁻¹ • θ s n, G (‖θ s n‖, ‖θ s n‖⁻¹ • θ s n, θ s)⟫) (Ici s) s) ∧
    (∀ s ∈ Ico a b, κ * ‖θ s n‖ ^ (k - 1) ≤
      ‖θ s n‖ ^ (k - 1) * ⟪‖θ s n‖⁻¹ • θ s n, G (‖θ s n‖, ‖θ s n‖⁻¹ • θ s n, θ s)⟫) ∧
    (∀ s ∈ Ico a b, ‖θ s n‖ ^ (k - 1) * ⟪‖θ s n‖⁻¹ • θ s n, G (‖θ s n‖, ‖θ s n‖⁻¹ • θ s n, θ s)⟫ ≤
      D₁ * ‖θ s n‖ ^ (k - 1)) := by
  have hsub : Icc a b ⊆ D := hθ.Icc_subset ha hb
  have hθc : ContinuousOn θ (Icc a b) := hθ.continuousOn.mono hsub
  refine ⟨?_, fun s hs => hpos _ (hK s hs), fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hwc : ContinuousOn (fun s => θ s n) (Icc a b) :=
      (PiLp.continuous_apply 2 (fun _ : ι => E) n).comp_continuousOn hθc
    exact hwc.norm
  · have hsD : s ∈ D := hsub (Ico_subset_Icc_self hs)
    have hd : HasDerivWithinAt θ (gf F (θ s)) (Ici s) s :=
      (hθ.sol s hsD).mono (Ici_subset_Ici.mpr (hθ.nonneg hsD))
    exact (escinv_polar_ode hG hk hd
      (norm_pos_iff.mp (hpos _ (hK s (Ico_subset_Icc_self hs))))).1
  · have h := (hD _ (hK s (Ico_subset_Icc_self hs))).1
    have hp := pow_nonneg (norm_nonneg (θ s n)) (k - 1)
    nlinarith
  · have h := (hD _ (hK s (Ico_subset_Icc_self hs))).2
    have hp := pow_nonneg (norm_nonneg (θ s n)) (k - 1)
    nlinarith

/-- `ρ` is non-decreasing along a trajectory staying in a region where `D ≥ κ > 0`. -/
private lemma escinv_mono {G : ℝ × E × Θ ι E → E} {n : ι} (hk : 3 ≤ k)
    (hG : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    {K : Set (Θ ι E)} {κ D₁ : ℝ} (hpos : ∀ x ∈ K, 0 < ‖x n‖)
    (hD : ∀ x ∈ K, κ ≤ ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ∧
      ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ≤ D₁) (hκ : 0 < κ)
    {θ : ℝ → Θ ι E} {D : Set ℝ} (hθ : IsMaxFwd (gf F) θ D) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D)
    (hK : ∀ s ∈ Icc a b, θ s ∈ K) :
    ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc s₁ b, ‖θ s₁ n‖ ≤ ‖θ s₂ n‖ := by
  intro s₁ hs₁ s₂ hs₂
  have hs₁D : s₁ ∈ D := hθ.Icc_subset ha hb hs₁
  have hs₂D : s₂ ∈ D := hθ.Icc_subset ha hb ⟨hs₁.1.trans hs₂.1, hs₂.2⟩
  have hK' : ∀ s ∈ Icc s₁ s₂, θ s ∈ K := fun s hs => hK s ⟨hs₁.1.trans hs.1, hs.2.trans hs₂.2⟩
  obtain ⟨hc, hp, hd, hlow, -⟩ := escinv_rho hk hG hpos hD hθ hs₁D hs₂D hK'
  have h0 := inv_pow_le_of_deriv_ge hk hc hd hp hlow s₂ ⟨hs₂.1, le_rfl⟩
  have hk2 : (0:ℝ) ≤ (k:ℝ) - 2 := by
    have : (3:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h1 : (‖θ s₂ n‖ ^ (k - 2))⁻¹ ≤ (‖θ s₁ n‖ ^ (k - 2))⁻¹ := by
    have : 0 ≤ ((k:ℝ) - 2) * κ * (s₂ - s₁) := by
      apply mul_nonneg (mul_nonneg hk2 hκ.le); linarith [hs₂.1]
    linarith
  have hp1 := hp s₁ ⟨le_rfl, hs₂.1⟩
  have hp2 := hp s₂ ⟨hs₂.1, le_rfl⟩
  rw [inv_le_inv₀ (pow_pos hp2 _) (pow_pos hp1 _)] at h1
  exact (pow_le_pow_iff_left₀ hp1.le hp2.le (by omega)).mp h1



/-- The estimates of the invariance step on `[t₀, t]`, for a trajectory staying in a region `K`
where the box estimates hold. -/
private lemma escinv_est {G : ℝ × E × Θ ι E → E} {A : Finset ι} {n : ι} {θ₀ : Θ ι E} {u₀ : E}
    (hk : 3 ≤ k)
    (hG : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    {K : Set (Θ ι E)} {r κ D₁ Cz μ Ca ε₁ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hμ : 0 < μ)
    (hCz : 0 ≤ Cz) (hCa : 0 ≤ Ca) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₁z : Cz * ε₁ ≤ κ / 4)
    (hpos : ∀ x ∈ K, 0 < ‖x n‖)
    (hD : ∀ x ∈ K, κ ≤ ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ∧
      ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ≤ D₁)
    (hbar : ∀ x ∈ K, ‖‖x n‖⁻¹ • x n - u₀‖ = r →
      ⟪‖x n‖⁻¹ • x n - u₀, G (‖x n‖, ‖x n‖⁻¹ • x n, x) -
        ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ • (‖x n‖⁻¹ • x n)⟫ < 0)
    (hz : ∀ x ∈ K, ‖gf F x - proj (insert n A) (gf F x)‖ ≤
      Cz * ‖x - proj (insert n A) x‖ ^ (k - 1))
    (ha : ∀ x ∈ K, μ * ‖proj A x - θ₀‖ ^ 2 -
      Ca * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) * ‖proj A x - θ₀‖ ≤
        ⟪proj A x - θ₀, proj A (gradient F x)⟫)
    {θ : ℝ → Θ ι E} {D : Set ℝ} (hθ : IsMaxFwd (gf F) θ D) {t₀ t : ℝ} (ht₀ : t₀ ∈ D)
    (ht : t ∈ D) (htt : t₀ ≤ t) (hK : ∀ s ∈ Icc t₀ t, θ s ∈ K)
    (hu₀ : ‖‖θ t₀ n‖⁻¹ • θ t₀ n - u₀‖ ≤ r)
    (hη : ‖θ t₀ - proj (insert n A) (θ t₀)‖ ≤ ε₁ * ‖θ t₀ n‖)
    (ha₀ : ‖proj A (θ t₀) - θ₀‖ ≤ ‖θ t₀ n‖) :
    (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (‖θ t₀ n‖ ^ (k - 2))⁻¹ - ((k : ℝ) - 2) * κ * (t - t₀) ∧
    ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
    ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧
    ‖proj A (θ t) - θ₀‖ ≤ ‖θ t₀ n‖ + Ca * (1 + 2 ^ k) / μ * ‖θ t n‖ ^ k := by
  have hsub : Icc t₀ t ⊆ D := hθ.Icc_subset ht₀ ht
  have hθc : ContinuousOn θ (Icc t₀ t) := hθ.continuousOn.mono hsub
  have hθd : ∀ s ∈ Ico t₀ t, HasDerivWithinAt θ (gf F (θ s)) (Ici s) s := fun s hs => by
    have hsD : s ∈ D := hsub (Ico_subset_Icc_self hs)
    exact (hθ.sol s hsD).mono (Ici_subset_Ici.mpr (hθ.nonneg hsD))
  obtain ⟨hρc, hρp, hρd, hρlow, -⟩ := escinv_rho hk hG hpos hD hθ ht₀ ht hK
  have hmono := escinv_mono hk hG hpos hD hκ hθ ht₀ ht hK
  have hρ0 : 0 < ‖θ t₀ n‖ := hρp t₀ ⟨le_rfl, htt⟩
  have hρ0t : ‖θ t₀ n‖ ≤ ‖θ t n‖ := hmono t₀ ⟨le_rfl, htt⟩ t ⟨htt, le_rfl⟩
  -- time bound
  have htime := inv_pow_le_of_deriv_ge hk hρc hρd hρp hρlow t ⟨htt, le_rfl⟩
  refine ⟨htime, ?_⟩
  -- the inactive neurons `z`
  have hk2 : (1 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hzc : ContinuousOn (fun s => θ s - proj (insert n A) (θ s)) (Icc t₀ t) :=
    hθc.sub ((proj (insert n A)).continuous.comp_continuousOn hθc)
  have hzd : ∀ s ∈ Ico t₀ t, HasDerivWithinAt (fun s => θ s - proj (insert n A) (θ s))
      (gf F (θ s) - proj (insert n A) (gf F (θ s))) (Ici s) s :=
    fun s hs => (hθd s hs).sub (escinv_hasDerivWithinAt_clm (hθd s hs) (proj (insert n A)))
  have hT : ((k : ℝ) - 2) * Cz * (t - t₀) * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ^ (k - 2) <
      1 - (2 : ℝ)⁻¹ ^ (k - 2) := by
    set P := ‖θ t₀ n‖ ^ (k - 2) with hP
    have hPpos : 0 < P := pow_pos hρ0 _
    have hρt : 0 < (‖θ t n‖ ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos (hρp t ⟨htt, le_rfl⟩) _)
    set X := ((k : ℝ) - 2) * (t - t₀) with hX
    have hX0 : 0 ≤ X := mul_nonneg (by linarith) (by linarith)
    have h1 : κ * X * P < 1 := by
      have : κ * X < P⁻¹ := by rw [hX]; nlinarith
      calc κ * X * P < P⁻¹ * P := mul_lt_mul_of_pos_right this hPpos
        _ = 1 := inv_mul_cancel₀ hPpos.ne'
    have h2 : ‖θ t₀ - proj (insert n A) (θ t₀)‖ ^ (k - 2) ≤ ε₁ * P := by
      calc ‖θ t₀ - proj (insert n A) (θ t₀)‖ ^ (k - 2) ≤ (ε₁ * ‖θ t₀ n‖) ^ (k - 2) :=
            pow_le_pow_left₀ (norm_nonneg _) hη _
        _ = ε₁ ^ (k - 2) * P := by rw [mul_pow]
        _ ≤ ε₁ * P := by
            gcongr
            exact pow_le_of_le_one hε₁.le hε₁1 (by omega)
    have h3 : (2 : ℝ)⁻¹ ^ (k - 2) ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have h4 : ((k : ℝ) - 2) * Cz * (t - t₀) * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ^ (k - 2) ≤
        Cz * X * (ε₁ * P) := by
      have : ((k : ℝ) - 2) * Cz * (t - t₀) = Cz * X := by rw [hX]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hCz hX0)
    have h5 : Cz * X * (ε₁ * P) ≤ κ / 4 * X * P := by
      have : Cz * X * (ε₁ * P) = (Cz * ε₁) * (X * P) := by ring
      rw [this]
      have : κ / 4 * X * P = (κ / 4) * (X * P) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hε₁z (mul_nonneg hX0 hPpos.le)
    nlinarith
  have hzb := norm_le_two_mul_of_deriv_le_pow hk hCz (norm_nonneg _) htt hzc hzd
    (fun s hs => hz _ (hK s (Ico_subset_Icc_self hs))) le_rfl hT
  refine ⟨hzb t ⟨htt, le_rfl⟩, ?_, ?_⟩
  -- the direction `u`: barrier argument
  · have hwc : ContinuousOn (fun s => θ s n) (Icc t₀ t) :=
      (PiLp.continuous_apply 2 (fun _ : ι => E) n).comp_continuousOn hθc
    have hinvc : ContinuousOn (fun s => ‖θ s n‖⁻¹) (Icc t₀ t) :=
      hρc.inv₀ (fun s hs => (hρp s hs).ne')
    have huc : ContinuousOn (fun s => ‖θ s n‖⁻¹ • θ s n) (Icc t₀ t) := hinvc.smul hwc
    have hfc : ContinuousOn (fun s => ‖‖θ s n‖⁻¹ • θ s n - u₀‖ ^ 2) (Icc t₀ t) :=
      ((huc.sub continuousOn_const).norm).pow 2
    have hfd : ∀ s ∈ Ico t₀ t, HasDerivWithinAt (fun s => ‖‖θ s n‖⁻¹ • θ s n - u₀‖ ^ 2)
        (2 * ⟪‖θ s n‖⁻¹ • θ s n - u₀, ‖θ s n‖ ^ (k - 2) • (G (‖θ s n‖, ‖θ s n‖⁻¹ • θ s n, θ s) -
          ⟪‖θ s n‖⁻¹ • θ s n, G (‖θ s n‖, ‖θ s n‖⁻¹ • θ s n, θ s)⟫ • (‖θ s n‖⁻¹ • θ s n))⟫)
        (Ici s) s := fun s hs =>
      ((escinv_polar_ode hG hk (hθd s hs)
        (norm_pos_iff.mp (hρp s (Ico_subset_Icc_self hs)))).2.sub_const u₀).norm_sq
    have hbd := image_le_of_deriv_right_lt_deriv_boundary' hfc hfd (B := fun _ => r ^ 2)
      (B' := fun _ => 0) (by simpa using pow_le_pow_left₀ (norm_nonneg _) hu₀ 2)
      continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _) (fun s hs heq => by
        have hsK := hK s (Ico_subset_Icc_self hs)
        have hnr : ‖‖θ s n‖⁻¹ • θ s n - u₀‖ = r :=
          (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).mp heq
        have h1 := hbar _ hsK hnr
        have h2 : 0 < ‖θ s n‖ ^ (k - 2) := pow_pos (hρp s (Ico_subset_Icc_self hs)) _
        rw [real_inner_smul_right]
        nlinarith) ⟨htt, le_rfl⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp hbd
  -- the active coordinates `a`: slaving estimate
  · have hec : ContinuousOn (fun s => proj A (θ s) - θ₀) (Icc t₀ t) :=
      ((proj A).continuous.comp_continuousOn hθc).sub continuousOn_const
    have hed : ∀ s ∈ Ico t₀ t, HasDerivWithinAt (fun s => proj A (θ s) - θ₀)
        (proj A (gf F (θ s))) (Ici s) s :=
      fun s hs => (escinv_hasDerivWithinAt_clm (hθd s hs) (proj A)).sub_const θ₀
    set β := Ca * (1 + 2 ^ k) * ‖θ t n‖ ^ k with hβdef
    have hβ : 0 ≤ β := by positivity
    have hbound : ∀ s ∈ Ico t₀ t, ⟪proj A (θ s) - θ₀, proj A (gf F (θ s))⟫ ≤
        -μ * ‖proj A (θ s) - θ₀‖ ^ 2 + β * ‖proj A (θ s) - θ₀‖ := by
      intro s hs
      have hsI := Ico_subset_Icc_self hs
      have hsK := hK s hsI
      have h1 := ha _ hsK
      have h2 : proj A (gf F (θ s)) = -proj A (gradient F (θ s)) := by rw [gf, map_neg]
      rw [h2, inner_neg_right]
      have hρst : ‖θ s n‖ ≤ ‖θ t n‖ := hmono s hsI t ⟨hs.2.le, le_rfl⟩
      have hzs : ‖θ s - proj (insert n A) (θ s)‖ ≤ 2 * ‖θ t n‖ := by
        have e1 := hzb s hsI
        have e2 : ε₁ * ‖θ t₀ n‖ ≤ ‖θ t₀ n‖ := by nlinarith
        linarith
      have hsum : ‖θ s n‖ ^ k + ‖θ s - proj (insert n A) (θ s)‖ ^ k ≤
          (1 + 2 ^ k) * ‖θ t n‖ ^ k := by
        have e1 : ‖θ s n‖ ^ k ≤ ‖θ t n‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hρst k
        have e2 : ‖θ s - proj (insert n A) (θ s)‖ ^ k ≤ (2 * ‖θ t n‖) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hzs k
        rw [mul_pow] at e2
        linarith
      have he := norm_nonneg (proj A (θ s) - θ₀)
      have e3 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hCa he)
      rw [hβdef]
      nlinarith
    have hab := norm_le_of_inner_deriv_le hμ hβ hec hed hbound t ⟨htt, le_rfl⟩
    have hexp : Real.exp (-μ * (t - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hexp0 : 0 ≤ Real.exp (-μ * (t - t₀)) := (Real.exp_pos _).le
    have e1 : Real.exp (-μ * (t - t₀)) * ‖proj A (θ t₀) - θ₀‖ ≤ ‖θ t₀ n‖ := by
      calc Real.exp (-μ * (t - t₀)) * ‖proj A (θ t₀) - θ₀‖ ≤ 1 * ‖θ t₀ n‖ :=
            mul_le_mul hexp ha₀ (norm_nonneg _) zero_le_one
        _ = ‖θ t₀ n‖ := one_mul _
    have e2 : β / μ = Ca * (1 + 2 ^ k) / μ * ‖θ t n‖ ^ k := by rw [hβdef]; ring
    linarith

/-! ### Bootstrap and exit time for one trajectory -/

private lemma escinv_norm_sub {w : E} (u₀ : E) (hw : 0 < ‖w‖) :
    ‖w - ‖w‖ • u₀‖ = ‖w‖ * ‖‖w‖⁻¹ • w - u₀‖ := by
  have : w - ‖w‖ • u₀ = ‖w‖ • (‖w‖⁻¹ • w - u₀) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
  rw [this, norm_smul, Real.norm_of_nonneg (norm_nonneg _)]

/-- The invariance step for one trajectory, given the box estimates and the constants. -/
private lemma escinv_traj {G : ℝ × E × Θ ι E → E} {A : Finset ι} {n : ι} {θ₀ : Θ ι E} {u₀ : E}
    (hk : 3 ≤ k)
    (hG : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    {r ρ₂ ra η₂ κ D₁ Cz μ Ca R C ρ₁ ε₁ : ℝ}
    (hr : 0 < r) (hκ : 0 < κ) (hμ : 0 < μ) (hCz : 0 ≤ Cz) (hCa : 0 ≤ Ca) (hC : 0 < C)
    (hbox : ∀ x : Θ ι E, 0 < ‖x n‖ → ‖x n‖ ≤ ρ₂ → ‖‖x n‖⁻¹ • x n - u₀‖ ≤ 2 * r →
        ‖proj A x - θ₀‖ ≤ ra → ‖x - proj (insert n A) x‖ ≤ η₂ →
        (κ ≤ ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ∧
          ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ≤ D₁) ∧
        (‖‖x n‖⁻¹ • x n - u₀‖ = r →
          ⟪‖x n‖⁻¹ • x n - u₀, G (‖x n‖, ‖x n‖⁻¹ • x n, x) -
            ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ • (‖x n‖⁻¹ • x n)⟫ < 0) ∧
        ‖gf F x - proj (insert n A) (gf F x)‖ ≤ Cz * ‖x - proj (insert n A) x‖ ^ (k - 1) ∧
        μ * ‖proj A x - θ₀‖ ^ 2 - Ca * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) *
          ‖proj A x - θ₀‖ ≤ ⟪proj A x - θ₀, proj A (gradient F x)⟫ ∧
        ‖x‖ ≤ R)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₁η : 2 * ρ₁ ≤ η₂) (hρ₁a : ρ₁ + C * ρ₁ ^ k < ra)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₁z : Cz * ε₁ ≤ κ / 4)
    (hC1 : 1 / (((k : ℝ) - 2) * κ) ≤ C) (hC2 : ((k : ℝ) - 2) * D₁ ≤ C)
    (hC3 : Ca * (1 + 2 ^ k) / μ ≤ C)
    {θ : ℝ → Θ ι E} {D : Set ℝ} (hθ : IsMaxFwd (gf F) θ D) {t₀ : ℝ} (ht₀ : t₀ ∈ D)
    (hesc : EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀)) :
    ∃ t₁ ∈ D, t₀ < t₁ ∧ ‖θ t₁ n‖ = ρ₁ ∧ (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) ∧
      ∀ t ∈ Icc t₀ t₁,
        ‖θ t₀ n‖ ≤ ‖θ t n‖ ∧
        t₁ - t ≤ C * (‖θ t n‖ ^ (k - 2))⁻¹ ∧
        (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁ - t) ∧
        ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
        ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧
        ‖proj A (θ t) - θ₀‖ ≤ ‖θ t₀ n‖ + C * ‖θ t n‖ ^ k := by
  obtain ⟨h0pos, h0lt, hu0, hz0, ha0⟩ := hesc
  have hk2 : (1 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hρ₁k : 0 ≤ C * ρ₁ ^ k := mul_nonneg hC.le (pow_nonneg hρ₁.le _)
  -- the closed region `K` and the smaller region `K'`
  set K : Set (Θ ι E) := {x | ‖θ t₀ n‖ / 2 ≤ ‖x n‖ ∧ ‖x n‖ ≤ ρ₂ ∧
      ‖x n - ‖x n‖ • u₀‖ ≤ 2 * r * ‖x n‖ ∧ ‖proj A x - θ₀‖ ≤ ra ∧
      ‖x - proj (insert n A) x‖ ≤ η₂} with hKdef
  set K' : Set (Θ ι E) := {x | ‖θ t₀ n‖ ≤ ‖x n‖ ∧ ‖x n‖ ≤ ρ₁ ∧
      ‖x n - ‖x n‖ • u₀‖ ≤ r * ‖x n‖ ∧ ‖proj A x - θ₀‖ ≤ ρ₁ + C * ρ₁ ^ k ∧
      ‖x - proj (insert n A) x‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖} with hK'def
  have hcx : Continuous (fun x : Θ ι E => x n) := PiLp.continuous_apply 2 (fun _ : ι => E) n
  have hcn : Continuous (fun x : Θ ι E => ‖x n‖) := hcx.norm
  have hc3 : Continuous (fun x : Θ ι E => ‖x n - ‖x n‖ • u₀‖) :=
    (hcx.sub (hcn.smul continuous_const)).norm
  have hc4 : Continuous (fun x : Θ ι E => ‖proj A x - θ₀‖) :=
    ((proj A).continuous.sub continuous_const).norm
  have hc5 : Continuous (fun x : Θ ι E => ‖x - proj (insert n A) x‖) :=
    (continuous_id.sub (proj (insert n A)).continuous).norm
  have hKc : IsClosed K :=
    (isClosed_le continuous_const hcn).inter ((isClosed_le hcn continuous_const).inter
      ((isClosed_le hc3 (continuous_const.mul hcn)).inter
        ((isClosed_le hc4 continuous_const).inter (isClosed_le hc5 continuous_const))))
  have hK'K : K' ⊆ interior K := by
    intro x hx
    obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
    have hxp : 0 < ‖x n‖ := h0pos.trans_le hx1
    rw [mem_interior_iff_mem_nhds]
    have e1 : ∀ᶠ y in 𝓝 x, ‖θ t₀ n‖ / 2 < ‖y n‖ :=
      continuousAt_const.eventually_lt hcn.continuousAt (by linarith)
    have e2 : ∀ᶠ y in 𝓝 x, ‖y n‖ < ρ₂ :=
      hcn.continuousAt.eventually_lt continuousAt_const (by linarith)
    have e3 : ∀ᶠ y in 𝓝 x, ‖y n - ‖y n‖ • u₀‖ < 2 * r * ‖y n‖ :=
      hc3.continuousAt.eventually_lt (continuous_const.mul hcn).continuousAt (by nlinarith)
    have e4 : ∀ᶠ y in 𝓝 x, ‖proj A y - θ₀‖ < ra :=
      hc4.continuousAt.eventually_lt continuousAt_const (by linarith)
    have e5 : ∀ᶠ y in 𝓝 x, ‖y - proj (insert n A) y‖ < η₂ :=
      hc5.continuousAt.eventually_lt continuousAt_const (by nlinarith)
    filter_upwards [e1, e2, e3, e4, e5] with y h1 h2 h3 h4 h5
    exact ⟨h1.le, h2.le, h3.le, h4.le, h5.le⟩
  have hK'sub : K' ⊆ K := fun x hx => interior_subset (hK'K hx)
  -- the box estimates on `K`
  have hKmem : ∀ x ∈ K, 0 < ‖x n‖ ∧ ‖x n‖ ≤ ρ₂ ∧ ‖‖x n‖⁻¹ • x n - u₀‖ ≤ 2 * r ∧
      ‖proj A x - θ₀‖ ≤ ra ∧ ‖x - proj (insert n A) x‖ ≤ η₂ := by
    intro x hx
    obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
    have hxp : 0 < ‖x n‖ := by linarith
    have hxu : ‖‖x n‖⁻¹ • x n - u₀‖ ≤ 2 * r := by
      rw [escinv_norm_sub u₀ hxp] at hx3
      nlinarith
    exact ⟨hxp, hx2, hxu, hx4, hx5⟩
  have hB := fun x (hx : x ∈ K) => hbox x (hKmem x hx).1 (hKmem x hx).2.1 (hKmem x hx).2.2.1
    (hKmem x hx).2.2.2.1 (hKmem x hx).2.2.2.2
  have hpos : ∀ x ∈ K, 0 < ‖x n‖ := fun x hx => (hKmem x hx).1
  have hD := fun x (hx : x ∈ K) => (hB x hx).1
  have hbar := fun x (hx : x ∈ K) => (hB x hx).2.1
  have hz := fun x (hx : x ∈ K) => (hB x hx).2.2.1
  have ha := fun x (hx : x ∈ K) => (hB x hx).2.2.2.1
  have hR := fun x (hx : x ∈ K) => (hB x hx).2.2.2.2
  -- the starting point lies in `K`
  have hK0 : θ t₀ ∈ K := by
    refine ⟨by linarith, by linarith, ?_, by linarith, ?_⟩
    · rw [escinv_norm_sub u₀ h0pos]; nlinarith
    · have : ε₁ * ‖θ t₀ n‖ ≤ ‖θ t₀ n‖ := by nlinarith
      linarith
  -- bootstrap: as long as `ρ ≤ ρ₁`, the trajectory stays in `K'`
  have hboot : ∀ b ∈ D, t₀ ≤ b → (∀ s ∈ Icc t₀ b, ‖θ s n‖ ≤ ρ₁) → ∀ s ∈ Icc t₀ b, θ s ∈ K' := by
    intro b hb htb hρb
    refine bootstrap (hθ.continuousOn.mono (hθ.Icc_subset ht₀ hb)) hKc hK'K hK0 ?_
    intro t ht hKt
    have htD : t ∈ D := hθ.Icc_subset ht₀ hb ht
    obtain ⟨-, hzt, hut, hat⟩ := escinv_est hk hG hr hκ hμ hCz hCa hε₁ hε₁1 hε₁z hpos hD hbar hz
      ha hθ ht₀ htD ht.1 hKt hu0 hz0 ha0
    have hmono := escinv_mono hk hG hpos hD hκ hθ ht₀ htD hKt
    have hρt0 : ‖θ t₀ n‖ ≤ ‖θ t n‖ := hmono t₀ ⟨le_rfl, ht.1⟩ t ⟨ht.1, le_rfl⟩
    have hρt1 : ‖θ t n‖ ≤ ρ₁ := hρb t ht
    have htp : 0 < ‖θ t n‖ := h0pos.trans_le hρt0
    refine ⟨hρt0, hρt1, ?_, ?_, hzt⟩
    · rw [escinv_norm_sub u₀ htp]; nlinarith
    · have e1 : ‖θ t n‖ ^ k ≤ ρ₁ ^ k := pow_le_pow_left₀ (norm_nonneg _) hρt1 k
      have e2 : Ca * (1 + 2 ^ k) / μ * ‖θ t n‖ ^ k ≤ C * ρ₁ ^ k :=
        mul_le_mul hC3 e1 (pow_nonneg (norm_nonneg _) _) hC.le
      linarith
  -- `ρ` reaches `ρ₁`
  have hex : ∃ t' ∈ D, t₀ ≤ t' ∧ ρ₁ ≤ ‖θ t' n‖ := by
    by_contra hcon'
    have hcon : ∀ t' ∈ D, t₀ ≤ t' → ‖θ t' n‖ < ρ₁ := fun t' ht' h =>
      lt_of_not_ge (fun h' => hcon' ⟨t', ht', h, h'⟩)
    have hm : 0 < ((k : ℝ) - 2) * κ := mul_pos (by linarith) hκ
    have hP : 0 < (‖θ t₀ n‖ ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos h0pos _)
    set T := (‖θ t₀ n‖ ^ (k - 2))⁻¹ / (((k : ℝ) - 2) * κ) with hTdef
    have hT : 0 < T := div_pos hP hm
    have hbd : ∀ b ∈ D, t₀ ≤ b → b < t₀ + T ∧ ‖θ b‖ ≤ R := by
      intro b hb htb
      have hKb : ∀ s ∈ Icc t₀ b, θ s ∈ K := fun s hs => hK'sub (hboot b hb htb
        (fun s' hs' => (hcon s' (hθ.Icc_subset ht₀ hb hs') hs'.1).le) s hs)
      obtain ⟨htime, -⟩ := escinv_est hk hG hr hκ hμ hCz hCa hε₁ hε₁1 hε₁z hpos hD hbar hz
        ha hθ ht₀ hb htb hKb hu0 hz0 ha0
      have hpb : 0 < (‖θ b n‖ ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos (hpos _ (hKb b ⟨htb, le_rfl⟩)) _)
      refine ⟨?_, hR _ (hKb b ⟨htb, le_rfl⟩)⟩
      have : (b - t₀) * (((k : ℝ) - 2) * κ) < (‖θ t₀ n‖ ^ (k - 2))⁻¹ := by nlinarith
      have : b - t₀ < T := by rw [hTdef, lt_div_iff₀ hm]; exact this
      linarith
    have hsubD := hθ.Icc_subset_of_bounded ht₀ (b := t₀ + T) (R := R)
      (fun s hs hsD => (hbd s hsD hs.1).2)
    have hTD : t₀ + T ∈ D := hsubD ⟨by linarith, le_rfl⟩
    exact lt_irrefl _ (hbd _ hTD (by linarith)).1
  -- the exit time `t₁`
  obtain ⟨t', ht'D, ht₀t', hρt'⟩ := hex
  have hρc' : ContinuousOn (fun s => ‖θ s n‖) (Icc t₀ t') :=
    hcn.comp_continuousOn (hθ.continuousOn.mono (hθ.Icc_subset ht₀ ht'D))
  set S := Icc t₀ t' ∩ (fun s => ‖θ s n‖) ⁻¹' Ici ρ₁ with hSdef
  have hSc : IsClosed S := hρc'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨t', ⟨ht₀t', le_rfl⟩, hρt'⟩
  have hSbdd : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
  set t₁ := sInf S with ht₁def
  have ht₁S : t₁ ∈ S := hSc.csInf_mem hSne hSbdd
  have ht₀t₁ : t₀ ≤ t₁ := ht₁S.1.1
  have ht₁t' : t₁ ≤ t' := ht₁S.1.2
  have hρt₁ge : ρ₁ ≤ ‖θ t₁ n‖ := ht₁S.2
  have ht₁D : t₁ ∈ D := hθ.Icc_subset ht₀ ht'D ht₁S.1
  have hbefore : ∀ s ∈ Ico t₀ t₁, ‖θ s n‖ < ρ₁ := by
    intro s hs
    by_contra hcon'
    have hcon : ρ₁ ≤ ‖θ s n‖ := not_lt.mp hcon'
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans ht₁t'⟩, hcon⟩
    have := csInf_le hSbdd hsS
    linarith [hs.2]
  have ht₀lt : t₀ < t₁ := by
    rcases eq_or_lt_of_le ht₀t₁ with h | h
    · rw [← h] at hρt₁ge; linarith
    · exact h
  have hρt₁ : ‖θ t₁ n‖ = ρ₁ := by
    have hc : ContinuousOn (fun s => ‖θ s n‖) (Icc t₀ t₁) :=
      hρc'.mono (Icc_subset_Icc le_rfl ht₁t')
    obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc ht₀t₁ hc ⟨h0lt.le, hρt₁ge⟩
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [← h]; exact hseq
    · exact absurd hseq (hbefore s ⟨hs.1, h⟩).ne
  have hle : ∀ s ∈ Icc t₀ t₁, ‖θ s n‖ ≤ ρ₁ := fun s hs => by
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, hρt₁]
    · exact (hbefore s ⟨hs.1, h⟩).le
  have hKt₁ : ∀ s ∈ Icc t₀ t₁, θ s ∈ K := fun s hs => hK'sub (hboot t₁ ht₁D ht₀t₁ hle s hs)
  refine ⟨t₁, ht₁D, ht₀lt, hρt₁, hbefore, fun t ht => ?_⟩
  have htD : t ∈ D := hθ.Icc_subset ht₀ ht₁D ht
  have hKt : ∀ s ∈ Icc t₀ t, θ s ∈ K := fun s hs => hKt₁ s ⟨hs.1, hs.2.trans ht.2⟩
  obtain ⟨-, hzt, hut, hat⟩ := escinv_est hk hG hr hκ hμ hCz hCa hε₁ hε₁1 hε₁z hpos hD hbar hz
    ha hθ ht₀ htD ht.1 hKt hu0 hz0 ha0
  have hmono := escinv_mono hk hG hpos hD hκ hθ ht₀ ht₁D hKt₁
  obtain ⟨hρc, hρp, hρd, hρlow, hρup⟩ := escinv_rho hk hG hpos hD hθ htD ht₁D
    (fun s hs => hKt₁ s ⟨ht.1.trans hs.1, hs.2⟩)
  have hA := inv_pow_le_of_deriv_ge hk hρc hρd hρp hρlow t₁ ⟨ht.2, le_rfl⟩
  have hB' := inv_pow_ge_of_deriv_le hk hρc hρd hρp hρup t₁ ⟨ht.2, le_rfl⟩
  rw [hρt₁] at hA hB'
  have htt₁ : 0 ≤ t₁ - t := sub_nonneg.mpr ht.2
  refine ⟨hmono t₀ ⟨le_rfl, ht₀t₁⟩ t ⟨ht.1, ht.2⟩, ?_, ?_, hzt, hut, ?_⟩
  · have hm : 0 < ((k : ℝ) - 2) * κ := mul_pos (by linarith) hκ
    have hCm : 1 ≤ C * (((k : ℝ) - 2) * κ) := by
      rw [div_le_iff₀ hm] at hC1; linarith
    have hρ₁p : 0 < (ρ₁ ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos hρ₁ _)
    have h1 : ((k : ℝ) - 2) * κ * (t₁ - t) ≤ (‖θ t n‖ ^ (k - 2))⁻¹ := by linarith
    calc t₁ - t ≤ (C * (((k : ℝ) - 2) * κ)) * (t₁ - t) := le_mul_of_one_le_left htt₁ hCm
      _ = C * (((k : ℝ) - 2) * κ * (t₁ - t)) := by ring
      _ ≤ C * (‖θ t n‖ ^ (k - 2))⁻¹ := mul_le_mul_of_nonneg_left h1 hC.le
  · have h1 : ((k : ℝ) - 2) * D₁ * (t₁ - t) ≤ C * (t₁ - t) :=
      mul_le_mul_of_nonneg_right hC2 htt₁
    linarith
  · have e2 : Ca * (1 + 2 ^ k) / μ * ‖θ t n‖ ^ k ≤ C * ‖θ t n‖ ^ k :=
      mul_le_mul_of_nonneg_right hC3 (pow_nonneg (norm_nonneg _) _)
    linarith

/-! ### Choice of the constants -/

/-- The spherical gradient field `V(u) = ∇U(u) - ⟪u, ∇U(u)⟫ u` has a sink at a non-degenerate
local maximum `u₀` of `U|_{S^{p-1}}` with `U(u₀) > 0`. -/
private lemma escinv_sink {U₀ : E → ℝ} {u₀ : E} (hk : 0 < k)
    (hdiff : DifferentiableAt ℝ (gradient U₀) u₀)
    (hu : IsNondegMaxSphere U₀ k u₀) (hU : 0 < U₀ u₀)
    (heuler : ⟪u₀, gradient U₀ u₀⟫ = k * U₀ u₀)
    (hself : fderiv ℝ (gradient U₀) u₀ u₀ = ((k : ℝ) - 1) • gradient U₀ u₀)
    (hsymm : ∀ v v', ⟪fderiv ℝ (gradient U₀) u₀ v, v'⟫ = ⟪v, fderiv ℝ (gradient U₀) u₀ v'⟫)
    (hhess : ∀ v, ⟪fderiv ℝ (gradient U₀) u₀ v, v⟫ = fderiv ℝ (fderiv ℝ U₀) u₀ v v) :
    ∃ c > 0, ∃ r > 0, ∀ u, ‖u - u₀‖ ≤ r →
      ⟪u - u₀, gradient U₀ u - ⟪u, gradient U₀ u⟫ • u⟫ ≤ -c * ‖u - u₀‖ ^ 2 := by
  set g := gradient U₀ with hgdef
  set M := fderiv ℝ g u₀ with hMdef
  set lam := ⟪u₀, g u₀⟫ with hlamdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 0 < lam := by rw [heuler]; positivity
  have hu1 : ‖u₀‖ = 1 := hu.norm_eq
  have huu : ⟪u₀, u₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu1]; norm_num
  -- `∇U(u₀) = λ u₀`
  have hgu : g u₀ = lam • u₀ := by
    set v := g u₀ - lam • u₀ with hv
    have hvu : ⟪v, u₀⟫ = 0 := by
      rw [hv, inner_sub_left, real_inner_smul_left, huu, real_inner_comm, ← hlamdef]; ring
    have h1 : ⟪g u₀, v⟫ = 0 := by
      rw [hgdef, inner_gradient_E]; exact hu.crit v hvu
    have h2 : ⟪v, v⟫ = 0 := by
      calc ⟪v, v⟫ = ⟪g u₀, v⟫ - lam * ⟪u₀, v⟫ := by
              rw [hv]; rw [inner_sub_left, real_inner_smul_left]
        _ = 0 := by rw [h1, real_inner_comm, hvu]; ring
    have : v = 0 := inner_self_eq_zero.mp h2
    rw [hv] at this
    exact sub_eq_zero.mp this
  have hMu : M u₀ = (((k : ℝ) - 1) * lam) • u₀ := by
    rw [hself, hgu, smul_smul]
  -- the derivative of `V` at `u₀`
  have hg : HasFDerivAt g M u₀ := hdiff.hasFDerivAt
  have hid : HasFDerivAt (fun u : E => u) (ContinuousLinearMap.id ℝ E) u₀ := hasFDerivAt_id u₀
  have hip := hid.inner ℝ hg
  have hsm := hip.smul hid
  have hV := hg.sub hsm
  set H := M - (⟪u₀, g u₀⟫ • ContinuousLinearMap.id ℝ E +
    (fderivInnerCLM ℝ (u₀, g u₀) ∘L (ContinuousLinearMap.id ℝ E).prod M).smulRight u₀) with hH
  have hHv : ∀ v, H v = M v - (lam • v + (⟪u₀, M v⟫ + ⟪v, g u₀⟫) • u₀) := by
    intro v
    simp [hH, fderivInnerCLM_apply, hlamdef]
  -- negative definiteness
  obtain ⟨ch, hch, hhs⟩ := hu.hess
  set c₀ := min ch (2 * lam) with hc₀
  have hc₀pos : 0 < c₀ := lt_min hch (by linarith)
  have hneg : ∀ v, ⟪H v, v⟫ ≤ -c₀ * ‖v‖ ^ 2 := by
    intro v
    set β := ⟪u₀, v⟫ with hβ
    set w := v - β • u₀ with hw
    have hwu : ⟪w, u₀⟫ = 0 := by
      rw [hw, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
    have hu0w : ⟪u₀, w⟫ = 0 := by rw [real_inner_comm]; exact hwu
    have hvw : v = w + β • u₀ := by rw [hw]; abel
    have hMw : ⟪M w, u₀⟫ = 0 := by
      rw [hsymm, hMu, real_inner_smul_right, hwu]; ring
    have hMuw : ⟪M u₀, w⟫ = 0 := by
      rw [hMu, real_inner_smul_left, hu0w]; ring
    have hMuu : ⟪M u₀, u₀⟫ = ((k : ℝ) - 1) * lam := by
      rw [hMu, real_inner_smul_left, huu]; ring
    have hMvv : ⟪M v, v⟫ = ⟪M w, w⟫ + ((k : ℝ) - 1) * lam * β ^ 2 := by
      rw [hvw, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
        hMw, hMuw, hMuu]
      ring
    have hu0Mv : ⟪u₀, M v⟫ = ((k : ℝ) - 1) * lam * β := by
      rw [← hsymm, hMu, real_inner_smul_left]
    have hvg : ⟪v, g u₀⟫ = lam * β := by
      rw [hgu, real_inner_smul_right, real_inner_comm]
    have hnorm : ‖v‖ ^ 2 = ‖w‖ ^ 2 + β ^ 2 := by
      rw [hvw, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_add_left,
        inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right, hwu, hu0w, huu]
      ring
    have hww : ⟪M w, w⟫ ≤ lam * ‖w‖ ^ 2 - ch * ‖w‖ ^ 2 := by
      have := hhs w hwu
      rw [hhess, heuler]; linarith
    have hHvv : ⟪H v, v⟫ = ⟪M v, v⟫ - (lam * ⟪v, v⟫ + (⟪u₀, M v⟫ + ⟪v, g u₀⟫) * β) := by
      rw [hHv, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hHvv, hMvv, hu0Mv, hvg, real_inner_self_eq_norm_sq, hnorm]
    have h1 : c₀ ≤ ch := min_le_left _ _
    have h2 : c₀ ≤ 2 * lam := min_le_right _ _
    nlinarith [sq_nonneg β, sq_nonneg ‖w‖, mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖w‖),
      mul_le_mul_of_nonneg_right h2 (sq_nonneg β)]
  -- little-o estimate
  have hlo := hV.isLittleO.def (half_pos hc₀pos)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hlo
  have hV0 : g u₀ - ⟪u₀, g u₀⟫ • u₀ = 0 := by rw [← hlamdef, hgu, sub_self]
  refine ⟨c₀ / 2, half_pos hc₀pos, ε / 2, half_pos hε, fun u hu => ?_⟩
  have hdist : dist u u₀ < ε := by rw [dist_eq_norm]; linarith
  have hb := hεb hdist
  have hfun : ∀ x : E, ((g - (fun t : E => ⟪t, g t⟫) • fun u : E => u) : E → E) x =
      g x - ⟪x, g x⟫ • x := fun x => rfl
  rw [hfun, hfun, hV0, sub_zero] at hb
  have h1 : ⟪u - u₀, g u - ⟪u, g u⟫ • u⟫ =
      ⟪H (u - u₀), u - u₀⟫ + ⟪u - u₀, g u - ⟪u, g u⟫ • u - H (u - u₀)⟫ := by
    rw [inner_sub_right (u - u₀) (g u - ⟪u, g u⟫ • u) (H (u - u₀)),
      real_inner_comm (H (u - u₀)) (u - u₀)]
    ring
  have h2 : ⟪u - u₀, g u - ⟪u, g u⟫ • u - H (u - u₀)⟫ ≤ ‖u - u₀‖ * (c₀ / 2 * ‖u - u₀‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  rw [h1]
  nlinarith [hneg (u - u₀)]

/-- `ζ_A(θ) ≤ N (|w_n|^k + |z|^k)`. -/
private lemma escinv_zeta_le {A : Finset ι} {n : ι} (x : Θ ι E) :
    zeta k A x ≤ (Fintype.card ι : ℝ) * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) := by
  unfold zeta
  have hz0 : 0 ≤ ‖x - proj (insert n A) x‖ ^ k := pow_nonneg (norm_nonneg _) k
  have hn0 : 0 ≤ ‖x n‖ ^ k := pow_nonneg (norm_nonneg _) k
  calc ∑ m ∈ Aᶜ, ‖x m‖ ^ k ≤ ∑ m ∈ Aᶜ, (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) := by
        apply Finset.sum_le_sum
        intro m hm
        by_cases hmn : m = n
        · rw [hmn]; linarith
        · have hmA' : m ∉ insert n A := by
            rw [Finset.mem_insert, not_or]; exact ⟨hmn, Finset.mem_compl.mp hm⟩
          have e1 : ‖x m‖ ^ k ≤ ‖x - proj (insert n A) x‖ ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_norm_sub_proj hmA' x) k
          linarith
    _ = (Aᶜ.card : ℝ) * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : ℝ) * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) := by
        gcongr
        exact_mod_cast Finset.card_le_univ _

/-- Lemma 1(a) for the inactive neurons: `|∇_z F| ≤ N C |z|^{k-1}`. -/
private lemma escinv_gf_sub_le {B : Finset ι} {Cg R : ℝ} (hCg : 0 ≤ Cg)
    (hgal : ∀ (m : ι) (θ : Θ ι E), ‖θ‖ ≤ R → ‖(gradient F θ) m‖ ≤ Cg * ‖θ m‖ ^ (k - 1))
    {x : Θ ι E} (hxR : ‖x‖ ≤ R) :
    ‖gf F x - proj B (gf F x)‖ ≤ (Fintype.card ι : ℝ) * Cg * ‖x - proj B x‖ ^ (k - 1) := by
  set N := (Fintype.card ι : ℝ) with hNdef
  have hz0 : 0 ≤ Cg * ‖x - proj B x‖ ^ (k - 1) := mul_nonneg hCg (pow_nonneg (norm_nonneg _) _)
  have hcomp : ∀ m, ‖(gf F x - proj B (gf F x)) m‖ ≤ Cg * ‖x - proj B x‖ ^ (k - 1) := by
    intro m
    by_cases hm : m ∈ B
    · have : (gf F x - proj B (gf F x)) m = 0 := by
        rw [PiLp.sub_apply, proj_apply]; simp only [hm, ↓reduceIte, sub_self]
      rw [this, norm_zero]; exact hz0
    · have : (gf F x - proj B (gf F x)) m = -(gradient F x) m := by
        rw [PiLp.sub_apply, proj_apply]
        simp only [hm, ↓reduceIte, sub_zero]
        rw [gf, PiLp.neg_apply]
      rw [this, norm_neg]
      have hxm : ‖x m‖ ≤ ‖x - proj B x‖ := norm_apply_le_norm_sub_proj hm x
      calc ‖(gradient F x) m‖ ≤ Cg * ‖x m‖ ^ (k - 1) := hgal m x hxR
        _ ≤ Cg * ‖x - proj B x‖ ^ (k - 1) := by gcongr
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : gf F x - proj B (gf F x) = 0 := by ext m; exact (IsEmpty.false m).elim
    rw [this, norm_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCg) (pow_nonneg (norm_nonneg _) _)
  have hN1 : 1 ≤ N := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    rw [hNdef]; exact_mod_cast this
  have hsq : ‖gf F x - proj B (gf F x)‖ ^ 2 ≤ (N * Cg * ‖x - proj B x‖ ^ (k - 1)) ^ 2 := by
    rw [norm_sq_eq_sum]
    calc ∑ m, ‖(gf F x - proj B (gf F x)) m‖ ^ 2
        ≤ ∑ _m : ι, (Cg * ‖x - proj B x‖ ^ (k - 1)) ^ 2 := by
          apply Finset.sum_le_sum
          intro m _
          exact pow_le_pow_left₀ (norm_nonneg _) (hcomp m) 2
      _ = N * (Cg * ‖x - proj B x‖ ^ (k - 1)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ N ^ 2 * (Cg * ‖x - proj B x‖ ^ (k - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hN1 two_ne_zero) (sq_nonneg _)
      _ = (N * Cg * ‖x - proj B x‖ ^ (k - 1)) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) hCg) (pow_nonneg (norm_nonneg _) _)) two_ne_zero).mp hsq

/-- Strong convexity of `F_A` plus Lemma 1(b): the drift of the active coordinates. -/
private lemma escinv_active {A : Finset ι} {n : ι} {θ₀ : Θ ι E} {μ rm Cp R : ℝ}
    (hθ₀ : θ₀ ∈ S A) (hgrad0 : gradient F θ₀ = 0) (hrm : 0 < rm) (hCp : 0 ≤ Cp)
    (hsm : ∀ x y : Θ ι E, x ∈ closedBall θ₀ rm → y ∈ closedBall θ₀ rm →
      x - y ∈ S A → μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, gradient F x - gradient F y⟫)
    (hpgl : ∀ θ : Θ ι E, ‖θ‖ ≤ R →
      ‖proj A (gradient F θ) - proj A (gradient F (proj A θ))‖ ≤ Cp * zeta k A θ)
    {x : Θ ι E} (hxR : ‖x‖ ≤ R) (hxa : ‖proj A x - θ₀‖ ≤ rm) :
    μ * ‖proj A x - θ₀‖ ^ 2 - Cp * (Fintype.card ι : ℝ) *
      (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) * ‖proj A x - θ₀‖ ≤
        ⟪proj A x - θ₀, proj A (gradient F x)⟫ := by
  set e := proj A x - θ₀ with hedef
  set Z := ‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k with hZdef
  set d := proj A (gradient F x) - proj A (gradient F (proj A x)) with hddef
  have he : e ∈ S A := S_sub (proj_mem_S A x) hθ₀
  have hpx : proj A x ∈ closedBall θ₀ rm := by rw [mem_closedBall, dist_eq_norm]; exact hxa
  have h1 := hsm (proj A x) θ₀ hpx (mem_closedBall_self hrm.le) he
  rw [hgrad0, sub_zero] at h1
  have h2 : ⟪e, proj A (gradient F (proj A x))⟫ = ⟪e, gradient F (proj A x)⟫ :=
    inner_proj_eq_of_mem_S he _
  have hzeta : zeta k A x ≤ (Fintype.card ι : ℝ) * Z := escinv_zeta_le x
  have e2 : ‖d‖ ≤ Cp * ((Fintype.card ι : ℝ) * Z) :=
    (hpgl x hxR).trans (mul_le_mul_of_nonneg_left hzeta hCp)
  have e3 : ‖e‖ * ‖d‖ ≤ ‖e‖ * (Cp * ((Fintype.card ι : ℝ) * Z)) :=
    mul_le_mul_of_nonneg_left e2 (norm_nonneg e)
  have e1 := abs_real_inner_le_norm e d
  have e4 := neg_abs_le ⟪e, d⟫
  have hsplit : ⟪e, proj A (gradient F x)⟫ = ⟪e, proj A (gradient F (proj A x))⟫ + ⟪e, d⟫ := by
    rw [hddef, inner_sub_right]; ring
  rw [hsplit, h2]
  have : Cp * (Fintype.card ι : ℝ) * Z * ‖e‖ = ‖e‖ * (Cp * ((Fintype.card ι : ℝ) * Z)) := by ring
  linarith


/-- Choice of the constants and of the box around `(ρ, u, a, z) = (0, u₀, θ₀, 0)` on which the
estimates of the invariance step hold: first `r`, then the box radii (`ρ₂ = r_a = η₂`). -/
private lemma escinv_box (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
    {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι} (hn : n ∉ A) {u₀ : E}
    (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀)
    {G : ℝ × E × Θ ι E → E} (hGc : ContDiff ℝ ∞ G)
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u)
    (hGz : ∀ ρ u θ, G (ρ, u, θ) = G (ρ, u, zeroAt n θ)) :
    ∃ κ > 0, ∃ D₁ > 0, ∃ μ > 0, ∃ Ca ≥ 0, ∃ Cz ≥ 0, ∃ R : ℝ, ∃ rB > 0, ∀ r ∈ Ioc 0 rB,
      ∃ ρ₂ > 0, ∃ ra > 0, ∃ η₂ > 0,
      ∀ x : Θ ι E, 0 < ‖x n‖ → ‖x n‖ ≤ ρ₂ → ‖‖x n‖⁻¹ • x n - u₀‖ ≤ 2 * r →
        ‖proj A x - θ₀‖ ≤ ra → ‖x - proj (insert n A) x‖ ≤ η₂ →
        (κ ≤ ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ∧
          ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ ≤ D₁) ∧
        (‖‖x n‖⁻¹ • x n - u₀‖ = r →
          ⟪‖x n‖⁻¹ • x n - u₀, G (‖x n‖, ‖x n‖⁻¹ • x n, x) -
            ⟪‖x n‖⁻¹ • x n, G (‖x n‖, ‖x n‖⁻¹ • x n, x)⟫ • (‖x n‖⁻¹ • x n)⟫ < 0) ∧
        ‖gf F x - proj (insert n A) (gf F x)‖ ≤ Cz * ‖x - proj (insert n A) x‖ ^ (k - 1) ∧
        μ * ‖proj A x - θ₀‖ ^ 2 - Ca * (‖x n‖ ^ k + ‖x - proj (insert n A) x‖ ^ k) *
          ‖proj A x - θ₀‖ ≤ ⟪proj A x - θ₀, proj A (gradient F x)⟫ ∧
        ‖x‖ ≤ R := by
  have hk0 : 0 < k := by omega
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set U₀ := U F k n θ₀ with hU₀def
  set lam := (k : ℝ) * U₀ u₀ with hlamdef
  have hlam : 0 < lam := by positivity
  -- smoothness of `∇U₀`
  have hgU : gradient U₀ = fun u => G (0, u, θ₀) := by funext u; rw [hG0]
  have hgUc : ContDiff ℝ ∞ (gradient U₀) := by
    rw [hgU]; exact hGc.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  -- the sink
  obtain ⟨cs, hcs, rs, hrs, hsink⟩ := escinv_sink hk0
    (hgUc.differentiable (by simp) u₀) hu hU (euler n θ₀ u₀) (hessU_self hk n θ₀ u₀)
    (hessU_symm n θ₀ u₀) (fun v => inner_fderiv_gradU n θ₀ u₀ v v)
  -- continuity of `k U₀` at `u₀`
  have hUc : Continuous U₀ := (U_contDiff n θ₀).continuous
  have hev : ∀ᶠ u in 𝓝 u₀, dist ((k : ℝ) * U₀ u) lam < lam / 4 :=
    Metric.tendsto_nhds.mp ((continuous_const.mul hUc).tendsto u₀) _ (by positivity)
  obtain ⟨δu, hδu, hδub⟩ := Metric.eventually_nhds_iff.mp hev
  -- Lipschitz bound for `G` near `(0, u₀, θ₀)`
  obtain ⟨L, hL⟩ := (hGc.contDiffOn (s := closedBall ((0 : ℝ), u₀, θ₀) 1)).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ 1) (isCompact_closedBall _ 1)
  have hGlip : ∀ (ρ : ℝ) (u : E) (θ' : Θ ι E), |ρ| ≤ 1 → ‖u - u₀‖ ≤ 1 → ‖θ' - θ₀‖ ≤ 1 →
      ‖G (ρ, u, θ') - G (0, u, θ₀)‖ ≤ L * (|ρ| + ‖θ' - θ₀‖) := by
    intro ρ u θ' h1 h2 h3
    have hm1 : (ρ, u, θ') ∈ closedBall ((0 : ℝ), u₀, θ₀) 1 := by
      rw [mem_closedBall, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, dist_eq_norm, dist_eq_norm,
        sub_zero]
      exact max_le h1 (max_le h2 h3)
    have hm2 : ((0 : ℝ), u, θ₀) ∈ closedBall ((0 : ℝ), u₀, θ₀) 1 := by
      rw [mem_closedBall, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, dist_eq_norm, dist_eq_norm,
        sub_self, sub_self, abs_zero, norm_zero]
      exact max_le zero_le_one (max_le h2 zero_le_one)
    have h4 := hL.dist_le_mul _ hm1 _ hm2
    rw [dist_eq_norm] at h4
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero, sub_self,
      norm_zero]
    exact max_le (by linarith [norm_nonneg (θ' - θ₀)])
      (max_le (by positivity) (by linarith [abs_nonneg ρ]))
  -- active coordinates: strong monotonicity and Lemma 1(b)
  obtain ⟨μ, rm, hμ, hrm, hsm⟩ := strong_mono hF hmin
  have hgrad0 : gradient F θ₀ = 0 := gradient_eq_zero_of_isNondegMin hF hk hH hmin
  obtain ⟨Cg, hCg, hgal⟩ := grad_apply_le hF hk hH (‖θ₀‖ + 1)
  obtain ⟨Cp, hCp, hpgl⟩ := proj_grad_sub_proj_le hF hk hH A (‖θ₀‖ + 1)
  set N := (Fintype.card ι : ℝ) with hNdef
  have hN1 : 1 ≤ N := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨n⟩
    rw [hNdef]; exact_mod_cast this
  refine ⟨lam / 2, by positivity, 2 * lam, by positivity, μ, hμ, Cp * N, by positivity,
    N * Cg, by positivity, ‖θ₀‖ + 1, min rs (min (δu / 4) (1 / 4)), by positivity,
    fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hrs' : r ≤ rs := hr.2.trans (min_le_left _ _)
  have hrδ : r ≤ δu / 4 := hr.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr14 : r ≤ 1 / 4 := hr.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set s := min (1 / 3) (min (lam / (12 * ((L : ℝ) + 1)))
    (min (cs * r / (24 * ((L : ℝ) + 1))) rm)) with hsdef
  have hs : 0 < s := by positivity
  have hs13 : s ≤ 1 / 3 := min_le_left _ _
  have hsL1 : s * (12 * ((L : ℝ) + 1)) ≤ lam :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hsL2 : s * (24 * ((L : ℝ) + 1)) ≤ cs * r := (le_div_iff₀ (by positivity)).mp
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsrm : s ≤ rm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨s, hs, s, hs, s, hs, fun x hx0 hx1 hx2 hx3 hx4 => ?_⟩
  -- bound on `‖x‖`
  have hxR : ‖x‖ ≤ ‖θ₀‖ + 1 := by
    have h1 : ‖proj A x‖ ≤ ‖θ₀‖ + s := by
      have := norm_sub_norm_le (proj A x) θ₀
      linarith
    have h2 := decomp hn x
    have h3 : ‖x‖ ≤ ‖proj A x‖ + ‖x n‖ + ‖x - proj (insert n A) x‖ := by
      calc ‖x‖ = ‖proj A x + single n (x n) + (x - proj (insert n A) x)‖ := by rw [← h2]
        _ ≤ ‖proj A x + single n (x n)‖ + ‖x - proj (insert n A) x‖ := norm_add_le _ _
        _ ≤ ‖proj A x‖ + ‖single n (x n)‖ + ‖x - proj (insert n A) x‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖proj A x‖ + ‖x n‖ + ‖x - proj (insert n A) x‖ := by rw [norm_single]
    linarith
  have hP3 := escinv_gf_sub_le (B := insert n A) hCg hgal hxR
  have hP4 := escinv_active (n := n) (k := k) hmin.mem hgrad0 hrm hCp hsm hpgl hxR (by linarith)
  -- polar quantities and the deviation `Δ` of `G` from `∇U₀`
  set ρ := ‖x n‖ with hρdef
  set u := ρ⁻¹ • x n with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
  have hx' : ‖zeroAt n x - θ₀‖ ≤ 2 * s := by
    rw [zeroAt_eq_proj_add hn x]
    calc ‖proj A x + (x - proj (insert n A) x) - θ₀‖
        = ‖(proj A x - θ₀) + (x - proj (insert n A) x)‖ := by congr 1; abel
      _ ≤ ‖proj A x - θ₀‖ + ‖x - proj (insert n A) x‖ := norm_add_le _ _
      _ ≤ 2 * s := by linarith
  set Δ := G (ρ, u, x) - G (0, u, θ₀) with hΔdef
  have hΔ : ‖Δ‖ ≤ L * (3 * s) := by
    rw [hΔdef, hGz ρ u x]
    have h1 := hGlip ρ u (zeroAt n x) (by rw [abs_of_pos hx0]; linarith) (by linarith)
      (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hL0)
    rw [abs_of_pos hx0]; linarith
  have hGx : G (ρ, u, x) = gradient U₀ u + Δ := by rw [hΔdef, hG0 u θ₀]; abel
  have huΔ : |⟪u, Δ⟫| ≤ ‖Δ‖ := by
    have := abs_real_inner_le_norm u Δ
    rwa [hu1, one_mul] at this
  have hLs : (L : ℝ) * (3 * s) ≤ lam / 4 := by nlinarith
  have hΔs : ‖Δ‖ ≤ lam / 4 := hΔ.trans hLs
  refine ⟨?_, ?_, hP3, hP4, hxR⟩
  -- `κ ≤ D ≤ D₁`
  · have hDx : ⟪u, G (ρ, u, x)⟫ = (k : ℝ) * U₀ u + ⟪u, Δ⟫ := by
      rw [hGx, inner_add_right, euler]
    have hUu : |(k : ℝ) * U₀ u - lam| < lam / 4 := by
      have := hδub (show dist u u₀ < δu by rw [dist_eq_norm]; linarith)
      rwa [Real.dist_eq] at this
    have e1 := abs_lt.mp hUu
    have e2 := abs_le.mp (huΔ.trans hΔs)
    rw [hDx]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  -- the barrier on `{‖u - u₀‖ = r}`
  · intro hur
    have hdecomp : G (ρ, u, x) - ⟪u, G (ρ, u, x)⟫ • u =
        (gradient U₀ u - ⟪u, gradient U₀ u⟫ • u) + (Δ - ⟪u, Δ⟫ • u) := by
      rw [hGx, inner_add_right, add_smul]; abel
    rw [hdecomp, inner_add_right]
    have h1 := hsink u (by rw [hur]; exact hrs')
    have e2 : ‖Δ - ⟪u, Δ⟫ • u‖ ≤ 2 * ‖Δ‖ := by
      calc ‖Δ - ⟪u, Δ⟫ • u‖ ≤ ‖Δ‖ + ‖⟪u, Δ⟫ • u‖ := norm_sub_le _ _
        _ = ‖Δ‖ + |⟪u, Δ⟫| := by rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
        _ ≤ 2 * ‖Δ‖ := by linarith
    have h2 : ⟪u - u₀, Δ - ⟪u, Δ⟫ • u⟫ ≤ r * (2 * ‖Δ‖) := by
      have e1 := real_inner_le_norm (u - u₀) (Δ - ⟪u, Δ⟫ • u)
      rw [hur] at e1
      calc _ ≤ r * ‖Δ - ⟪u, Δ⟫ • u‖ := e1
        _ ≤ r * (2 * ‖Δ‖) := mul_le_mul_of_nonneg_left e2 hr0.le
    rw [hur] at h1
    have hLs2 : (L : ℝ) * (6 * s) ≤ cs * r / 4 := by nlinarith
    have h3 : 2 * ‖Δ‖ ≤ cs * r / 4 := by linarith
    have h4 : r * (2 * ‖Δ‖) ≤ r * (cs * r / 4) := mul_le_mul_of_nonneg_left h3 hr0.le
    have h5 : 0 < cs * r ^ 2 := by positivity
    have h6 : r * (cs * r / 4) = cs * r ^ 2 / 4 := by ring
    linarith

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

/-- The invariance step of the proof of Lemma 3. -/
theorem escape_invariance {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι}
    (hn : n ∉ A) {u₀ : E} (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀) :
    ∃ rB > 0, ∀ r ∈ Ioc 0 rB, ∃ ρB > 0, ∃ εB > 0, ∃ C > 0, ∀ ρ₁ ∈ Ioc 0 ρB, ∀ ε₁ ∈ Ioc 0 εB,
      ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D → ∀ t₀ ∈ D,
        EscHyp A n θ₀ u₀ ρ₁ r ε₁ (θ t₀) →
        ∃ t₁ ∈ D, t₀ < t₁ ∧ ‖θ t₁ n‖ = ρ₁ ∧ (∀ t ∈ Ico t₀ t₁, ‖θ t n‖ < ρ₁) ∧
          ∀ t ∈ Icc t₀ t₁,
            ‖θ t₀ n‖ ≤ ‖θ t n‖ ∧
            t₁ - t ≤ C * (‖θ t n‖ ^ (k - 2))⁻¹ ∧
            (‖θ t n‖ ^ (k - 2))⁻¹ ≤ (ρ₁ ^ (k - 2))⁻¹ + C * (t₁ - t) ∧
            ‖θ t - proj (insert n A) (θ t)‖ ≤ 2 * ‖θ t₀ - proj (insert n A) (θ t₀)‖ ∧
            ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧
            ‖proj A (θ t) - θ₀‖ ≤ ‖θ t₀ n‖ + C * ‖θ t n‖ ^ k := by
  obtain ⟨G, hGc, hG, hG0, hGz⟩ := exists_polar hF hk hH n
  obtain ⟨κ, hκ, D₁, -, μ, hμ, Ca, hCa, Cz, hCz, R, rB, hrB, hbox⟩ :=
    escinv_box hF hk hH hmin hn hu hU hGc hG0 hGz
  refine ⟨rB, hrB, fun r hr => ?_⟩
  obtain ⟨ρ₂, hρ₂, ra, hra, η₂, hη₂, hb⟩ := hbox r hr
  have hk2 : (1 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set C := max (max (1 / (((k : ℝ) - 2) * κ)) (((k : ℝ) - 2) * D₁))
    (max (Ca * (1 + 2 ^ k) / μ) 1) with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC1 : 1 / (((k : ℝ) - 2) * κ) ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : ((k : ℝ) - 2) * D₁ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : Ca * (1 + 2 ^ k) / μ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨min (min (ρ₂ / 2) (η₂ / 2)) (min (ra / (2 * (1 + C))) 1), by positivity,
    min 1 (κ / (4 * Cz + 1)), by positivity, C, hC,
    fun ρ₁ hρ₁ ε₁ hε₁ θ D hθ t₀ ht₀ hesc => ?_⟩
  have hρ₁0 : 0 < ρ₁ := hρ₁.1
  have hρ₁a2 : ρ₁ ≤ ρ₂ / 2 := hρ₁.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρ₁b : ρ₁ ≤ η₂ / 2 := hρ₁.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ₁c : ρ₁ ≤ ra / (2 * (1 + C)) :=
    hρ₁.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ₁d : ρ₁ ≤ 1 := hρ₁.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₁0 : 0 < ε₁ := hε₁.1
  have hε₁1 : ε₁ ≤ 1 := hε₁.2.trans (min_le_left _ _)
  have hε₁2 : ε₁ ≤ κ / (4 * Cz + 1) := hε₁.2.trans (min_le_right _ _)
  have hρ₁₂ : ρ₁ < ρ₂ := by linarith
  have hρ₁η : 2 * ρ₁ ≤ η₂ := by linarith
  have hρ₁a : ρ₁ + C * ρ₁ ^ k < ra := by
    have e1 : ρ₁ ^ k ≤ ρ₁ := pow_le_of_le_one hρ₁0.le hρ₁d (by omega)
    have e2 : ρ₁ * (2 * (1 + C)) ≤ ra := (le_div_iff₀ (by positivity)).mp hρ₁c
    have e3 : C * ρ₁ ^ k ≤ C * ρ₁ := mul_le_mul_of_nonneg_left e1 hC.le
    nlinarith
  have hε₁z : Cz * ε₁ ≤ κ / 4 := by
    have e1 : ε₁ * (4 * Cz + 1) ≤ κ := (le_div_iff₀ (by positivity)).mp hε₁2
    nlinarith
  exact escinv_traj hk hG hr.1 hκ hμ hCz hCa hC hb hρ₁0 hρ₁₂ hρ₁η hρ₁a hε₁0 hε₁1 hε₁z hC1 hC2
    hC3 hθ ht₀ hesc

end S2S
