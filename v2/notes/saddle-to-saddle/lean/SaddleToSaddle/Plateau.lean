import SaddleToSaddle.GradFlow

/-!
# Lemma 2 (Plateau)

Near a non-degenerate local minimum `θ₀` of `F_A`, the active coordinates relax exponentially
fast to `θ₀`, up to an error `C₀ ζ_A`, and each inactive weight `w_n = O(α)` evolves on the slow
time scale `α^{2-k}` by `ẇ_n ≈ ∇U_n(θ₀; w_n)`.

`plateau_active` is the first estimate of Lemma 2 for a single trajectory. `plateau` is the
lemma itself, in a quantitative form: the limit `α → 0` is replaced by explicit error bounds,
uniform in the trajectory, from which the statement of the note follows (see `Main.lean`).
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- The conclusion of Lemma 2 (Plateau), in quantitative form, for given constants `r₀, μ`.
Let `Ξ_i`, `i ∉ A`, solve `Ξ_i' = ∇U_i(θ₀; Ξ_i)` on `[σ₀, σ₁]`. If at time `τ` the active
coordinates are `r₀`-close to `θ₀` and the rescaled inactive weights `α⁻¹ w_i(τ)` are `δ₀`-close
to `Ξ_i(σ₀)`, then the maximal trajectory is defined on `[τ, τ + α^{2-k}(σ₁ - σ₀)]`, the rescaled
inactive weights follow `Ξ_i` up to `K (δ₀ + α)`, and the active coordinates satisfy the
exponential bound with error `K α^k`. -/
def PlateauProp (F : Θ ι E → ℝ) (k : ℕ) (A : Finset ι) (θ₀ : Θ ι E) (r₀ μ : ℝ) : Prop :=
  0 < r₀ ∧ 0 < μ ∧
    ∀ (σ₀ σ₁ : ℝ) (Ξ : ι → ℝ → E), σ₀ < σ₁ →
      (∀ i ∉ A, ∀ σ ∈ Icc σ₀ σ₁,
        HasDerivWithinAt (Ξ i) (gradient (U F k i θ₀) (Ξ i σ)) (Icc σ₀ σ₁) σ) →
      ∃ α₁ δ₁ K : ℝ, 0 < α₁ ∧ 0 < δ₁ ∧ 0 < K ∧
        ∀ α ∈ Ioc 0 α₁, ∀ (θ : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ D →
        ∀ τ ∈ D, ∀ δ₀ ∈ Icc 0 δ₁,
          ‖proj A (θ τ) - θ₀‖ ≤ r₀ → (∀ i ∉ A, ‖α⁻¹ • θ τ i - Ξ i σ₀‖ ≤ δ₀) →
          Icc τ (τ + (α ^ (k - 2))⁻¹ * (σ₁ - σ₀)) ⊆ D ∧
          (∀ σ ∈ Icc σ₀ σ₁, ∀ i ∉ A,
            ‖α⁻¹ • θ (τ + (α ^ (k - 2))⁻¹ * (σ - σ₀)) i - Ξ i σ‖ ≤ K * (δ₀ + α)) ∧
          (∀ t ∈ Icc τ (τ + (α ^ (k - 2))⁻¹ * (σ₁ - σ₀)),
            ‖proj A (θ t) - θ₀‖ ≤
              Real.exp (-μ * (t - τ)) * ‖proj A (θ τ) - θ₀‖ + K * α ^ k)

/-! ### Auxiliary lemmas -/

private lemma hasDerivWithinAt_Ici_of_Icc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ → X} {f' : X} {a b t : ℝ} (h : HasDerivWithinAt f f' (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- A vector of `Θ` whose components are bounded by `c` has norm at most `card ι * c`. -/
private lemma norm_le_card_mul {x : Θ ι E} {c : ℝ} (hc : 0 ≤ c) (h : ∀ m, ‖x m‖ ≤ c) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * c := by
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h1 : ‖x‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * c) ^ 2 := by
    rw [norm_sq_eq_sum]
    calc ∑ m, ‖x m‖ ^ 2 ≤ ∑ _m : ι, c ^ 2 :=
          Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (h m) 2
      _ = (Fintype.card ι : ℝ) * c ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Fintype.card ι : ℝ) * c) ^ 2 := by
          rw [mul_pow]
          gcongr
          rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h0
            nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hN hc) two_ne_zero).mp h1

/-- The components of `θ - π_A θ` vanish on `A` and equal those of `θ` outside `A`. -/
private lemma norm_sub_proj_le_card_mul {A : Finset ι} {θ : Θ ι E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ m ∉ A, ‖θ m‖ ≤ c) : ‖θ - proj A θ‖ ≤ (Fintype.card ι : ℝ) * c := by
  refine norm_le_card_mul hc fun m => ?_
  by_cases hm : m ∈ A
  · simp [proj_apply, hm, hc]
  · simpa [proj_apply, hm] using h m hm

private lemma zeta_le_card_mul {A : Finset ι} {θ : Θ ι E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ m ∉ A, ‖θ m‖ ≤ c) : zeta k A θ ≤ (Fintype.card ι : ℝ) * c ^ k := by
  unfold zeta
  calc ∑ m ∈ Aᶜ, ‖θ m‖ ^ k ≤ ∑ _m ∈ Aᶜ, c ^ k :=
        Finset.sum_le_sum fun m hm =>
          pow_le_pow_left₀ (norm_nonneg _) (h m (Finset.mem_compl.mp hm)) k
    _ = (Aᶜ.card : ℝ) * c ^ k := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : ℝ) * c ^ k := by
        gcongr
        exact_mod_cast Finset.card_le_univ _

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

/-- Lemma 2, active coordinates: `|π_A θ(t) - θ₀| ≤ e^{-μ(t-a)} |π_A θ(a) - θ₀| + C₀ Z` as long
as `ζ_A(θ) ≤ Z ≤ r₀`. -/
theorem plateau_active {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) :
    ∃ r₀ C₀ μ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ 0 < C₀ ∧ 0 < μ ∧
      ∀ (θ : ℝ → Θ ι E) (a b Z : ℝ), a ≤ b →
        (∀ t ∈ Icc a b, HasDerivWithinAt θ (gf F (θ t)) (Icc a b) t) →
        ‖proj A (θ a) - θ₀‖ ≤ r₀ → Z ≤ r₀ → (∀ t ∈ Icc a b, zeta k A (θ t) ≤ Z) →
        ∀ t ∈ Icc a b,
          ‖proj A (θ t) - θ₀‖ ≤ Real.exp (-μ * (t - a)) * ‖proj A (θ a) - θ₀‖ + C₀ * Z := by
  obtain ⟨μ, r, hμ, hr, hmono⟩ := strong_mono hF hmin
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨C, hC0, hC⟩ := proj_grad_sub_proj_le hF hk hH A (‖θ₀‖ + r + N)
  have hgrad0 : gradient F θ₀ = 0 := gradient_eq_zero_of_isNondegMin hF hk hH hmin
  set C₀ : ℝ := (C + 1) / μ with hC₀
  have hC₀pos : 0 < C₀ := div_pos (by linarith) hμ
  set r₀ : ℝ := min (1 / 2) (r / (2 * (1 + C₀))) with hr₀
  have hr₀pos : 0 < r₀ := lt_min (by norm_num) (div_pos hr (by positivity))
  have hr₀lt1 : r₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hr₀C : r₀ + C₀ * r₀ < r := by
    have h1 : r₀ ≤ r / (2 * (1 + C₀)) := min_le_right _ _
    have h2 : r₀ * (1 + C₀) ≤ r / 2 := by
      calc r₀ * (1 + C₀) ≤ r / (2 * (1 + C₀)) * (1 + C₀) := by gcongr
        _ = r / 2 := by field_simp
    nlinarith
  refine ⟨r₀, C₀, μ, hr₀pos, hr₀lt1, hC₀pos, hμ, ?_⟩
  intro θ a b Z hab hθ ha hZ hζ
  have hZ0 : 0 ≤ Z := (zeta_nonneg k A (θ a)).trans (hζ a ⟨le_rfl, hab⟩)
  have hθ₀S : θ₀ ∈ S A := hmin.mem
  -- inactive components are bounded by `1`
  have hinact : ∀ t ∈ Icc a b, ∀ m ∉ A, ‖θ t m‖ ≤ 1 := by
    intro t ht m hm
    have h1 : ‖θ t m‖ ^ k ≤ zeta k A (θ t) := by
      unfold zeta
      exact Finset.single_le_sum (f := fun m => ‖θ t m‖ ^ k)
        (fun _ _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_compl.mpr hm)
    have h2 : ‖θ t m‖ ^ k ≤ 1 := by linarith [hζ t ht]
    by_contra hcon
    push_neg at hcon
    have : 1 < ‖θ t m‖ ^ k := one_lt_pow₀ hcon (by omega)
    linarith
  have hsub : ∀ t ∈ Icc a b, ‖θ t - proj A (θ t)‖ ≤ N := by
    intro t ht
    simpa using norm_sub_proj_le_card_mul zero_le_one (hinact t ht)
  -- the derivative of `proj A ∘ θ`
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => proj A (θ t) - θ₀) (proj A (gf F (θ t))) (Icc a b) t := by
    intro t ht
    have := ((proj A : Θ ι E →L[ℝ] Θ ι E).hasFDerivAt.comp_hasDerivWithinAt t (hθ t ht))
    simpa using this.sub_const θ₀
  have hcont : ContinuousOn (fun t => proj A (θ t) - θ₀) (Icc a b) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  -- the key differential inequality, valid while `‖π_A θ - θ₀‖ ≤ r`
  have hkey : ∀ t ∈ Icc a b, ‖proj A (θ t) - θ₀‖ ≤ r →
      ⟪proj A (θ t) - θ₀, proj A (gf F (θ t))⟫ ≤
        -μ * ‖proj A (θ t) - θ₀‖ ^ 2 + (C * Z) * ‖proj A (θ t) - θ₀‖ := by
    intro t ht hr'
    set e := proj A (θ t) - θ₀ with he
    have heS : e ∈ S A := S_sub (proj_mem_S A (θ t)) hθ₀S
    have hnorm : ‖θ t‖ ≤ ‖θ₀‖ + r + N := by
      have h1 : ‖proj A (θ t)‖ ≤ ‖θ₀‖ + r := by
        have := norm_sub_norm_le (proj A (θ t)) θ₀
        linarith
      calc ‖θ t‖ = ‖proj A (θ t) + (θ t - proj A (θ t))‖ := by congr 1; abel
        _ ≤ ‖proj A (θ t)‖ + ‖θ t - proj A (θ t)‖ := norm_add_le _ _
        _ ≤ ‖θ₀‖ + r + N := by linarith [hsub t ht]
    have hΔ := hC (θ t) hnorm
    have hmono' := hmono (proj A (θ t)) θ₀ (mem_closedBall.mpr (by simpa [dist_eq_norm] using hr'))
      (mem_closedBall_self hr.le) heS
    rw [hgrad0, sub_zero] at hmono'
    -- `⟪e, π_A(-∇F θ)⟫ = -⟪e, π_A ∇F(π_A θ)⟫ - ⟪e, Δ⟫`
    have hsplit : ⟪e, proj A (gf F (θ t))⟫ =
        -⟪e, gradient F (proj A (θ t))⟫ -
          ⟪e, proj A (gradient F (θ t)) - proj A (gradient F (proj A (θ t)))⟫ := by
      rw [inner_sub_right, inner_proj_eq_of_mem_S heS, inner_proj_eq_of_mem_S heS,
        inner_proj_eq_of_mem_S heS, gf, inner_neg_right]
      ring
    rw [hsplit]
    have hcs : -⟪e, proj A (gradient F (θ t)) - proj A (gradient F (proj A (θ t)))⟫ ≤
        ‖e‖ * (C * Z) := by
      have h1 := real_inner_le_norm e
        (-(proj A (gradient F (θ t)) - proj A (gradient F (proj A (θ t)))))
      rw [inner_neg_right, norm_neg] at h1
      have h2 : C * zeta k A (θ t) ≤ C * Z := mul_le_mul_of_nonneg_left (hζ t ht) hC0
      calc _ ≤ ‖e‖ * ‖proj A (gradient F (θ t)) - proj A (gradient F (proj A (θ t)))‖ := h1
        _ ≤ ‖e‖ * (C * Z) := by gcongr; linarith
    nlinarith [hmono', hcs]
  -- the bound on `[a, t]`, given that `‖π_A θ - θ₀‖ ≤ r` there
  have hbound : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, ‖proj A (θ s) - θ₀‖ ≤ r) →
      ‖proj A (θ t) - θ₀‖ ≤ Real.exp (-μ * (t - a)) * ‖proj A (θ a) - θ₀‖ + C * Z / μ := by
    intro t ht hbox
    have hsubset : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have := norm_le_of_inner_deriv_le (f := fun t => proj A (θ t) - θ₀)
      (f' := fun t => proj A (gf F (θ t))) (a := a) (b := t) hμ (mul_nonneg hC0 hZ0)
      (hcont.mono hsubset)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hderiv s (hsubset (Ico_subset_Icc_self hs))).mono
        hsubset) hs)
      (fun s hs => hkey s (hsubset (Ico_subset_Icc_self hs)) (hbox s (Ico_subset_Icc_self hs)))
      t ⟨ht.1, le_rfl⟩
    simpa using this
  have hCZ : C * Z / μ ≤ C₀ * Z := by
    rw [hC₀, div_mul_eq_mul_div]
    gcongr
    linarith
  -- bootstrap: `‖π_A θ - θ₀‖` stays below `r₀ + C₀ r₀ < r`
  have hboot := bootstrap (f := fun t => proj A (θ t) - θ₀) (a := a) (b := b) hcont
    (K := closedBall 0 r) (K' := closedBall 0 (r₀ + C₀ * r₀)) isClosed_closedBall
    (by
      rw [interior_closedBall _ hr.ne']
      exact closedBall_subset_ball hr₀C)
    (mem_closedBall_zero_iff.mpr (ha.trans (by nlinarith [mul_pos hC₀pos hr₀pos])))
    (by
      intro t ht hbox
      have hb := hbound t ht (fun s hs => mem_closedBall_zero_iff.mp (hbox s hs))
      rw [mem_closedBall_zero_iff]
      have hexp : Real.exp (-μ * (t - a)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      have h1 : Real.exp (-μ * (t - a)) * ‖proj A (θ a) - θ₀‖ ≤ r₀ := by
        calc _ ≤ 1 * r₀ := by gcongr
          _ = r₀ := one_mul _
      have h2 : C₀ * Z ≤ C₀ * r₀ := mul_le_mul_of_nonneg_left hZ hC₀pos.le
      linarith)
  intro t ht
  have hbox : ∀ s ∈ Icc a t, ‖proj A (θ s) - θ₀‖ ≤ r := by
    intro s hs
    have := mem_closedBall_zero_iff.mp (hboot s ⟨hs.1, hs.2.trans ht.2⟩)
    linarith
  have := hbound t ht hbox
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 2 (Plateau)**, quantitative form: the constants `r₀`, `μ` depend only on `(A, θ₀)`. -/
theorem plateau {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) :
    ∃ r₀ μ : ℝ, PlateauProp F k A θ₀ r₀ μ := by
  obtain ⟨r₀, C₀, μ, hr₀, hr₀1, hC₀, hμ, hact⟩ := plateau_active hF hk hH hmin
  refine ⟨r₀, μ, hr₀, hμ, ?_⟩
  intro σ₀ σ₁ Ξ hσ hΞ
  have hθ₀S : θ₀ ∈ S A := hmin.mem
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Δσ : ℝ := σ₁ - σ₀ with hΔσ
  have hΔσ0 : 0 < Δσ := by rw [hΔσ]; linarith
  -- a bound on the dormant states
  obtain ⟨RΞ, hRΞ0, hRΞ⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ i ∉ A, ∀ σ ∈ Icc σ₀ σ₁, ‖Ξ i σ‖ ≤ R := by
    have hc : ∀ i ∉ A, ContinuousOn (Ξ i) (Icc σ₀ σ₁) :=
      fun i hi σ hσ' => (hΞ i hi σ hσ').continuousWithinAt
    have hb : ∀ i ∉ A, ∃ R, ∀ σ ∈ Icc σ₀ σ₁, ‖Ξ i σ‖ ≤ R :=
      fun i hi => isCompact_Icc.exists_bound_of_continuousOn (hc i hi)
    choose! R hR using hb
    refine ⟨∑ i ∈ Aᶜ, |R i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i hi σ hσ' => ?_⟩
    calc ‖Ξ i σ‖ ≤ R i := hR i hi σ hσ'
      _ ≤ |R i| := le_abs_self _
      _ ≤ ∑ i ∈ Aᶜ, |R i| :=
          Finset.single_le_sum (f := fun i => |R i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_compl.mpr hi)
  -- the polar functions `G_i`
  choose G hGsmooth hGpolar hG0 _ using fun i => exists_polar hF hk hH i
  -- a common Lipschitz constant for the `G_i` on a large ball
  set Rθ : ℝ := ‖θ₀‖ + r₀ + 1 + N * (RΞ + 1) with hRθ
  set Rb : ℝ := max 1 (max (RΞ + 1) Rθ) with hRb
  obtain ⟨L, hL⟩ : ∃ L : NNReal, ∀ i, LipschitzOnWith L (G i) (closedBall 0 Rb) := by
    have h : ∀ i, ∃ L : NNReal, LipschitzOnWith L (G i) (closedBall 0 Rb) := fun i =>
      ((hGsmooth i).contDiffOn).exists_lipschitzOnWith (by simp) (convex_closedBall _ _)
        (isCompact_closedBall _ _)
    choose Li hLi using h
    exact ⟨Finset.univ.sup Li, fun i => (hLi i).weaken (Finset.le_sup (Finset.mem_univ i))⟩
  set Lr : ℝ := (L : ℝ) with hLr
  have hLr0 : 0 ≤ Lr := L.2
  -- the constants
  set Kc : ℝ := C₀ * N * (RΞ + 1) ^ k with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set K : ℝ := Real.exp (Lr * Δσ) * (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) + Kc
    with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ Real.exp (Lr * Δσ) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ 1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1)) := by
      have : 0 ≤ Lr * r₀ / μ := by positivity
      have : 0 ≤ Lr * Δσ * (1 + Kc + N * (RΞ + 1)) := by positivity
      linarith
    have h3 : Real.exp (Lr * Δσ) * 1 ≤ Real.exp (Lr * Δσ) *
        (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    linarith
  have hKpos : 0 < K := by linarith
  set α₁ : ℝ := min 1 (min (1 / (4 * K)) (r₀ / (N * (RΞ + 1) ^ k + 1))) with hα₁
  set δ₁ : ℝ := 1 / (4 * K) with hδ₁
  have hα₁pos : 0 < α₁ := lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨α₁, δ₁, K, hα₁pos, by positivity, hKpos, ?_⟩
  intro α hα θ D hD τ hτ δ₀ hδ₀ hnear hdorm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2.trans (min_le_left _ _)
  have hαK : α ≤ 1 / (4 * K) := hα.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hαζ : α ≤ r₀ / (N * (RΞ + 1) ^ k + 1) :=
    hα.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ₀K : δ₀ ≤ 1 / (4 * K) := hδ₀.2
  -- powers of `α`
  have hk2 : 1 ≤ k - 2 := by omega
  have hαk2 : α ^ (k - 2) ≤ α := by
    calc α ^ (k - 2) ≤ α ^ 1 := pow_le_pow_of_le_one hα0.le hα1 hk2
      _ = α := pow_one α
  have hαk : α ^ k ≤ α := by
    calc α ^ k ≤ α ^ 1 := pow_le_pow_of_le_one hα0.le hα1 (by omega)
      _ = α := pow_one α
  have hαk2pos : 0 < α ^ (k - 2) := pow_pos hα0 _
  set sc : ℝ := (α ^ (k - 2))⁻¹ with hsc
  have hscpos : 0 < sc := inv_pos.mpr hαk2pos
  set tend : ℝ := τ + sc * Δσ with htend
  have hτtend : τ ≤ tend := by
    rw [htend]; have : 0 ≤ sc * Δσ := mul_nonneg hscpos.le hΔσ0.le; linarith
  -- the rescaled time
  obtain ⟨s, hs⟩ : ∃ s : ℝ → ℝ, s = fun t => σ₀ + α ^ (k - 2) * (t - τ) := ⟨_, rfl⟩
  have hs_mem : ∀ t ∈ Icc τ tend, s t ∈ Icc σ₀ σ₁ := by
    intro t ht
    constructor
    · rw [hs]; have : 0 ≤ α ^ (k - 2) * (t - τ) := mul_nonneg hαk2pos.le (by linarith [ht.1])
      simp only; linarith
    · have : α ^ (k - 2) * (t - τ) ≤ α ^ (k - 2) * (sc * Δσ) := by
        gcongr; linarith [ht.2]
      have h2 : α ^ (k - 2) * (sc * Δσ) = Δσ := by
        rw [hsc, ← mul_assoc, mul_inv_cancel₀ hαk2pos.ne', one_mul]
      rw [hs]; simp only; rw [hΔσ] at h2; linarith
  have hs_time : ∀ t ∈ Icc τ tend, α ^ (k - 2) * (t - τ) ≤ Δσ := by
    intro t ht
    have := (hs_mem t ht).2
    rw [hs] at this; simp only at this
    rw [hΔσ]; linarith
  -- the deviation of the rescaled dormant weights
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ → E, f = fun i t => α⁻¹ • θ t i - Ξ i (s t) := ⟨_, rfl⟩
  -- smallness of the constants
  have hZ : N * (RΞ + 1) ^ k * α ^ k ≤ r₀ := by
    have h1 : N * (RΞ + 1) ^ k * α ^ k ≤ N * (RΞ + 1) ^ k * α := by gcongr
    have h2 : N * (RΞ + 1) ^ k * α ≤ (N * (RΞ + 1) ^ k + 1) * α := by
      rw [add_mul, one_mul]; linarith
    have h3 : (N * (RΞ + 1) ^ k + 1) * α ≤ r₀ := by
      rw [le_div_iff₀ (by positivity)] at hαζ; linarith
    linarith
  -- Step 1: the estimates on any `[τ, T'] ⊆ D` on which the box holds
  have hstep : ∀ T' ∈ Icc τ tend, Icc τ T' ⊆ D →
      (∀ t ∈ Icc τ T', ∀ i ∉ A, ‖f i t‖ ≤ 1) →
      (∀ t ∈ Icc τ T', ∀ i ∉ A, ‖θ t i‖ ≤ α * (RΞ + 1)) ∧
      (∀ t ∈ Icc τ T', ‖proj A (θ t) - θ₀‖ ≤
          Real.exp (-μ * (t - τ)) * ‖proj A (θ τ) - θ₀‖ + Kc * α ^ k) ∧
      (∀ t ∈ Icc τ T', ‖θ t‖ ≤ Rθ) ∧
      (∀ t ∈ Icc τ T', ∀ i ∉ A, ‖f i t‖ ≤ K * (δ₀ + α)) := by
    intro T' hT' hsubD hbox
    have hT'D : T' ∈ D := hsubD ⟨hT'.1, le_rfl⟩
    have hsol := hD.hasDerivWithinAt_Icc hτ hT'D
    have hTT : Icc τ T' ⊆ Icc τ tend := Icc_subset_Icc le_rfl hT'.2
    -- (a) the inactive weights are `O(α)`
    have ha : ∀ t ∈ Icc τ T', ∀ i ∉ A, ‖θ t i‖ ≤ α * (RΞ + 1) := by
      intro t ht i hi
      have h1 : ‖α⁻¹ • θ t i‖ ≤ RΞ + 1 := by
        have := hbox t ht i hi
        have h2 := hRΞ i hi (s t) (hs_mem t (hTT ht))
        calc ‖α⁻¹ • θ t i‖ = ‖f i t + Ξ i (s t)‖ := by rw [hf]; simp
          _ ≤ ‖f i t‖ + ‖Ξ i (s t)‖ := norm_add_le _ _
          _ ≤ RΞ + 1 := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα0] at h1
      rw [inv_mul_le_iff₀ hα0] at h1
      linarith
    -- (b) `ζ_A ≤ Z ≤ r₀`
    have hζ : ∀ t ∈ Icc τ T', zeta k A (θ t) ≤ N * (RΞ + 1) ^ k * α ^ k := by
      intro t ht
      have := zeta_le_card_mul (k := k) (A := A) (θ := θ t) (by positivity) (ha t ht)
      rw [mul_pow] at this
      linarith [this]
    -- (c) the active coordinates
    have hactive : ∀ t ∈ Icc τ T', ‖proj A (θ t) - θ₀‖ ≤
        Real.exp (-μ * (t - τ)) * ‖proj A (θ τ) - θ₀‖ + Kc * α ^ k := by
      intro t ht
      have := hact θ τ T' (N * (RΞ + 1) ^ k * α ^ k) hT'.1 hsol hnear hZ hζ t ht
      have he : C₀ * (N * (RΞ + 1) ^ k * α ^ k) = Kc * α ^ k := by rw [hKc]; ring
      linarith
    -- (d) a bound on `θ`
    have hθbound : ∀ t ∈ Icc τ T', ‖θ t‖ ≤ Rθ := by
      intro t ht
      have h1 : ‖proj A (θ t) - θ₀‖ ≤ r₀ + 1 := by
        have h2 := hactive t ht
        have hexp : Real.exp (-μ * (t - τ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have : 0 ≤ μ * (t - τ) := mul_nonneg hμ.le (by linarith [ht.1])
            linarith)
        have h3 : Real.exp (-μ * (t - τ)) * ‖proj A (θ τ) - θ₀‖ ≤ r₀ := by
          calc _ ≤ 1 * r₀ := by gcongr
            _ = r₀ := one_mul _
        have h4 : Kc * α ^ k ≤ 1 := by
          have h5 : Kc * α ^ k ≤ Kc * α := mul_le_mul_of_nonneg_left hαk hKc0
          have h6 : Kc * α ≤ Kc * (1 / (4 * K)) := mul_le_mul_of_nonneg_left hαK hKc0
          have h7 : Kc * (1 / (4 * K)) ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            have : Kc ≤ K := by
              have : 0 ≤ Real.exp (Lr * Δσ) *
                  (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) := by positivity
              rw [hK]; linarith
            linarith
          linarith
        linarith
      have h5 : ‖θ t - proj A (θ t)‖ ≤ N * (α * (RΞ + 1)) :=
        norm_sub_proj_le_card_mul (by positivity) (ha t ht)
      have h6 : N * (α * (RΞ + 1)) ≤ N * (RΞ + 1) := by
        have : α * (RΞ + 1) ≤ 1 * (RΞ + 1) := by gcongr
        have := mul_le_mul_of_nonneg_left this hN0
        linarith
      calc ‖θ t‖ = ‖θ₀ + (proj A (θ t) - θ₀) + (θ t - proj A (θ t))‖ := by congr 1; abel
        _ ≤ ‖θ₀‖ + ‖proj A (θ t) - θ₀‖ + ‖θ t - proj A (θ t)‖ := norm_add₃_le
        _ ≤ Rθ := by rw [hRθ]; linarith
    refine ⟨ha, hactive, hθbound, ?_⟩
    -- (e) Grönwall for the rescaled dormant weights
    intro t ht i hi
    have hdist : ∀ t ∈ Icc τ T', ‖θ t - θ₀‖ ≤
        Real.exp (-μ * (t - τ)) * r₀ + (Kc * α ^ k + N * (α * (RΞ + 1))) := by
      intro t ht
      have h1 := hactive t ht
      have h2 : ‖θ t - proj A (θ t)‖ ≤ N * (α * (RΞ + 1)) :=
        norm_sub_proj_le_card_mul (by positivity) (ha t ht)
      have h3 : Real.exp (-μ * (t - τ)) * ‖proj A (θ τ) - θ₀‖ ≤ Real.exp (-μ * (t - τ)) * r₀ :=
        mul_le_mul_of_nonneg_left hnear (Real.exp_pos _).le
      calc ‖θ t - θ₀‖ = ‖(proj A (θ t) - θ₀) + (θ t - proj A (θ t))‖ := by congr 1; abel
        _ ≤ ‖proj A (θ t) - θ₀‖ + ‖θ t - proj A (θ t)‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    -- the derivative of `f i`
    have hderiv : ∀ t ∈ Icc τ T', HasDerivWithinAt (f i)
        (α ^ (k - 2) • (G i (α, α⁻¹ • θ t i, θ t) - G i (0, Ξ i (s t), θ₀))) (Icc τ T') t := by
      intro t ht
      have h1 : HasDerivWithinAt (fun t => θ t i) ((gf F (θ t)) i) (Icc τ T') t :=
        (PiLp.proj 2 (fun _ : ι => E) i).hasFDerivAt.comp_hasDerivWithinAt t (hsol t ht)
      have hpol : (gf F (θ t)) i = α ^ (k - 1) • G i (α, α⁻¹ • θ t i, θ t) := by
        have := hGpolar i α (α⁻¹ • θ t i) (θ t)
        rw [smul_inv_smul₀ hα0.ne', insertAt_self] at this
        rw [← this, gf]
        rfl
      have h2 : HasDerivWithinAt (fun t => α⁻¹ • θ t i)
          (α ^ (k - 2) • G i (α, α⁻¹ • θ t i, θ t)) (Icc τ T') t := by
        have := h1.const_smul α⁻¹
        convert this using 1
        rw [hpol, smul_smul]
        congr 1
        have hk1 : k - 1 = (k - 2) + 1 := by omega
        rw [hk1, pow_succ]
        field_simp
      have hsmap : MapsTo s (Icc τ T') (Icc σ₀ σ₁) := fun t ht => hs_mem t (hTT ht)
      have h3 : HasDerivWithinAt s (α ^ (k - 2)) (Icc τ T') t := by
        rw [hs]
        have := ((hasDerivAt_id t).sub_const τ).const_mul (α ^ (k - 2))
        simpa using (this.const_add σ₀).hasDerivWithinAt
      have h4 : HasDerivWithinAt (fun t => Ξ i (s t))
          (α ^ (k - 2) • G i (0, Ξ i (s t), θ₀)) (Icc τ T') t := by
        have := (hΞ i hi (s t) (hsmap ht)).scomp t h3 hsmap
        rw [← hG0] at this
        exact this
      have := h2.sub h4
      rw [hf]
      convert this using 1
      rw [smul_sub]
    -- the bound on the derivative
    have hbound : ∀ t ∈ Ico τ T', ‖α ^ (k - 2) • (G i (α, α⁻¹ • θ t i, θ t) -
        G i (0, Ξ i (s t), θ₀))‖ ≤
        (α ^ (k - 2) * Lr) * ‖f i t‖ + (α ^ (k - 2) * Lr * r₀) * Real.exp (-μ * (t - τ)) +
          α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) := by
      intro t ht
      have ht' : t ∈ Icc τ T' := Ico_subset_Icc_self ht
      have hW : ‖α⁻¹ • θ t i‖ ≤ RΞ + 1 := by
        have := ha t ht' i hi
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα0, inv_mul_le_iff₀ hα0]
        linarith
      have hRbge : 1 ≤ Rb ∧ RΞ + 1 ≤ Rb ∧ Rθ ≤ Rb :=
        ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
          (le_max_right _ _).trans (le_max_right _ _)⟩
      have hp1 : ((α, α⁻¹ • θ t i, θ t) : ℝ × E × Θ ι E) ∈ closedBall 0 Rb := by
        rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def]
        refine max_le ?_ (max_le ?_ ?_)
        · rw [Real.norm_eq_abs, abs_of_pos hα0]; linarith [hRbge.1]
        · linarith [hRbge.2.1]
        · linarith [hθbound t ht', hRbge.2.2]
      have hθ₀Rθ : ‖θ₀‖ ≤ Rθ := by rw [hRθ]; have := mul_nonneg hN0 (by linarith : (0:ℝ) ≤ RΞ + 1); linarith
      have hp2 : ((0, Ξ i (s t), θ₀) : ℝ × E × Θ ι E) ∈ closedBall 0 Rb := by
        rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def]
        refine max_le ?_ (max_le ?_ ?_)
        · simp; linarith [hRbge.1]
        · linarith [hRΞ i hi (s t) (hs_mem t (hTT ht')), hRbge.2.1]
        · linarith [hRbge.2.2]
      have hlip := (hL i).norm_sub_le hp1 hp2
      have hdiff : ‖((α, α⁻¹ • θ t i, θ t) : ℝ × E × Θ ι E) - (0, Ξ i (s t), θ₀)‖ ≤
          α + ‖f i t‖ + ‖θ t - θ₀‖ := by
        rw [Prod.norm_def]
        simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Prod.norm_def]
        have hfi : f i t = α⁻¹ • θ t i - Ξ i (s t) := by rw [hf]
        refine max_le ?_ (max_le ?_ ?_)
        · rw [Real.norm_eq_abs, abs_of_pos hα0]
          linarith [norm_nonneg (f i t), norm_nonneg (θ t - θ₀)]
        · rw [← hfi]; linarith [norm_nonneg (θ t - θ₀)]
        · linarith [norm_nonneg (f i t)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαk2pos]
      have h5 := hdist t ht'
      calc α ^ (k - 2) * ‖G i (α, α⁻¹ • θ t i, θ t) - G i (0, Ξ i (s t), θ₀)‖
          ≤ α ^ (k - 2) * (Lr * (α + ‖f i t‖ + ‖θ t - θ₀‖)) := by
            gcongr
            calc _ ≤ Lr * ‖((α, α⁻¹ • θ t i, θ t) : ℝ × E × Θ ι E) - (0, Ξ i (s t), θ₀)‖ := hlip
              _ ≤ _ := by gcongr
        _ ≤ α ^ (k - 2) * (Lr * (α + ‖f i t‖ + (Real.exp (-μ * (t - τ)) * r₀ +
              (Kc * α ^ k + N * (α * (RΞ + 1)))))) := by gcongr
        _ = _ := by ring
    have hgr := norm_le_gronwall_exp (f := f i)
      (f' := fun t => α ^ (k - 2) • (G i (α, α⁻¹ • θ t i, θ t) - G i (0, Ξ i (s t), θ₀)))
      (a := τ) (b := T') (L := α ^ (k - 2) * Lr) (ν := μ) (c₁ := α ^ (k - 2) * Lr * r₀)
      (c₂ := α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))))
      (by positivity) hμ (by positivity) (by positivity)
      (fun t ht => (hderiv t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc (hderiv t (Ico_subset_Icc_self ht)) ht)
      hbound t ht
    -- simplify the Grönwall bound
    have hfτ : ‖f i τ‖ ≤ δ₀ := by
      have : s τ = σ₀ := by rw [hs]; simp
      rw [hf]; simp only [this]; exact hdorm i hi
    have htime := hs_time t (hTT ht)
    have hexp : Real.exp (α ^ (k - 2) * Lr * (t - τ)) ≤ Real.exp (Lr * Δσ) := by
      apply Real.exp_le_exp.mpr
      have : α ^ (k - 2) * Lr * (t - τ) = Lr * (α ^ (k - 2) * (t - τ)) := by ring
      rw [this]; gcongr
    have hc1 : α ^ (k - 2) * Lr * r₀ / μ ≤ α * (Lr * r₀ / μ) := by
      rw [mul_div_assoc, mul_div_assoc, mul_assoc]
      gcongr
    have hc2 : α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (t - τ) ≤
        α * (Lr * Δσ * (1 + Kc + N * (RΞ + 1))) := by
      have h1 : α + (Kc * α ^ k + N * (α * (RΞ + 1))) ≤ α * (1 + Kc + N * (RΞ + 1)) := by
        have : Kc * α ^ k ≤ Kc * α := mul_le_mul_of_nonneg_left hαk hKc0
        have he : α * (1 + Kc + N * (RΞ + 1)) = α + Kc * α + N * (α * (RΞ + 1)) := by ring
        linarith
      have h2 : α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (t - τ) =
          Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (α ^ (k - 2) * (t - τ)) := by ring
      rw [h2]
      have h3 : 0 ≤ α + (Kc * α ^ k + N * (α * (RΞ + 1))) := by positivity
      calc Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (α ^ (k - 2) * (t - τ))
          ≤ Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * Δσ := by gcongr
        _ ≤ Lr * (α * (1 + Kc + N * (RΞ + 1))) * Δσ := by gcongr
        _ = _ := by ring
    have hinner : ‖f i τ‖ + α ^ (k - 2) * Lr * r₀ / μ +
        α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (t - τ) ≤
        (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) * (δ₀ + α) := by
      have h0 : 0 ≤ Lr * r₀ / μ := by positivity
      have h0' : 0 ≤ Lr * Δσ * (1 + Kc + N * (RΞ + 1)) := by positivity
      have hδ0 : 0 ≤ δ₀ := hδ₀.1
      have he : (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) * (δ₀ + α) =
          δ₀ + α + Lr * r₀ / μ * δ₀ + α * (Lr * r₀ / μ) +
            Lr * Δσ * (1 + Kc + N * (RΞ + 1)) * δ₀ + α * (Lr * Δσ * (1 + Kc + N * (RΞ + 1))) := by
        ring
      have h1 : 0 ≤ Lr * r₀ / μ * δ₀ := mul_nonneg h0 hδ0
      have h2 : 0 ≤ Lr * Δσ * (1 + Kc + N * (RΞ + 1)) * δ₀ := mul_nonneg h0' hδ0
      linarith [hfτ, hc1, hc2, hα0.le]
    have hinner0 : 0 ≤ ‖f i τ‖ + α ^ (k - 2) * Lr * r₀ / μ +
        α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (t - τ) := by
      have : 0 ≤ t - τ := by linarith [ht.1]
      positivity
    calc ‖f i t‖ ≤ Real.exp (α ^ (k - 2) * Lr * (t - τ)) * (‖f i τ‖ +
          α ^ (k - 2) * Lr * r₀ / μ +
          α ^ (k - 2) * Lr * (α + (Kc * α ^ k + N * (α * (RΞ + 1)))) * (t - τ)) := hgr
      _ ≤ Real.exp (Lr * Δσ) * ((1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) *
          (δ₀ + α)) := by gcongr
      _ ≤ K * (δ₀ + α) := by
          rw [hK, ← mul_assoc, add_mul]
          have : 0 ≤ Kc * (δ₀ + α) := by have := hδ₀.1; positivity
          linarith
  -- Step 2: bootstrap on any `[τ, T'] ⊆ D`
  have hKhalf : K * (δ₀ + α) ≤ 1 / 2 := by
    have h1 : K * δ₀ ≤ 1 / 4 := by
      calc K * δ₀ ≤ K * (1 / (4 * K)) := by gcongr
        _ = 1 / 4 := by field_simp
    have h2 : K * α ≤ 1 / 4 := by
      calc K * α ≤ K * (1 / (4 * K)) := by gcongr
        _ = 1 / 4 := by field_simp
    rw [mul_add]; linarith
  have hbootT : ∀ T' ∈ Icc τ tend, Icc τ T' ⊆ D → ∀ t ∈ Icc τ T', ∀ i ∉ A, ‖f i t‖ ≤ 1 / 2 := by
    intro T' hT' hsubD
    have hT'D : T' ∈ D := hsubD ⟨hT'.1, le_rfl⟩
    have hsol := hD.hasDerivWithinAt_Icc hτ hT'D
    have hTT : Icc τ T' ⊆ Icc τ tend := Icc_subset_Icc le_rfl hT'.2
    set g : ℝ → (ι → E) := fun t i => if i ∈ A then 0 else f i t with hg
    have hcont : ContinuousOn g (Icc τ T') := by
      refine continuousOn_pi.mpr fun i => ?_
      by_cases hi : i ∈ A
      · simp only [hg, hi, if_true]; exact continuousOn_const
      · simp only [hg, hi, if_false]
        rw [hf]
        refine ContinuousOn.sub ?_ ?_
        · refine ContinuousOn.const_smul ?_ _
          exact (PiLp.continuous_apply 2 (fun _ : ι => E) i).comp_continuousOn
            (fun t ht => (hsol t ht).continuousWithinAt)
        · have hΞc : ContinuousOn (Ξ i) (Icc σ₀ σ₁) :=
            fun σ hσ' => (hΞ i hi σ hσ').continuousWithinAt
          refine hΞc.comp ?_ (fun t ht => hs_mem t (hTT ht))
          rw [hs]; fun_prop
    have hKset : IsClosed {x : ι → E | ∀ i ∉ A, ‖x i‖ ≤ 1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_le (continuous_norm.comp (continuous_apply i)) continuous_const
    have hint : {x : ι → E | ∀ i ∉ A, ‖x i‖ ≤ 1 / 2} ⊆ interior {x : ι → E | ∀ i ∉ A, ‖x i‖ ≤ 1} := by
      have hopen : IsOpen {x : ι → E | ∀ i ∉ A, ‖x i‖ < 1} := by
        have : {x : ι → E | ∀ i ∉ A, ‖x i‖ < 1} = ⋂ i ∈ (Aᶜ : Finset ι), {x | ‖x i‖ < 1} := by
          ext x; simp
        rw [this]
        exact isOpen_biInter_finset fun i _ =>
          isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
      refine Subset.trans ?_ (interior_maximal ?_ hopen)
      · intro x hx i hi; have := hx i hi; linarith
      · intro x hx i hi; exact (hx i hi).le
    have hb := bootstrap (f := g) hcont hKset hint
      (by
        intro i hi
        simp only [hg, hi, if_false]
        have : s τ = σ₀ := by rw [hs]; simp
        rw [hf]; simp only [this]
        have h1 := hdorm i hi
        have h2 : δ₀ ≤ 1 / 4 := hδ₀K.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
        linarith)
      (by
        intro t ht hbox i hi
        have hbox' : ∀ s' ∈ Icc τ t, ∀ j ∉ A, ‖f j s'‖ ≤ 1 := by
          intro s' hs' j hj
          have := hbox s' hs' j hj
          simpa [hg, hj] using this
        have := (hstep t ⟨ht.1, ht.2.trans hT'.2⟩ ((Icc_subset_Icc le_rfl ht.2).trans hsubD)
          hbox').2.2.2 t ⟨ht.1, le_rfl⟩ i hi
        simp only [hg, hi, if_false]
        linarith)
    intro t ht i hi
    have := hb t ht i hi
    simpa [hg, hi] using this
  -- Step 3: existence on `[τ, tend]`
  have hstepT : ∀ T' ∈ Icc τ tend, Icc τ T' ⊆ D → _ := fun T' hT' hsubD =>
    hstep T' hT' hsubD (fun t ht i hi => (hbootT T' hT' hsubD t ht i hi).trans (by norm_num))
  have hexist : Icc τ tend ⊆ D := by
    refine hD.Icc_subset_of_bounded hτ (R := Rθ) ?_
    intro t ht htD
    have hsub : Icc τ t ⊆ D := hD.Icc_subset hτ htD
    exact (hstepT t ht hsub).2.2.1 t ⟨ht.1, le_rfl⟩
  obtain ⟨_, hactive, _, hdormant⟩ := hstepT tend ⟨hτtend, le_rfl⟩ hexist
  refine ⟨hexist, ?_, ?_⟩
  · intro σ hσ' i hi
    have ht : τ + sc * (σ - σ₀) ∈ Icc τ tend := by
      constructor
      · have : 0 ≤ sc * (σ - σ₀) := mul_nonneg hscpos.le (by linarith [hσ'.1])
        linarith
      · rw [htend]; gcongr; rw [hΔσ]; linarith [hσ'.2]
    have hst : s (τ + sc * (σ - σ₀)) = σ := by
      rw [hs]; simp only [add_sub_cancel_left]
      rw [hsc, ← mul_assoc, mul_inv_cancel₀ hαk2pos.ne', one_mul]; ring
    have := hdormant _ ht i hi
    rw [hf] at this; simp only [hst] at this
    exact this
  · intro t ht
    have := hactive t ht
    have hKcK : Kc ≤ K := by
      have : 0 ≤ Real.exp (Lr * Δσ) *
          (1 + Lr * r₀ / μ + Lr * Δσ * (1 + Kc + N * (RΞ + 1))) := by positivity
      rw [hK]; linarith
    have : Kc * α ^ k ≤ K * α ^ k := mul_le_mul_of_nonneg_right hKcK (by positivity)
    linarith

end S2S
