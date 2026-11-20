import SaddleToSaddle.Coords

/-!
# Generic analysis lemmas

Comparison principles (one-sided Grönwall estimates), a continuous-induction ("bootstrap")
principle, a time-change lemma for ODEs, and a lemma relating iterated derivatives along lines
to iterated Fréchet derivatives. Nothing here is specific to the saddle-to-saddle setting.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

/-- Continuous induction ("bootstrap"): if `f` starts in a closed set `K`, and whenever `f` stays
in `K` on `[a, t]` it is in fact in a smaller set `K' ⊆ interior K` at time `t`, then `f` stays
in `K'` on all of `[a, b]`. -/
theorem bootstrap {X : Type*} [TopologicalSpace X] {a b : ℝ} {f : ℝ → X}
    (hf : ContinuousOn f (Icc a b)) {K K' : Set X} (hK : IsClosed K) (hK' : K' ⊆ interior K)
    (ha : f a ∈ K) (himp : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, f s ∈ K) → f t ∈ K') :
    ∀ t ∈ Icc a b, f t ∈ K' := by
  have hsub : Icc a b ⊆ f ⁻¹' K := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
    · have h := hf.preimage_isClosed_of_isClosed isClosed_Icc hK
      rwa [inter_comm] at h
    · exact ha
    · intro t ht hsubt
      have htK : f t ∈ K' := himp t (Ico_subset_Icc_self ht) (fun s hs => hsubt hs)
      have h1 : f ⁻¹' interior K ∈ 𝓝[Icc a b] t :=
        (hf t (Ico_subset_Icc_self ht)).preimage_mem_nhdsWithin
          (isOpen_interior.mem_nhds (hK' htK))
      have h2 : 𝓝[>] t ≤ 𝓝[Icc a b] t := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT ht.2]
        exact nhdsWithin_mono _ (Ioo_subset_Icc_self.trans (Icc_subset_Icc ht.1 le_rfl))
      exact mem_of_superset (h2 h1) (preimage_mono interior_subset)
  intro t ht
  exact himp t ht (fun s hs => hsub ⟨hs.1, hs.2.trans ht.2⟩)

/-- One-sided Grönwall estimate in a Hilbert space: if `⟪f, f'⟫ ≤ -μ‖f‖² + β‖f‖`, then
`‖f t‖ ≤ e^{-μ(t-a)} ‖f a‖ + β/μ`. -/
theorem norm_le_of_inner_deriv_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f f' : ℝ → V} {a b μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, ⟪f t, f' t⟫ ≤ -μ * ‖f t‖ ^ 2 + β * ‖f t‖) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (-μ * (t - a)) * ‖f a‖ + β / μ := by
  intro t ht
  -- the estimate with a margin `ε`
  have hmain : ∀ ε > 0,
      ‖f t‖ ≤ Real.exp (-μ * (t - a)) * ‖f a‖ + β / μ + ε * (1 + 1 / μ) := by
    intro ε hε
    set E : ℝ → ℝ := fun t => Real.exp (-μ * (t - a)) with hEdef
    have hE : ∀ t, HasDerivAt E (E t * (-μ)) t := fun t => by
      have h := (((hasDerivAt_id t).sub_const a).const_mul (-μ)).exp
      exact h.congr_deriv (by simp [hEdef])
    set B : ℝ → ℝ := fun t => E t * (‖f a‖ + ε) + (β + ε) / μ * (1 - E t) with hBdef
    set B' : ℝ → ℝ := fun t => E t * (β + ε - μ * (‖f a‖ + ε)) with hB'def
    have hB : ∀ t, HasDerivAt B (B' t) t := fun t => by
      have h := ((hE t).mul_const (‖f a‖ + ε)).add (((hE t).const_sub 1).const_mul ((β + ε) / μ))
      refine h.congr_deriv ?_
      simp only [hB'def]
      field_simp
      ring
    have hBeq : ∀ t, B' t = -μ * B t + (β + ε) := fun t => by
      simp only [hBdef, hB'def]
      field_simp
      ring
    have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
    have hEle : ∀ t, a ≤ t → E t ≤ 1 := fun t ht => by
      simp only [hEdef]
      rw [Real.exp_le_one_iff]
      nlinarith
    have hBpos : ∀ t, a ≤ t → 0 < B t := fun t ht => by
      simp only [hBdef]
      have h1 := hEpos t
      have h2 := hEle t ht
      have h3 : 0 ≤ (β + ε) / μ * (1 - E t) :=
        mul_nonneg (div_nonneg (by linarith) hμ.le) (by linarith)
      have h4 : 0 < E t * (‖f a‖ + ε) := mul_pos h1 (by positivity)
      linarith
    have hsq := image_le_of_deriv_right_lt_deriv_boundary (f := fun t => ‖f t‖ ^ 2)
      (f' := fun t => 2 * ⟪f t, f' t⟫) (B := fun t => B t ^ 2)
      (B' := fun t => ((2 : ℕ) : ℝ) * B t ^ (2 - 1) * B' t) ?_ ?_ ?_ ?_ ?_ ht
    · have hBt := hBpos t ht.1
      have h0 : ‖f t‖ ≤ B t := (sq_le_sq₀ (norm_nonneg _) hBt.le).1 hsq
      refine h0.trans ?_
      simp only [hBdef]
      have h1 := hEpos t
      have h2 := hEle t ht.1
      have h4 : β / μ * (1 - E t) ≤ β / μ := by
        have : 0 ≤ β / μ := div_nonneg hβ hμ.le
        nlinarith
      have h5 : ε / μ * (1 - E t) ≤ ε / μ := by
        have : 0 ≤ ε / μ := div_nonneg hε.le hμ.le
        nlinarith
      have h6 : E t * ε ≤ ε := by nlinarith
      have h7 : (β + ε) / μ * (1 - E t) = β / μ * (1 - E t) + ε / μ * (1 - E t) := by ring
      have h8 : ε * (1 + 1 / μ) = ε + ε / μ := by ring
      have h9 : E t * (‖f a‖ + ε) = E t * ‖f a‖ + E t * ε := by ring
      rw [h7, h8, h9]
      linarith
    · exact (continuous_norm.comp_continuousOn hf).pow 2
    · intro x hx
      exact (hf' x hx).norm_sq
    · have hEa : E a = 1 := by simp [hEdef]
      simp only [hBdef, hEa, sub_self, mul_zero, add_zero, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    · intro x
      exact (hB x).pow 2
    · intro x hx hxeq
      have hBx := hBpos x hx.1
      have hnx : ‖f x‖ = B x := (sq_eq_sq₀ (norm_nonneg _) hBx.le).1 hxeq
      have hb := hbound x hx
      rw [hnx] at hb
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      rw [hBeq x]
      nlinarith
  -- let the margin go to zero
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : 0 < 1 + 1 / μ := by positivity
  have h := hmain (ε / (1 + 1 / μ)) (div_pos hε hc)
  rwa [div_mul_cancel₀ _ hc.ne'] at h

/-- Grönwall's lemma with an exponentially decaying forcing term. -/
theorem norm_le_gronwall_exp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f f' : ℝ → V} {a b L ν c₁ c₂ : ℝ} (hL : 0 ≤ L) (hν : 0 < ν) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, ‖f' t‖ ≤ L * ‖f t‖ + c₁ * Real.exp (-ν * (t - a)) + c₂) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (L * (t - a)) * (‖f a‖ + c₁ / ν + c₂ * (t - a)) := by
  intro t ht
  set Ed : ℝ → ℝ := fun t => Real.exp (-ν * (t - a)) with hEd
  have hEdpos : ∀ t, 0 < Ed t := fun t => Real.exp_pos _
  have hEdle : ∀ t, a ≤ t → Ed t ≤ 1 := fun t ht => by
    simp only [hEd]
    rw [Real.exp_le_one_iff]
    nlinarith
  have hEdd : ∀ t, HasDerivAt Ed (Ed t * (-ν)) t := fun t => by
    have h := (((hasDerivAt_id t).sub_const a).const_mul (-ν)).exp
    exact h.congr_deriv (by simp [hEd])
  -- the estimate with a margin `ε`
  have hmain : ∀ ε > 0, ‖f t‖ ≤ Real.exp ((L + ε) * (t - a)) *
      (‖f a‖ + ε + c₁ / ν * (1 - Ed t) + c₂ * (t - a)) := by
    intro ε hε
    set P : ℝ → ℝ := fun t => Real.exp ((L + ε) * (t - a)) with hP
    set Q : ℝ → ℝ := fun t => ‖f a‖ + ε + c₁ / ν * (1 - Ed t) + c₂ * (t - a) with hQ
    have hPd : ∀ t, HasDerivAt P (P t * (L + ε)) t := fun t => by
      have h := (((hasDerivAt_id t).sub_const a).const_mul (L + ε)).exp
      exact h.congr_deriv (by simp [hP])
    have hQd : ∀ t, HasDerivAt Q (c₁ * Ed t + c₂) t := fun t => by
      have h := ((((hEdd t).const_sub 1).const_mul (c₁ / ν)).const_add (‖f a‖ + ε)).add
        (((hasDerivAt_id t).sub_const a).const_mul c₂)
      refine h.congr_deriv ?_
      field_simp
    have hBd : ∀ t, HasDerivAt (fun t => P t * Q t)
        (P t * (L + ε) * Q t + P t * (c₁ * Ed t + c₂)) t := fun t => (hPd t).mul (hQd t)
    have hPpos : ∀ t, 0 < P t := fun t => Real.exp_pos _
    have hPge : ∀ t, a ≤ t → 1 ≤ P t := fun t ht => by
      simp only [hP]
      exact Real.one_le_exp (mul_nonneg (by linarith) (by linarith))
    have hQpos : ∀ t, a ≤ t → ‖f a‖ + ε ≤ Q t := fun t ht => by
      simp only [hQ]
      have h1 : 0 ≤ c₁ / ν * (1 - Ed t) :=
        mul_nonneg (div_nonneg hc₁ hν.le) (by linarith [hEdle t ht])
      have h2 : 0 ≤ c₂ * (t - a) := mul_nonneg hc₂ (by linarith)
      linarith
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary hf hf' ?_ hBd ?_ ht
    · have hPa : P a = 1 := by simp [hP]
      have hEda : Ed a = 1 := by simp [hEd]
      show ‖f a‖ ≤ P a * Q a
      simp only [hPa, hQ, hEda, sub_self, mul_zero, add_zero, one_mul]
      linarith
    · intro x hx hxeq
      have hb : ‖f' x‖ ≤ L * ‖f x‖ + c₁ * Ed x + c₂ := hbound x hx
      have hxeq' : ‖f x‖ = P x * Q x := hxeq
      rw [hxeq'] at hb
      have hPx := hPge x hx.1
      have hQx := hQpos x hx.1
      have hEx := hEdpos x
      have h1 : 0 < ε * (P x * Q x) :=
        mul_pos hε (mul_pos (hPpos x) (by linarith [norm_nonneg (f a)]))
      have h2 : c₁ * Ed x + c₂ ≤ P x * (c₁ * Ed x + c₂) := by
        have : 0 ≤ c₁ * Ed x + c₂ := by positivity
        nlinarith
      have h3 : P x * (L + ε) * Q x = L * (P x * Q x) + ε * (P x * Q x) := by ring
      show ‖f' x‖ < P x * (L + ε) * Q x + P x * (c₁ * Ed x + c₂)
      linarith
  -- let the margin go to zero
  have hlim : Tendsto (fun ε => Real.exp ((L + ε) * (t - a)) *
      (‖f a‖ + ε + c₁ / ν * (1 - Ed t) + c₂ * (t - a))) (𝓝[>] 0)
      (𝓝 (Real.exp ((L + 0) * (t - a)) * (‖f a‖ + 0 + c₁ / ν * (1 - Ed t) + c₂ * (t - a)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Continuous.tendsto (f := fun ε => Real.exp ((L + ε) * (t - a)) *
      (‖f a‖ + ε + c₁ / ν * (1 - Ed t) + c₂ * (t - a)))
    fun_prop
  have h1 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun ε hε => hmain ε hε))
  simp only [add_zero] at h1
  refine h1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have : c₁ / ν * (1 - Ed t) ≤ c₁ / ν := by
    have h0 : 0 ≤ c₁ / ν := div_nonneg hc₁ hν.le
    have := hEdpos t
    nlinarith
  linarith

/-- Comparison with `ẏ = C y^{k-1}`: on a short enough interval, a function with
`‖f'‖ ≤ C ‖f‖^{k-1}` at most doubles. -/
theorem norm_le_two_mul_of_deriv_le_pow {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f f' : ℝ → V} {a b C η : ℝ} {k : ℕ} (hk : 3 ≤ k) (hC : 0 ≤ C) (hη : 0 ≤ η) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, ‖f' t‖ ≤ C * ‖f t‖ ^ (k - 1)) (ha : ‖f a‖ ≤ η)
    (hT : ((k : ℝ) - 2) * C * (b - a) * η ^ (k - 2) < 1 - (2 : ℝ)⁻¹ ^ (k - 2)) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ 2 * η := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m ≠ 0 := by omega
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  have ek : ((m + 2 : ℕ) : ℝ) - 2 = (m : ℝ) := by push_cast; ring
  rw [e1] at hbound
  rw [e2, ek] at hT
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  intro t ht
  -- smallness of the perturbation parameter `ε`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (m : ℝ) * (C + ε) * (b - a) * (η + ε) ^ m < 1 - (2 : ℝ)⁻¹ ^ m := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hcont : Continuous (fun ε : ℝ => (m : ℝ) * (C + ε) * (b - a) * (η + ε) ^ m) := by
      fun_prop
    have h := hcont.tendsto 0
    simp only [add_zero] at h
    exact h.eventually_lt_const hT
  -- comparison with the solution of `y' = (C + ε) y ^ (m + 1)`, `y a = η + ε`
  have hmain : ∀ ε > 0, (m : ℝ) * (C + ε) * (b - a) * (η + ε) ^ m < 1 - (2 : ℝ)⁻¹ ^ m →
      ‖f t‖ ≤ 2 * (η + ε) := by
    intro ε hε hsmall
    set η' := η + ε with hη'
    set C' := C + ε with hC'
    have hη'pos : 0 < η' := by linarith
    have hη'm : 0 < η' ^ m := pow_pos hη'pos m
    obtain ⟨base, hbase⟩ : ∃ base : ℝ → ℝ,
        base = fun s => (η' ^ m)⁻¹ - (m : ℝ) * C' * (s - a) := ⟨_, rfl⟩
    have hbase_lb : ∀ s ∈ Icc a b, (2⁻¹ : ℝ) ^ m * (η' ^ m)⁻¹ < base s := by
      intro s hs
      rw [hbase]
      have h1 : (m : ℝ) * C' * (s - a) ≤ (m : ℝ) * C' * (b - a) := by
        apply mul_le_mul_of_nonneg_left (by linarith [hs.2])
        have : 0 ≤ C' := by linarith
        positivity
      have h2 : (m : ℝ) * C' * (b - a) < (1 - (2 : ℝ)⁻¹ ^ m) * (η' ^ m)⁻¹ := by
        rw [← div_eq_mul_inv, lt_div_iff₀ hη'm]
        exact hsmall
      linarith
    have hbase_pos : ∀ s ∈ Icc a b, 0 < base s := fun s hs =>
      lt_of_le_of_lt (by positivity) (hbase_lb s hs)
    have hbase_d : ∀ s, HasDerivAt base (-((m : ℝ) * C')) s := fun s => by
      have h := (((hasDerivAt_id s).sub_const a).const_mul ((m : ℝ) * C')).const_sub
        ((η' ^ m)⁻¹)
      rw [hbase]
      exact h.congr_deriv (by ring)
    set p : ℝ := -(m : ℝ)⁻¹ with hp
    obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, B = fun s => base s ^ p := ⟨_, rfl⟩
    have hBpos : ∀ s ∈ Icc a b, 0 < B s := fun s hs => by
      rw [hB]
      exact Real.rpow_pos_of_pos (hbase_pos s hs) _
    have hBpow : ∀ s ∈ Icc a b, B s ^ m = (base s)⁻¹ := fun s hs => by
      rw [show B s = base s ^ p by rw [hB], hp, Real.rpow_neg (hbase_pos s hs).le, inv_pow,
        Real.rpow_inv_natCast_pow (hbase_pos s hs).le hm]
    have hBd : ∀ s ∈ Icc a b, HasDerivAt B (C' * B s ^ (m + 1)) s := fun s hs => by
      have h := (hbase_d s).rpow_const (p := p) (Or.inl (hbase_pos s hs).ne')
      have e3 : B s ^ (m + 1) = base s ^ (p - 1) := by
        rw [show B s = base s ^ p by rw [hB], ← Real.rpow_natCast,
          ← Real.rpow_mul (hbase_pos s hs).le]
        congr 1
        rw [hp]
        push_cast
        field_simp
        ring
      rw [e3]
      have e4 : B = fun s => base s ^ p := hB
      rw [e4]
      refine h.congr_deriv ?_
      rw [hp]
      field_simp
    have hcmp := image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (B := B)
      (B' := fun s => C' * B s ^ (m + 1)) hf hf' ?_ ?_ ?_ ?_ ht
    · refine hcmp.trans ?_
      have hBt := hBpos t ht
      rw [← pow_le_pow_iff_left₀ hBt.le (by positivity) hm, hBpow t ht, mul_pow,
        inv_le_comm₀ (hbase_pos t ht) (by positivity), mul_inv, ← inv_pow]
      exact (hbase_lb t ht).le
    · have hBa : B a = η' := by
        have hab' : a ∈ Icc a b := ⟨le_rfl, hab⟩
        rw [← pow_left_inj₀ (hBpos a hab').le hη'pos.le hm, hBpow a hab', hbase]
        simp
      rw [hBa]
      linarith
    · intro s hs
      exact (hBd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hBd s (Ico_subset_Icc_self hs)).hasDerivWithinAt
    · intro x hx hxeq
      have hb := hbound x hx
      rw [hxeq] at hb
      have hBx := hBpos x (Ico_subset_Icc_self hx)
      have h1 : 0 < B x ^ (m + 1) := pow_pos hBx _
      have h2 : C * B x ^ (m + 1) < C' * B x ^ (m + 1) :=
        mul_lt_mul_of_pos_right (by linarith) h1
      show ‖f' x‖ < C' * B x ^ (m + 1)
      linarith
  -- let `ε → 0`
  have hlim : Tendsto (fun ε : ℝ => 2 * (η + ε)) (𝓝[>] 0) (𝓝 (2 * (η + 0))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((by fun_prop : Continuous fun ε : ℝ => 2 * (η + ε)).tendsto 0)
  have h := ge_of_tendsto hlim ((hev.and self_mem_nhdsWithin).mono
    fun ε hε => hmain ε hε.2 hε.1)
  simpa using h

/-- Growth from `ρ' ≥ κ ρ^{k-1}`: `ρ(t)^{2-k} ≤ ρ(a)^{2-k} - (k-2) κ (t - a)`. -/
theorem inv_pow_le_of_deriv_ge {ρ ρ' : ℝ → ℝ} {a b κ : ℝ} {k : ℕ} (hk : 3 ≤ k)
    (hρ : ContinuousOn ρ (Icc a b)) (hρ' : ∀ t ∈ Ico a b, HasDerivWithinAt ρ (ρ' t) (Ici t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < ρ t) (hgrowth : ∀ t ∈ Ico a b, κ * ρ t ^ (k - 1) ≤ ρ' t) :
    ∀ t ∈ Icc a b, (ρ t ^ (k - 2))⁻¹ ≤ (ρ a ^ (k - 2))⁻¹ - ((k : ℝ) - 2) * κ * (t - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have ek : ((m + 3 : ℕ) : ℝ) - 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [e1] at hgrowth
  rw [e2, ek]
  intro t ht
  refine image_le_of_deriv_right_le_deriv_boundary (f := fun t => (ρ t ^ (m + 1))⁻¹)
    (f' := fun t => -(((m + 1 : ℕ) : ℝ) * ρ t ^ (m + 1 - 1) * ρ' t) / (ρ t ^ (m + 1)) ^ 2)
    (B := fun t => (ρ a ^ (m + 1))⁻¹ - ((m : ℝ) + 1) * κ * (t - a))
    (B' := fun _ => -(((m : ℝ) + 1) * κ)) ?_ ?_ ?_ ?_ ?_ ?_ ht
  · exact (hρ.pow (m + 1)).inv₀ (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  · intro t ht
    exact ((hρ' t ht).pow (m + 1)).inv (pow_ne_zero _ (hpos t (Ico_subset_Icc_self ht)).ne')
  · simp
  · fun_prop
  · intro t _
    have h1 := (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul
      (((m : ℝ) + 1) * κ)).const_sub ((ρ a ^ (m + 1))⁻¹)
    exact h1.congr_deriv (by ring)
  · intro t ht
    have hρt := hpos t (Ico_subset_Icc_self ht)
    have hg := hgrowth t ht
    simp only [Nat.add_sub_cancel]
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have h2 : (ρ t ^ (m + 1)) ^ 2 = ρ t ^ m * ρ t ^ (m + 2) := by ring
    rw [h2]
    push_cast
    have hm : 0 ≤ ((m : ℝ) + 1) * ρ t ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hg hm]

/-- Growth from `ρ' ≤ C ρ^{k-1}`: `ρ(t)^{2-k} ≥ ρ(a)^{2-k} - (k-2) C (t - a)`. -/
theorem inv_pow_ge_of_deriv_le {ρ ρ' : ℝ → ℝ} {a b C : ℝ} {k : ℕ} (hk : 3 ≤ k)
    (hρ : ContinuousOn ρ (Icc a b)) (hρ' : ∀ t ∈ Ico a b, HasDerivWithinAt ρ (ρ' t) (Ici t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < ρ t) (hgrowth : ∀ t ∈ Ico a b, ρ' t ≤ C * ρ t ^ (k - 1)) :
    ∀ t ∈ Icc a b, (ρ a ^ (k - 2))⁻¹ - ((k : ℝ) - 2) * C * (t - a) ≤ (ρ t ^ (k - 2))⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have ek : ((m + 3 : ℕ) : ℝ) - 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [e1] at hgrowth
  rw [e2, ek]
  intro t ht
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := fun t => (ρ a ^ (m + 1))⁻¹ - ((m : ℝ) + 1) * C * (t - a))
    (f' := fun _ => -(((m : ℝ) + 1) * C))
    (B := fun t => (ρ t ^ (m + 1))⁻¹)
    (B' := fun t => -(((m + 1 : ℕ) : ℝ) * ρ t ^ (m + 1 - 1) * ρ' t) / (ρ t ^ (m + 1)) ^ 2)
    ?_ ?_ ?_ ?_ ?_ ?_ ht
  · fun_prop
  · intro t _
    have h1 := (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul
      (((m : ℝ) + 1) * C)).const_sub ((ρ a ^ (m + 1))⁻¹)
    exact h1.congr_deriv (by ring)
  · simp
  · exact (hρ.pow (m + 1)).inv₀ (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  · intro t ht
    exact ((hρ' t ht).pow (m + 1)).inv (pow_ne_zero _ (hpos t (Ico_subset_Icc_self ht)).ne')
  · intro t ht
    have hρt := hpos t (Ico_subset_Icc_self ht)
    have hg := hgrowth t ht
    simp only [Nat.add_sub_cancel]
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    have h2 : (ρ t ^ (m + 1)) ^ 2 = ρ t ^ m * ρ t ^ (m + 2) := by ring
    rw [h2]
    push_cast
    have hm : 0 ≤ ((m : ℝ) + 1) * ρ t ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hg hm]

/-- Time change: if `Φ' = λ(t) X(Φ)` on `(-∞, t']` with `λ > 0` continuous and
`∫_{-∞}^{t'} λ = ∞` (expressed through a lower bound `g' ≤ λ` with `g → -∞`), then the
reparametrization of `Φ` by `τ = ∫_{t'}^t λ` is a solution of `Y' = X(Y)` on `(-∞, 0]`. -/
theorem time_change {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (X : Y → Y)
    (Φ : ℝ → Y) (lam : ℝ → ℝ) (t' : ℝ)
    (hlam : ContinuousOn lam (Iic t')) (hpos : ∀ t ≤ t', 0 < lam t)
    (hΦ : ∀ t ≤ t', HasDerivWithinAt Φ (lam t • X (Φ t)) (Iic t') t)
    (hdiv : ∃ g g' : ℝ → ℝ, Tendsto g atBot atBot ∧ (∀ t ≤ t', HasDerivAt g (g' t) t) ∧
      ∀ t ≤ t', g' t ≤ lam t) :
    ∃ Yc : ℝ → Y, Yc 0 = Φ t' ∧ (∀ τ ≤ 0, HasDerivWithinAt Yc (X (Yc τ)) (Iic 0) τ) ∧
      ∀ τ ≤ 0, ∃ t ≤ t', Yc τ = Φ t := by
  obtain ⟨g, g', hg, hgd, hgl⟩ := hdiv
  -- extend `lam` past `t'` by the constant `lam t'`
  obtain ⟨lam₁, hlam₁⟩ : ∃ lam₁ : ℝ → ℝ, lam₁ = fun t => lam (min t t') := ⟨_, rfl⟩
  have hlam₁c : Continuous lam₁ := by
    rw [hlam₁]
    exact hlam.comp_continuous (continuous_id.min continuous_const)
      (fun t => min_le_right t t')
  have hlam₁pos : ∀ t, 0 < lam₁ t := fun t => by
    rw [hlam₁]
    exact hpos _ (min_le_right t t')
  have hlam₁eq : ∀ t ≤ t', lam₁ t = lam t := fun t ht => by
    simp only [hlam₁, min_eq_left ht]
  -- the new time `Λ t = ∫_{t'}^t lam₁`
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ → ℝ, Λ = fun t => ∫ s in t'..t, lam₁ s := ⟨_, rfl⟩
  have hΛd : ∀ t, HasDerivAt Λ (lam₁ t) t := fun t => by
    rw [hΛ]
    exact (hlam₁c.integral_hasStrictDerivAt t' t).hasDerivAt
  have hΛmono : StrictMono Λ := strictMono_of_hasDerivAt_pos hΛd hlam₁pos
  have hΛcont : Continuous Λ := continuous_iff_continuousAt.2 fun t => (hΛd t).continuousAt
  have hΛ0 : Λ t' = 0 := by
    rw [hΛ]
    simp
  have hΛtop : Tendsto Λ atTop atTop := by
    have h1 : ∀ t ≥ t', Λ t = (t - t') * lam t' := by
      intro t ht
      rw [hΛ]
      simp only
      rw [intervalIntegral.integral_congr (g := fun _ => lam t') ?_]
      · rw [intervalIntegral.integral_const, smul_eq_mul]
      · intro s hs
        rw [uIcc_of_le ht] at hs
        simp only [hlam₁, min_eq_right hs.1]
    have h2 : Tendsto (fun t => (t - t') * lam t') atTop atTop :=
      Tendsto.atTop_mul_const (hpos t' le_rfl)
        (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t') tendsto_id)
    exact h2.congr' ((eventually_ge_atTop t').mono fun t ht => (h1 t ht).symm)
  have hΛbot : Tendsto Λ atBot atBot := by
    -- `Λ - g` is monotone on `(-∞, t']`
    have hmono : MonotoneOn (fun t => Λ t - g t) (Iic t') := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic t') (f' := fun t => lam₁ t - g' t)
      · intro t ht
        exact ((hΛd t).continuousAt.sub (hgd t ht).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Iic] at ht
        exact ((hΛd t).sub (hgd t (le_of_lt ht))).hasDerivWithinAt
      · intro t ht
        rw [interior_Iic] at ht
        have h1 := hgl t (le_of_lt ht)
        have h2 := hlam₁eq t (le_of_lt ht)
        show 0 ≤ lam₁ t - g' t
        linarith
    have hle : ∀ t ≤ t', Λ t ≤ g t - g t' := by
      intro t ht
      have h1 := hmono (mem_Iic.2 ht) (mem_Iic.2 le_rfl) ht
      simp only [hΛ0] at h1
      linarith
    have h2 : Tendsto (fun t => g t - g t') atBot atBot := by
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-g t') hg
    exact tendsto_atBot_mono' atBot ((eventually_le_atBot t').mono fun t ht => hle t ht) h2
  -- invert `Λ`
  have hsurj : Function.Surjective Λ := hΛcont.surjective hΛtop hΛbot
  set e := StrictMono.orderIsoOfSurjective Λ hΛmono hsurj with he
  have hecoe : ∀ t, e t = Λ t := fun t => by
    rw [he, StrictMono.coe_orderIsoOfSurjective]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ, σ = e.symm := ⟨_, rfl⟩
  have hΛσ : ∀ τ, Λ (σ τ) = τ := fun τ => by
    rw [← hecoe, hσ, OrderIso.apply_symm_apply]
  have hσΛ : ∀ t, σ (Λ t) = t := fun t => by
    rw [← hecoe, hσ, OrderIso.symm_apply_apply]
  have hσcont : Continuous σ := by
    rw [hσ]
    exact e.symm.continuous
  have hσmono : Monotone σ := by
    rw [hσ]
    exact e.symm.monotone
  have hσ0 : σ 0 = t' := by
    rw [← hΛ0]
    exact hσΛ t'
  have hσle : ∀ τ ≤ 0, σ τ ≤ t' := fun τ hτ => by
    rw [← hσ0]
    exact hσmono hτ
  have hσd : ∀ τ, HasDerivAt σ (lam₁ (σ τ))⁻¹ τ := fun τ =>
    HasDerivAt.of_local_left_inverse hσcont.continuousAt (hΛd (σ τ)) (hlam₁pos _).ne'
      (Eventually.of_forall hΛσ)
  refine ⟨Φ ∘ σ, ?_, ?_, ?_⟩
  · simp [hσ0]
  · intro τ hτ
    have h1 := hΦ (σ τ) (hσle τ hτ)
    have h2 := (hσd τ).hasDerivWithinAt (s := Iic 0)
    have h3 := h1.scomp τ h2 (fun x hx => hσle x hx)
    convert h3 using 1
    rw [hlam₁eq _ (hσle τ hτ), smul_smul, inv_mul_cancel₀ (hpos _ (hσle τ hτ)).ne', one_smul,
      Function.comp_apply]
  · intro τ hτ
    exact ⟨σ τ, hσle τ hτ, rfl⟩

/-- Iterated derivatives along a line are iterated Fréchet derivatives on the diagonal. -/
theorem iteratedDeriv_comp_line {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : V → W} (hf : ContDiff ℝ ∞ f) (x y : V)
    (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => f (x + s • y)) 0 = iteratedFDeriv ℝ j f x (fun _ => y) := by
  have key : ∀ j : ℕ, iteratedDeriv j (fun s : ℝ => f (x + s • y)) =
      fun s => iteratedFDeriv ℝ j f (x + s • y) (fun _ => y) := by
    intro j
    induction j with
    | zero => ext s; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext s
      have h1 : ContDiffAt ℝ (n + 1) f (x + s • y) :=
        (hf.of_le (mod_cast le_top)).contDiffAt
      exact h1.deriv_fderiv_add_smul
  simpa using congr_fun (key j) 0

end S2S
