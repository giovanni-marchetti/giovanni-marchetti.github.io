import SaddleToSaddle.Flatness

/-!
# Gradient-flow trajectories

ODE facts used throughout: maximal solutions extend while they stay bounded; uniqueness and
continuous dependence on initial conditions (from Mathlib's Grönwall estimates); invariance of
the subspaces `S_A` ("Consequences" of Lemma 1); decrease of the loss; critical points;
strong monotonicity of `∇F` near a non-degenerate minimum of `F_A`.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

/-! ### Maximal forward solutions -/

section MaxFwd

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {V : X → X} {γ : ℝ → X} {D : Set ℝ}

theorem IsMaxFwd.Icc_subset (h : IsMaxFwd V γ D) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) :
    Icc a b ⊆ D :=
  h.ordConnected.out ha hb

theorem IsMaxFwd.nonneg (h : IsMaxFwd V γ D) {t : ℝ} (ht : t ∈ D) : 0 ≤ t :=
  h.subset_Ici ht

theorem IsMaxFwd.Icc_zero_subset (h : IsMaxFwd V γ D) {t : ℝ} (ht : t ∈ D) : Icc 0 t ⊆ D :=
  h.Icc_subset h.zero_mem ht

theorem IsMaxFwd.continuousOn (h : IsMaxFwd V γ D) : ContinuousOn γ D := fun t ht =>
  (h.sol t ht).continuousWithinAt.mono h.subset_Ici

theorem IsMaxFwd.hasDerivAt (h : IsMaxFwd V γ D) {t : ℝ} (ht : t ∈ D) (ht0 : 0 < t) :
    HasDerivAt γ (V (γ t)) t :=
  (h.sol t ht).hasDerivAt (Ici_mem_nhds ht0)

/-- Restriction of a maximal solution to a compact interval in its domain. -/
theorem IsMaxFwd.hasDerivWithinAt_Icc (h : IsMaxFwd V γ D) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) :
    ∀ t ∈ Icc a b, HasDerivWithinAt γ (V (γ t)) (Icc a b) t := fun t ht =>
  (h.sol t (h.Icc_subset ha hb ht)).mono ((h.Icc_subset ha hb).trans h.subset_Ici)

/-- Blow-up alternative: a maximal solution that stays bounded on `[a, b] ∩ D` is defined on all
of `[a, b]`. -/
theorem IsMaxFwd.Icc_subset_of_bounded (h : IsMaxFwd V γ D) {a b R : ℝ} (ha : a ∈ D)
    (hR : ∀ t ∈ Icc a b, t ∈ D → ‖γ t‖ ≤ R) : Icc a b ⊆ D := by
  by_contra hsub
  rw [Set.not_subset] at hsub
  obtain ⟨t₀, ht₀, ht₀D⟩ := hsub
  have hTne : (Icc a b \ D).Nonempty := ⟨t₀, ht₀, ht₀D⟩
  have hTbdd : BddBelow (Icc a b \ D) := ⟨a, fun t ht => ht.1.1⟩
  have hac : a ≤ sInf (Icc a b \ D) := le_csInf hTne (fun t ht => ht.1.1)
  have hcb : sInf (Icc a b \ D) ≤ b := (csInf_le hTbdd ⟨ht₀, ht₀D⟩).trans ht₀.2
  have ha0 : 0 ≤ a := h.nonneg ha
  have hc0 : 0 ≤ sInf (Icc a b \ D) := ha0.trans hac
  have hsub : Ico 0 (sInf (Icc a b \ D)) ⊆ D := by
    intro t ht
    by_cases hta : t ≤ a
    · exact h.Icc_zero_subset ha ⟨ht.1, hta⟩
    · rw [not_le] at hta
      by_contra htD
      have htT : t ∈ Icc a b \ D := ⟨⟨hta.le, ht.2.le.trans hcb⟩, htD⟩
      exact absurd (csInf_le hTbdd htT) (not_le.mpr ht.2)
  have hbdd : Bornology.IsBounded (γ '' Ico 0 (sInf (Icc a b \ D))) := by
    have h1 : Bornology.IsBounded (γ '' Icc 0 a) :=
      (isCompact_Icc.image_of_continuousOn (h.continuousOn.mono (h.Icc_zero_subset ha))).isBounded
    have h2 : Bornology.IsBounded (γ '' Ico a (sInf (Icc a b \ D))) := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨R, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact hR t ⟨ht.1, ht.2.le.trans hcb⟩ (hsub ⟨ha0.trans ht.1, ht.2⟩)
    refine (h1.union h2).subset ?_
    rw [← image_union]
    apply image_mono
    intro t ht
    by_cases hta : t ≤ a
    · exact Or.inl ⟨ht.1, hta⟩
    · exact Or.inr ⟨(not_le.mp hta).le, ht.2⟩
  obtain ⟨ε, hε, hD⟩ := h.maximal _ hc0 hsub hbdd
  obtain ⟨t, htT, htc⟩ := exists_lt_of_csInf_lt hTne (lt_add_of_pos_right _ hε)
  exact htT.2 (hD ⟨hc0.trans (csInf_le hTbdd htT), htc⟩)

end MaxFwd

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- Lipschitz bound for `∇F` on balls. -/
theorem gf_lipschitzOnWith (hF : ContDiff ℝ ∞ F) (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L (gf F) (closedBall 0 R) :=
  (gf_contDiff hF).contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall 0 R)
    (isCompact_closedBall 0 R)

/-- Uniqueness of gradient-flow trajectories on a compact interval, forward and backward. -/
theorem gf_unique (hF : ContDiff ℝ ∞ F) {γ₁ γ₂ : ℝ → Θ ι E} {a b c : ℝ} (hc : c ∈ Icc a b)
    (h₁ : ∀ t ∈ Icc a b, HasDerivWithinAt γ₁ (gf F (γ₁ t)) (Icc a b) t)
    (h₂ : ∀ t ∈ Icc a b, HasDerivWithinAt γ₂ (gf F (γ₂ t)) (Icc a b) t)
    (heq : γ₁ c = γ₂ c) : EqOn γ₁ γ₂ (Icc a b) := by
  have hc₁ : ContinuousOn γ₁ (Icc a b) := fun t ht => (h₁ t ht).continuousWithinAt
  have hc₂ : ContinuousOn γ₂ (Icc a b) := fun t ht => (h₂ t ht).continuousWithinAt
  obtain ⟨R₁, hR₁⟩ :=
    (isCompact_Icc.image_of_continuousOn hc₁).isBounded.subset_closedBall (0 : Θ ι E)
  obtain ⟨R₂, hR₂⟩ :=
    (isCompact_Icc.image_of_continuousOn hc₂).isBounded.subset_closedBall (0 : Θ ι E)
  obtain ⟨L, hL⟩ := gf_lipschitzOnWith hF (max R₁ R₂)
  have hm₁ : ∀ t ∈ Icc a b, γ₁ t ∈ closedBall (0 : Θ ι E) (max R₁ R₂) := fun t ht =>
    closedBall_subset_closedBall (le_max_left _ _) (hR₁ (mem_image_of_mem _ ht))
  have hm₂ : ∀ t ∈ Icc a b, γ₂ t ∈ closedBall (0 : Θ ι E) (max R₁ R₂) := fun t ht =>
    closedBall_subset_closedBall (le_max_right _ _) (hR₂ (mem_image_of_mem _ ht))
  have hcb : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
  have hac : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
  intro t ht
  rcases le_total c t with hct | htc
  · refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => gf F)
      (s := fun _ => closedBall 0 (max R₁ R₂)) (K := L) (fun _ _ => hL) (hc₁.mono hcb) ?_
      (fun s hs => hm₁ s (hcb (Ico_subset_Icc_self hs))) (hc₂.mono hcb) ?_
      (fun s hs => hm₂ s (hcb (Ico_subset_Icc_self hs))) heq ⟨hct, ht.2⟩
    · intro s hs
      exact (h₁ s (hcb (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hc.1.trans hs.1, hs.2⟩)
    · intro s hs
      exact (h₂ s (hcb (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hc.1.trans hs.1, hs.2⟩)
  · refine ODE_solution_unique_of_mem_Icc_left (v := fun _ => gf F)
      (s := fun _ => closedBall 0 (max R₁ R₂)) (K := L) (fun _ _ => hL) (hc₁.mono hac) ?_
      (fun s hs => hm₁ s (hac (Ioc_subset_Icc_self hs))) (hc₂.mono hac) ?_
      (fun s hs => hm₂ s (hac (Ioc_subset_Icc_self hs))) heq ⟨ht.1, htc⟩
    · intro s hs
      exact (h₁ s (hac (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans hc.2⟩)
    · intro s hs
      exact (h₂ s (hac (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans hc.2⟩)

/-- Time reversal of a differentiable curve on a compact interval. -/
private lemma hasDerivWithinAt_Icc_comp_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f f' : ℝ → X} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t) :
    ∀ t ∈ Icc (-b) (-a), HasDerivWithinAt (fun s => f (-s)) (-f' (-t)) (Icc (-b) (-a)) t := by
  intro t ht
  have hmt : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) := by
    intro s hs
    exact ⟨le_neg.mp hs.2, neg_le.mp hs.1⟩
  have h1 : HasDerivWithinAt f (f' (-t)) (Icc a b) (-t) := h (-t) (hmt ht)
  have h2 : HasDerivWithinAt (Neg.neg : ℝ → ℝ) (-1) (Icc (-b) (-a)) t :=
    (hasDerivAt_neg t).hasDerivWithinAt
  have h3 := h1.scomp t h2 hmt
  rw [neg_one_smul] at h3
  exact h3

/-- Time shift of a solution on a compact interval. -/
private lemma hasDerivWithinAt_Icc_comp_shift {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : ℝ → X} {v : X → X} {c c' b : ℝ}
    (h : ∀ t ∈ Icc c' (c' + (b - c)), HasDerivWithinAt f (v (f t)) (Icc c' (c' + (b - c))) t) :
    ∀ t ∈ Icc c b, HasDerivWithinAt (fun s => f (c' + (s - c))) (v (f (c' + (t - c))))
      (Icc c b) t := by
  intro t ht
  have hmt : MapsTo (fun s => c' + (s - c)) (Icc c b) (Icc c' (c' + (b - c))) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h1 : HasDerivWithinAt f (v (f (c' + (t - c)))) (Icc c' (c' + (b - c))) (c' + (t - c)) :=
    h _ (hmt ht)
  have h2 : HasDerivWithinAt (fun s : ℝ => c' + (s - c)) 1 (Icc c b) t :=
    (((hasDerivAt_id' t).sub_const c).const_add c').hasDerivWithinAt
  have h3 := HasDerivWithinAt.scomp (h := fun s : ℝ => c' + (s - c)) (x := t) h1 h2 hmt
  rw [one_smul] at h3
  exact h3

/-- Forward Grönwall estimate for two solutions of `ẋ = v(x)` on `[c, b]`. -/
private lemma fwd_estimate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v : X → X} {L : NNReal} {B : ℝ} (hv : LipschitzOnWith L v (closedBall 0 (B + 1)))
    {γ θ' : ℝ → X} {c b : ℝ}
    (hγB : ∀ t ∈ Icc c b, ‖γ t‖ ≤ B)
    (hγ : ∀ t ∈ Icc c b, HasDerivWithinAt γ (v (γ t)) (Icc c b) t)
    (hθ : ∀ t ∈ Icc c b, HasDerivWithinAt θ' (v (θ' t)) (Icc c b) t)
    (hδ : ‖θ' c - γ c‖ * Real.exp (L * (b - c)) < 1) :
    ∀ t ∈ Icc c b, ‖θ' t - γ t‖ ≤ ‖θ' c - γ c‖ * Real.exp (L * (t - c)) := by
  rcases lt_or_ge b c with hbc | hcb
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hbc)
  have key : ∀ t ∈ Icc c b, (∀ s ∈ Icc c t, ‖θ' s - γ s‖ ≤ 1) →
      ∀ s ∈ Icc c t, ‖θ' s - γ s‖ ≤ ‖θ' c - γ c‖ * Real.exp (L * (s - c)) := by
    intro t ht hK
    have hsub : Icc c t ⊆ Icc c b := Icc_subset_Icc_right ht.2
    have hder : ∀ (g : ℝ → X), (∀ s ∈ Icc c b, HasDerivWithinAt g (v (g s)) (Icc c b) s) →
        ∀ s ∈ Ico c t, HasDerivWithinAt g (v (g s)) (Ici s) s := fun g hg s hs =>
      (hg s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2.trans_le ht.2⟩)
    have hγmem : ∀ s ∈ Ico c t, γ s ∈ closedBall (0 : X) (B + 1) := fun s hs => by
      rw [mem_closedBall, dist_zero_right]
      linarith [hγB s (hsub (Ico_subset_Icc_self hs))]
    have hθmem : ∀ s ∈ Ico c t, θ' s ∈ closedBall (0 : X) (B + 1) := fun s hs => by
      rw [mem_closedBall, dist_zero_right]
      have h1 := hγB s (hsub (Ico_subset_Icc_self hs))
      have h2 := hK s (Ico_subset_Icc_self hs)
      have h3 : ‖θ' s‖ ≤ ‖θ' s - γ s‖ + ‖γ s‖ := by
        simpa using norm_add_le (θ' s - γ s) (γ s)
      linarith
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => v)
      (s := fun _ => closedBall (0 : X) (B + 1)) (K := L) (fun _ _ => hv)
      (fun s hs => (hθ s (hsub hs)).continuousWithinAt.mono hsub) (hder θ' hθ) hθmem
      (fun s hs => (hγ s (hsub hs)).continuousWithinAt.mono hsub) (hder γ hγ) hγmem
      (le_of_eq (dist_eq_norm _ _))
    intro s hs
    rw [← dist_eq_norm]
    exact this s hs
  have hexp : ∀ t ∈ Icc c b, ‖θ' c - γ c‖ * Real.exp (L * (t - c)) ≤
      ‖θ' c - γ c‖ * Real.exp (L * (b - c)) := fun t ht => by
    gcongr
    exact ht.2
  have hboot := bootstrap (f := fun t => θ' t - γ t) (a := c) (b := b)
    (fun t ht => ((hθ t ht).continuousWithinAt.sub (hγ t ht).continuousWithinAt))
    (K := closedBall 0 1) (K' := closedBall 0 (‖θ' c - γ c‖ * Real.exp (L * (b - c))))
    isClosed_closedBall ((closedBall_subset_ball hδ).trans ball_subset_interior_closedBall)
    (by
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖θ' c - γ c‖ ≤ ‖θ' c - γ c‖ * Real.exp (L * (b - c)) := by
        have : 1 ≤ Real.exp (L * (b - c)) :=
          Real.one_le_exp (mul_nonneg L.2 (sub_nonneg.mpr hcb))
        nlinarith [norm_nonneg (θ' c - γ c)]
      linarith)
    (fun t ht hK => by
      rw [mem_closedBall, dist_zero_right]
      refine (key t ht (fun s hs => ?_) t ⟨ht.1, le_rfl⟩).trans (hexp t ht)
      have := hK s hs
      rwa [mem_closedBall, dist_zero_right] at this)
  intro t ht
  refine key b ⟨hcb, le_rfl⟩ (fun s hs => ?_) t ht
  have := hboot s hs
  rw [mem_closedBall, dist_zero_right] at this
  linarith

/-- Continuous dependence on initial conditions, forward and backward in time, near a reference
trajectory `γ` defined on `[a, b]`. -/
theorem gf_cont_dep (hF : ContDiff ℝ ∞ F) {γ : ℝ → Θ ι E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (gf F (γ t)) (Icc a b) t) :
    ∃ δ₀ > 0, ∃ K > 0, ∀ θ' : ℝ → Θ ι E,
      (∀ t ∈ Icc a b, HasDerivWithinAt θ' (gf F (θ' t)) (Icc a b) t) →
      ∀ c ∈ Icc a b, ‖θ' c - γ c‖ ≤ δ₀ → ∀ t ∈ Icc a b, ‖θ' t - γ t‖ ≤ K * ‖θ' c - γ c‖ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht => (hγ t ht).continuousWithinAt)
  obtain ⟨L, hL⟩ := gf_lipschitzOnWith hF (B + 1)
  have hL' : LipschitzOnWith L (fun x => -gf F x) (closedBall 0 (B + 1)) := fun x hx y hy => by
    simpa only [edist_neg_neg] using hL hx hy
  have hK0 : 0 < Real.exp (L * (b - a)) := Real.exp_pos _
  refine ⟨1 / (2 * Real.exp (L * (b - a))), by positivity, Real.exp (L * (b - a)), hK0,
    fun θ' hθ' c hc hδ t ht => ?_⟩
  have hδK : ‖θ' c - γ c‖ * Real.exp (L * (b - a)) ≤ 1 / 2 := by
    calc ‖θ' c - γ c‖ * Real.exp (L * (b - a))
        ≤ 1 / (2 * Real.exp (L * (b - a))) * Real.exp (L * (b - a)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hexp : ∀ x : ℝ, x ≤ b - a →
      ‖θ' c - γ c‖ * Real.exp (L * x) ≤ ‖θ' c - γ c‖ * Real.exp (L * (b - a)) := by
    intro x hx
    gcongr
  rcases le_total c t with hct | htc
  · have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
    have := fwd_estimate hL (fun s hs => hB s (hsub hs)) (fun s hs => (hγ s (hsub hs)).mono hsub)
      (fun s hs => (hθ' s (hsub hs)).mono hsub)
      (by linarith [hexp (b - c) (by linarith [hc.1])]) t ⟨hct, ht.2⟩
    rw [mul_comm (Real.exp _)]
    exact this.trans (hexp _ (by linarith [hc.1, ht.2]))
  · have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
    have hγr := hasDerivWithinAt_Icc_comp_neg (fun s hs => (hγ s (hsub hs)).mono hsub)
    have hθr := hasDerivWithinAt_Icc_comp_neg (fun s hs => (hθ' s (hsub hs)).mono hsub)
    have hBr : ∀ s ∈ Icc (-c) (-a), ‖γ (-s)‖ ≤ B := fun s hs =>
      hB (-s) (hsub ⟨le_neg.mp hs.2, neg_le.mp hs.1⟩)
    have hδr : ‖θ' (-(-c)) - γ (-(-c))‖ * Real.exp (L * (-a - -c)) < 1 := by
      rw [neg_neg]
      linarith [hexp (-a - -c) (by linarith [hc.2])]
    have := fwd_estimate (v := fun x => -gf F x) (γ := fun s => γ (-s)) (θ' := fun s => θ' (-s))
      hL' hBr hγr hθr hδr (-t) ⟨neg_le_neg htc, neg_le_neg ht.1⟩
    simp only [neg_neg] at this
    rw [mul_comm (Real.exp _)]
    exact this.trans (hexp _ (by linarith [hc.2, ht.1]))

/-- Continuous dependence for a maximal forward solution: if it starts close to a reference
trajectory `γ` defined on `[c, b]`, it is defined on `[c, b]` and stays close. -/
theorem gf_cont_dep_maxFwd (hF : ContDiff ℝ ∞ F) {γ : ℝ → Θ ι E} {c b : ℝ} (hcb : c ≤ b)
    (hγ : ∀ t ∈ Icc c b, HasDerivWithinAt γ (gf F (γ t)) (Icc c b) t) :
    ∃ δ₀ > 0, ∃ K > 0, ∀ (θ' : ℝ → Θ ι E) (D : Set ℝ), IsMaxFwd (gf F) θ' D →
      ∀ c' ∈ D, ‖θ' c' - γ c‖ ≤ δ₀ →
        Icc c' (c' + (b - c)) ⊆ D ∧
        ∀ t ∈ Icc c b, ‖θ' (c' + (t - c)) - γ t‖ ≤ K * ‖θ' c' - γ c‖ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht => (hγ t ht).continuousWithinAt)
  obtain ⟨L, hL⟩ := gf_lipschitzOnWith hF (B + 1)
  have hK0 : 0 < Real.exp (L * (b - c)) := Real.exp_pos _
  refine ⟨1 / (2 * Real.exp (L * (b - c))), by positivity, Real.exp (L * (b - c)), hK0,
    fun θ' D hmax c' hc' hδ => ?_⟩
  have hδK : ‖θ' c' - γ c‖ * Real.exp (L * (b - c)) ≤ 1 / 2 := by
    calc ‖θ' c' - γ c‖ * Real.exp (L * (b - c))
        ≤ 1 / (2 * Real.exp (L * (b - c))) * Real.exp (L * (b - c)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hexp : ∀ x : ℝ, x ≤ b - c →
      ‖θ' c' - γ c‖ * Real.exp (L * x) ≤ ‖θ' c' - γ c‖ * Real.exp (L * (b - c)) := by
    intro x hx
    gcongr
  have claim : ∀ b' ∈ Icc c b, c' + (b' - c) ∈ D → ∀ t ∈ Icc c b',
      ‖θ' (c' + (t - c)) - γ t‖ ≤ ‖θ' c' - γ c‖ * Real.exp (L * (t - c)) := by
    intro b' hb' hD t ht
    have hsub : Icc c b' ⊆ Icc c b := Icc_subset_Icc_right hb'.2
    have hθ := hasDerivWithinAt_Icc_comp_shift (c := c) (c' := c') (b := b') (v := gf F)
      (hmax.hasDerivWithinAt_Icc hc' hD)
    have hδ' : ‖θ' (c' + (c - c)) - γ c‖ * Real.exp (L * (b' - c)) < 1 := by
      rw [sub_self, add_zero]
      linarith [hexp (b' - c) (by linarith [hb'.2])]
    have := fwd_estimate (θ' := fun s => θ' (c' + (s - c))) hL (fun s hs => hB s (hsub hs))
      (fun s hs => (hγ s (hsub hs)).mono hsub) hθ hδ' t ht
    simpa only [sub_self, add_zero] using this
  have hsubD : Icc c' (c' + (b - c)) ⊆ D := by
    refine hmax.Icc_subset_of_bounded (R := B + 1) hc' fun t ht htD => ?_
    have hb' : c + (t - c') ∈ Icc c b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have he : c' + (c + (t - c') - c) = t := by ring
    have h1 := claim (c + (t - c')) hb' (by rw [he]; exact htD) (c + (t - c'))
      ⟨hb'.1, le_rfl⟩
    rw [he] at h1
    have h2 := hexp (c + (t - c') - c) (by linarith [hb'.2])
    have h3 := hB _ hb'
    have h4 : ‖θ' t‖ ≤ ‖θ' t - γ (c + (t - c'))‖ + ‖γ (c + (t - c'))‖ := by
      simpa using norm_add_le (θ' t - γ (c + (t - c'))) (γ (c + (t - c')))
    linarith
  refine ⟨hsubD, fun t ht => ?_⟩
  have := claim b ⟨hcb, le_rfl⟩ (hsubD ⟨by linarith, le_rfl⟩) t ht
  rw [mul_comm (Real.exp _)]
  exact this.trans (hexp _ (by linarith [ht.2]))

/-- A componentwise bound gives a bound on the norm. -/
private lemma norm_le_of_forall_apply_le {x y : Θ ι E} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ m, ‖x m‖ ≤ K * ‖y m‖) : ‖x‖ ≤ K * ‖y‖ := by
  have h2 : ‖x‖ ^ 2 ≤ (K * ‖y‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h m) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- Invariance of `S_A` ("Consequences" of Lemma 1). -/
theorem S_invariant (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k) {A : Finset ι}
    {γ : ℝ → Θ ι E} {a b c : ℝ} (hc : c ∈ Icc a b)
    (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (gf F (γ t)) (Icc a b) t) (h : γ c ∈ S A) :
    ∀ t ∈ Icc a b, γ t ∈ S A := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun t ht => (hγ t ht).continuousWithinAt)
  obtain ⟨C, hC0, hC⟩ := grad_apply_le hF hk hH B
  set Q : Θ ι E →L[ℝ] Θ ι E := ContinuousLinearMap.id ℝ _ - proj A with hQ
  have hQapply : ∀ x : Θ ι E, ∀ m, Q x m = if m ∈ A then 0 else x m := by
    intro x m
    by_cases hm : m ∈ A <;> simp [hQ, hm]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB c hc)
  have hbound : ∀ t ∈ Icc a b, ‖Q (gf F (γ t))‖ ≤ (C * B ^ (k - 2)) * ‖Q (γ t)‖ := by
    intro t ht
    apply norm_le_of_forall_apply_le (by positivity)
    intro m
    rw [hQapply, hQapply]
    by_cases hm : m ∈ A
    · simp [hm]
    · simp only [hm, ite_false]
      have h1 : ‖(gf F (γ t)) m‖ = ‖(gradient F (γ t)) m‖ := by simp [gf]
      rw [h1]
      have h2 := hC m (γ t) (hB t ht)
      have h3 : ‖γ t m‖ ≤ B := (norm_apply_le _ _).trans (hB t ht)
      have h4 : ‖γ t m‖ ^ (k - 1) ≤ B ^ (k - 2) * ‖γ t m‖ := by
        have : k - 1 = (k - 2) + 1 := by omega
        rw [this, pow_succ]
        gcongr
      calc ‖(gradient F (γ t)) m‖ ≤ C * ‖γ t m‖ ^ (k - 1) := h2
        _ ≤ C * (B ^ (k - 2) * ‖γ t m‖) := by gcongr
        _ = C * B ^ (k - 2) * ‖γ t m‖ := by ring
  have hder : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => Q (γ t)) (Q (gf F (γ t))) (Icc a b) t :=
    fun t ht => Q.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  have hcont : ContinuousOn (fun t => Q (γ t)) (Icc a b) := fun t ht =>
    (hder t ht).continuousWithinAt
  have hQc : Q (γ c) = 0 := by
    simp [hQ, proj_eq_self_of_mem_S h]
  have hmemS : ∀ t, Q (γ t) = 0 → γ t ∈ S A := by
    intro t ht m hm
    have := congrArg (fun x : Θ ι E => x m) ht
    simpa [hQapply, hm] using this
  intro t ht
  apply hmemS
  rcases le_total c t with hct | htc
  · have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (hcont.mono hsub)
      (fun s hs => (hder s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hc.1.trans hs.1, hs.2⟩)) hQc
      (fun s hs => hbound s (hsub (Ico_subset_Icc_self hs))) t ⟨hct, ht.2⟩
  · have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
    have hderr := hasDerivWithinAt_Icc_comp_neg (fun s hs => (hder s (hsub hs)).mono hsub)
    have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := fun s => Q (γ (-s)))
      (fun s hs => (hderr s hs).continuousWithinAt)
      (fun s hs => (hderr s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (by simpa using hQc)
      (fun s hs => by
        rw [norm_neg]
        exact hbound (-s) (hsub ⟨le_neg.mp hs.2.le, neg_le.mp hs.1⟩))
      (-t) ⟨neg_le_neg htc, neg_le_neg ht.1⟩
    simpa using this

/-- The loss decreases along gradient-flow trajectories. -/
theorem hasDerivWithinAt_F_comp (hF : ContDiff ℝ ∞ F) {γ : ℝ → Θ ι E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt γ (gf F (γ t)) s t) :
    HasDerivWithinAt (fun t => F (γ t)) (-‖gradient F (γ t)‖ ^ 2) s t := by
  have hd : HasFDerivAt F (fderiv ℝ F (γ t)) (γ t) :=
    ((hF.differentiable (by simp)) (γ t)).hasFDerivAt
  have h2 : HasDerivWithinAt (fun t => F (γ t)) (fderiv ℝ F (γ t) (gf F (γ t))) s t :=
    hd.comp_hasDerivWithinAt t h
  convert h2 using 1
  rw [← inner_gradient, gf, inner_neg_right, real_inner_self_eq_norm_sq]

/-- Critical points of `F_A` are critical points of `F` ("Consequences" of Lemma 1). -/
theorem gradient_eq_zero_of_isNondegMin (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
    {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) : gradient F θ₀ = 0 := by
  ext m
  by_cases hm : m ∈ A
  · have h1 : ⟪(gradient F θ₀) m, (gradient F θ₀) m⟫ = 0 := by
      rw [inner_gradient_single]
      exact hmin.crit _ (single_mem_S hm _)
    rw [inner_self_eq_zero] at h1
    simpa using h1
  · simpa using grad_apply_eq_zero hF hk hH (hmin.mem m hm)

set_option maxSynthPendingDepth 3 in
/-- Strong monotonicity of `∇F` in the directions of `S_A` near a non-degenerate local minimum
of `F_A`. -/
theorem strong_mono (hF : ContDiff ℝ ∞ F) {A : Finset ι} {θ₀ : Θ ι E}
    (hmin : IsNondegMin F A θ₀) :
    ∃ μ r : ℝ, 0 < μ ∧ 0 < r ∧ ∀ x y : Θ ι E, x ∈ closedBall θ₀ r → y ∈ closedBall θ₀ r →
      x - y ∈ S A → μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, gradient F x - gradient F y⟫ := by
  obtain ⟨c, hc, hpos⟩ := hmin.posdef
  have hF1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hcont2 : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv (by simp)
  have hdiff1 : Differentiable ℝ (fderiv ℝ F) := hF1.differentiable (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.continuous_iff.mp hcont2 θ₀ (c / 2) (by positivity)
  refine ⟨c / 2, ε / 2, by positivity, by positivity, fun x y hx hy hxy => ?_⟩
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, y + s • (x - y) ∈ closedBall θ₀ (ε / 2) := by
    intro s hs
    have : y + s • (x - y) = (1 - s) • y + s • x := by module
    rw [this]
    exact (convex_closedBall θ₀ (ε / 2)) hy hx (by linarith [hs.2]) hs.1 (by ring)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ F (y + s • (x - y)) (x - y))
      (fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) s := by
      simpa using ((hasDerivAt_id s).smul_const (x - y)).const_add y
    have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (y + s • (x - y)))
        (y + s • (x - y)) := (hdiff1 _).hasFDerivAt
    have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ F (y + s • (x - y)))
        (fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y)) s :=
      HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => y + s • (x - y)) s h2 h1
    have h4 := h3.clm_apply (hasDerivAt_const s (x - y))
    simpa using h4
  obtain ⟨s, hs, hs'⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => fderiv ℝ F (y + s • (x - y)) (x - y))
    (fun s : ℝ => fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y)) zero_lt_one
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt) (fun s _ => hderiv s)
  have hlow : c / 2 * ‖x - y‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y) := by
    have hD := hpos (x - y) hxy
    have hclose : ‖fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) - fderiv ℝ (fderiv ℝ F) θ₀‖ < c / 2 := by
      rw [← dist_eq_norm]
      apply hball
      have := hseg s ⟨hs.1.le, hs.2.le⟩
      rw [mem_closedBall] at this
      linarith
    have hdiffb : |fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y) -
        fderiv ℝ (fderiv ℝ F) θ₀ (x - y) (x - y)| ≤ c / 2 * ‖x - y‖ ^ 2 := by
      have : fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y) -
          fderiv ℝ (fderiv ℝ F) θ₀ (x - y) (x - y) =
          (fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) - fderiv ℝ (fderiv ℝ F) θ₀) (x - y) (x - y) := by
        simp
      rw [this, ← Real.norm_eq_abs]
      calc _ ≤ ‖(fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) - fderiv ℝ (fderiv ℝ F) θ₀) (x - y)‖ *
            ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) - fderiv ℝ (fderiv ℝ F) θ₀‖ * ‖x - y‖ *
            ‖x - y‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ c / 2 * ‖x - y‖ * ‖x - y‖ := by gcongr
        _ = c / 2 * ‖x - y‖ ^ 2 := by ring
    have := (abs_le.mp hdiffb).1
    nlinarith
  have hslope : fderiv ℝ (fderiv ℝ F) (y + s • (x - y)) (x - y) (x - y) =
      ⟪x - y, gradient F x - gradient F y⟫ := by
    rw [hs']
    simp only [one_smul, zero_smul, add_zero, sub_zero, div_one, add_sub_cancel]
    rw [inner_sub_right, real_inner_comm, inner_gradient, real_inner_comm, inner_gradient]
  linarith

end S2S
