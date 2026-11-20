import SaddleToSaddle.Basic

/-!
# Maximal solutions and the blow-up alternative

An autonomous ODE `ẋ = V(x)` with a `C¹` vector field on a finite-dimensional space has a maximal
forward solution `[0, T⁺) → X` for every initial value, and if it is bounded on `[0, b)` then it
extends beyond `b` (Teschl, Theorem 2.13 and Corollary 2.15). Proved from Mathlib's local existence
(Picard–Lindelöf) and uniqueness (Grönwall): the maximal solution is the union of all solutions on
compact intervals, and a bounded solution is extended using a uniform local existence time on a
compact set.
-/

open scoped ContDiff Topology
open Set Filter Metric

noncomputable section

namespace S2S

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Uniform local existence on a compact set. -/
private lemma uniform_local_existence (V : X → X) (hV : ContDiff ℝ 1 V) {K : Set X} (hK : IsCompact K) :
    ∃ ε > 0, ∀ x ∈ K, ∃ α : ℝ → X, α 0 = x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (V (α t)) t := by
  have h : ∀ x₀ : X, ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → X,
      α 0 = x ∧ ∀ t ∈ Ioo (0 - ε) (0 + ε), HasDerivAt α (V (α t)) t :=
    fun x₀ => ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hV.contDiffAt 0
  choose r hr ε hε hα using h
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (r x))
    (fun x _ => ball_mem_nhds x (hr x))
  by_cases ht : t.Nonempty
  · refine ⟨t.inf' ht ε, (Finset.lt_inf'_iff ht).mpr fun x _ => hε x, fun x hx => ?_⟩
    obtain ⟨x₀, hx₀t, hx₀⟩ := mem_iUnion₂.mp (hcover hx)
    obtain ⟨α, hα0, hαd⟩ := hα x₀ x (ball_subset_closedBall hx₀)
    refine ⟨α, hα0, fun s hs => hαd s ?_⟩
    have hle : t.inf' ht ε ≤ ε x₀ := Finset.inf'_le _ hx₀t
    constructor <;> [linarith [hs.1]; linarith [hs.2]]
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    obtain ⟨x₀, hx₀t, -⟩ := mem_iUnion₂.mp (hcover hx)
    exact absurd ⟨x₀, hx₀t⟩ ht

/-- Uniqueness of solutions on `[0, T]` with the same initial value. -/
private lemma uniq (V : X → X) (hV : ContDiff ℝ 1 V) {γ₁ γ₂ : ℝ → X} {T : ℝ}
    (h₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ₁ (V (γ₁ t)) (Icc 0 T) t)
    (h₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ₂ (V (γ₂ t)) (Icc 0 T) t) (h0 : γ₁ 0 = γ₂ 0) :
    EqOn γ₁ γ₂ (Icc 0 T) := by
  have hc₁ : ContinuousOn γ₁ (Icc 0 T) := fun t ht => (h₁ t ht).continuousWithinAt
  have hc₂ : ContinuousOn γ₂ (Icc 0 T) := fun t ht => (h₂ t ht).continuousWithinAt
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
  set R := max R₁ R₂
  obtain ⟨L, hL⟩ := (hV.contDiffOn (s := closedBall (0 : X) R)).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => V) (s := fun _ => closedBall 0 R)
    (K := L) (fun _ _ => hL) hc₁ ?_ ?_ hc₂ ?_ ?_ h0
  · intro t ht
    exact (h₁ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact mem_closedBall_zero_iff.mpr ((hR₁ t (Ico_subset_Icc_self ht)).trans (le_max_left _ _))
  · intro t ht
    exact (h₂ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact mem_closedBall_zero_iff.mpr ((hR₂ t (Ico_subset_Icc_self ht)).trans (le_max_right _ _))

/-- Gluing two solutions at a time `c`. -/
private lemma glue (V : X → X) {γ₁ γ₂ : ℝ → X} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (h₁ : ∀ t ∈ Icc a c, HasDerivWithinAt γ₁ (V (γ₁ t)) (Icc a c) t)
    (h₂ : ∀ t ∈ Icc c b, HasDerivWithinAt γ₂ (V (γ₂ t)) (Icc c b) t) (hc : γ₁ c = γ₂ c) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => if s ≤ c then γ₁ s else γ₂ s)
      (V ((fun s => if s ≤ c then γ₁ s else γ₂ s) t)) (Icc a b) t := by
  set g : ℝ → X := fun s => if s ≤ c then γ₁ s else γ₂ s with hg
  have hg₁ : EqOn g γ₁ (Icc a c) := fun s hs => by simp [hg, hs.2]
  have hg₂ : EqOn g γ₂ (Icc c b) := fun s hs => by
    by_cases h : s ≤ c
    · have : s = c := le_antisymm h hs.1
      subst this; simp [hg, hc]
    · simp [hg, h]
  have hsplit : Icc a b = Icc a c ∪ Icc c b := (Icc_union_Icc_eq_Icc hac hcb).symm
  intro t ht
  have hd₁ : t ∈ Icc a c → HasDerivWithinAt g (V (g t)) (Icc a c) t := fun htc => by
    rw [hg₁ htc]; exact (h₁ t htc).congr hg₁ (hg₁ htc)
  have hd₂ : t ∈ Icc c b → HasDerivWithinAt g (V (g t)) (Icc c b) t := fun htc => by
    rw [hg₂ htc]; exact (h₂ t htc).congr hg₂ (hg₂ htc)
  rw [hsplit]
  rcases lt_trichotomy t c with htc | htc | htc
  · have hmem : t ∈ Icc a c := ⟨ht.1, htc.le⟩
    refine (hd₁ hmem).mono_of_mem_nhdsWithin ?_
    refine mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds htc)) ?_
    rintro s ⟨hs1 | hs1, hs2⟩
    · exact hs1
    · exact absurd hs1.1 (not_le.mpr hs2)
  · subst htc
    exact (hd₁ ⟨ht.1, le_rfl⟩).union (hd₂ ⟨le_rfl, ht.2⟩)
  · have hmem : t ∈ Icc c b := ⟨htc.le, ht.2⟩
    refine (hd₂ hmem).mono_of_mem_nhdsWithin ?_
    refine mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds htc)) ?_
    rintro s ⟨hs1 | hs1, hs2⟩
    · exact absurd hs1.2 (not_le.mpr hs2)
    · exact hs1

/-- **Maximal solutions** with the blow-up alternative. -/
theorem exists_isMaxFwd (V : X → X) (hV : ContDiff ℝ 1 V) (x₀ : X) :
    ∃ γ D, IsMaxFwd V γ D ∧ γ 0 = x₀ := by
  classical
  -- solutions on closed intervals `[0, T]`
  set Sol : (ℝ → X) → ℝ → Prop := fun γ T =>
    γ 0 = x₀ ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (V (γ t)) (Icc 0 T) t with hSol
  set 𝒯 : Set ℝ := {T | 0 < T ∧ ∃ γ, Sol γ T} with h𝒯
  have hΓ : ∀ T ∈ 𝒯, ∃ γ, Sol γ T := fun T hT => hT.2
  choose! Γ hΓ using hΓ
  -- any two solutions agree on the common interval
  have hagree : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, ∀ t, 0 ≤ t → t ≤ T₁ → t ≤ T₂ → Γ T₁ t = Γ T₂ t := by
    intro T₁ hT₁ T₂ hT₂ t ht0 ht1 ht2
    have hm : Icc 0 (min T₁ T₂) ⊆ Icc 0 T₁ := Icc_subset_Icc le_rfl (min_le_left _ _)
    have hm' : Icc 0 (min T₁ T₂) ⊆ Icc 0 T₂ := Icc_subset_Icc le_rfl (min_le_right _ _)
    refine uniq V hV (T := min T₁ T₂) (fun s hs => ((hΓ T₁ hT₁).2 s (hm hs)).mono hm)
      (fun s hs => ((hΓ T₂ hT₂).2 s (hm' hs)).mono hm') ((hΓ T₁ hT₁).1.trans (hΓ T₂ hT₂).1.symm)
      ⟨ht0, le_min ht1 ht2⟩
  -- local existence at `x₀`
  obtain ⟨ε₀, hε₀, hloc⟩ := uniform_local_existence V hV (isCompact_singleton (x := x₀))
  obtain ⟨α₀, hα₀0, hα₀d⟩ := hloc x₀ rfl
  have h𝒯ne : ε₀ / 2 ∈ 𝒯 := by
    refine ⟨by positivity, α₀, hα₀0, fun t ht => (hα₀d t ⟨?_, ?_⟩).hasDerivWithinAt⟩
    · linarith [ht.1]
    · linarith [ht.2]
  -- the domain and the maximal solution
  set D : Set ℝ := {t | 0 ≤ t ∧ ∃ T ∈ 𝒯, t < T} with hD
  set γ : ℝ → X := fun t => if h : ∃ T ∈ 𝒯, t < T then Γ h.choose t else x₀ with hγ
  have hγeq : ∀ T ∈ 𝒯, ∀ t, 0 ≤ t → t < T → γ t = Γ T t := by
    intro T hT t ht0 htT
    have h : ∃ T ∈ 𝒯, t < T := ⟨T, hT, htT⟩
    simp only [hγ, dif_pos h]
    exact hagree _ h.choose_spec.1 _ hT t ht0 h.choose_spec.2.le htT.le
  have hγ0 : γ 0 = x₀ := by
    rw [hγeq _ h𝒯ne 0 le_rfl (by positivity)]; exact (hΓ _ h𝒯ne).1
  -- the derivative
  have hderiv : ∀ t ∈ D, HasDerivWithinAt γ (V (γ t)) (Ici 0) t := by
    rintro t ⟨ht0, T, hT, htT⟩
    have hTpos : 0 < T := hT.1
    have hd : HasDerivWithinAt (Γ T) (V (Γ T t)) (Icc 0 T) t := (hΓ T hT).2 t ⟨ht0, htT.le⟩
    have hnhds : Icc 0 T ∈ 𝓝[Ici 0] t := by
      refine mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds htT)) ?_
      rintro s ⟨hs1, hs2⟩; exact ⟨hs1, hs2.le⟩
    have hd' : HasDerivWithinAt (Γ T) (V (Γ T t)) (Ici 0) t := hd.mono_of_mem_nhdsWithin hnhds
    have heq : γ =ᶠ[𝓝[Ici 0] t] Γ T := by
      filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds htT)] with s hs
      exact hγeq T hT s hs.1 hs.2
    rw [hγeq T hT t ht0 htT]
    exact hd'.congr_of_eventuallyEq heq (hγeq T hT t ht0 htT)
  refine ⟨γ, D, ⟨⟨le_rfl, _, h𝒯ne, by positivity⟩, fun t ht => ht.1, ?_, hderiv, ?_⟩, hγ0⟩
  · -- `D` is an interval
    refine ⟨fun x hx y hy t ht => ⟨hx.1.trans ht.1, ?_⟩⟩
    obtain ⟨T, hT, hyT⟩ := hy.2
    exact ⟨T, hT, ht.2.trans_lt hyT⟩
  · -- maximality
    intro b hb hsub hbdd
    rcases hb.eq_or_lt with hb0 | hbpos
    · subst hb0
      exact ⟨ε₀ / 2, by positivity, fun t ht => ⟨ht.1, ε₀ / 2, h𝒯ne, by simpa using ht.2⟩⟩
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
    obtain ⟨ε, hε, hloc⟩ := uniform_local_existence V hV (isCompact_closedBall (0 : X) R)
    -- restart from `t₁ = max 0 (b - ε/2)`
    set t₁ := max 0 (b - ε / 2) with ht₁
    have ht₁0 : 0 ≤ t₁ := le_max_left _ _
    have ht₁b : t₁ < b := max_lt hbpos (by linarith)
    have ht₁D : t₁ ∈ D := hsub ⟨ht₁0, ht₁b⟩
    obtain ⟨α, hα0, hαd⟩ := hloc (γ t₁) (hR ⟨t₁, ⟨ht₁0, ht₁b⟩, rfl⟩)
    obtain ⟨T, hT, ht₁T⟩ := ht₁D.2
    -- the solution on `[0, t₁]`
    have hsol₁ : ∀ t ∈ Icc 0 t₁, HasDerivWithinAt (Γ T) (V (Γ T t)) (Icc 0 t₁) t := fun t ht =>
      ((hΓ T hT).2 t ⟨ht.1, ht.2.trans ht₁T.le⟩).mono (Icc_subset_Icc le_rfl ht₁T.le)
    -- the restarted solution on `[t₁, t₁ + 3ε/4]`
    set β : ℝ → X := fun s => α (s - t₁) with hβ
    have hsol₂ : ∀ t ∈ Icc t₁ (t₁ + 3 * ε / 4),
        HasDerivWithinAt β (V (β t)) (Icc t₁ (t₁ + 3 * ε / 4)) t := by
      intro t ht
      have h := hαd (t - t₁) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have := h.scomp t ((hasDerivAt_id t).sub_const t₁)
      simpa [hβ, Function.comp_def] using this.hasDerivWithinAt
    have hmatch : Γ T t₁ = β t₁ := by
      simp only [hβ, sub_self, hα0]
      exact (hγeq T hT t₁ ht₁0 ht₁T).symm
    have hglue := glue V (a := 0) (c := t₁) (b := t₁ + 3 * ε / 4) ht₁0 (by linarith) hsol₁ hsol₂
      hmatch
    set T' := t₁ + 3 * ε / 4 with hT'
    have hT'𝒯 : T' ∈ 𝒯 := by
      refine ⟨by linarith, _, ?_, hglue⟩
      simp only [ht₁0, if_true]
      exact (hΓ T hT).1
    refine ⟨ε / 4, by positivity, fun t ht => ⟨ht.1, T', hT'𝒯, ?_⟩⟩
    have : b - ε / 2 ≤ t₁ := le_max_right _ _
    linarith [ht.2]


end S2S
