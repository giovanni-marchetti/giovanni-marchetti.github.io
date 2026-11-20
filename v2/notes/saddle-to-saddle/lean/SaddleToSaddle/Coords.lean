import SaddleToSaddle.Basic

/-!
# Coordinates on `Θ = (ℝ^p)^N`

Basic API for `single`, `zeroOut`, `proj`, `zeroAt`, `insertAt`, `S`, and gradient components.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

@[simp] lemma single_apply_self (n : ι) (w : E) : (single n w : Θ ι E) n = w := by
  simp [single]

lemma single_apply_of_ne {n m : ι} (h : m ≠ n) (w : E) : (single n w : Θ ι E) m = 0 := by
  simp [single, h]

lemma single_apply (n : ι) (w : E) (m : ι) :
    (single n w : Θ ι E) m = if m = n then w else 0 := by
  by_cases h : m = n
  · subst h; simp
  · simp [single_apply_of_ne h, h]

@[simp] lemma single_zero (n : ι) : (single n (0 : E) : Θ ι E) = 0 := by
  ext m; simp [single_apply]

lemma single_add (n : ι) (v w : E) :
    (single n (v + w) : Θ ι E) = single n v + single n w := by
  ext m; by_cases h : m = n <;> simp [single_apply, h]

lemma single_smul (n : ι) (c : ℝ) (w : E) :
    (single n (c • w) : Θ ι E) = c • single n w := by
  ext m; by_cases h : m = n <;> simp [single_apply, h]

lemma single_sub (n : ι) (v w : E) :
    (single n (v - w) : Θ ι E) = single n v - single n w := by
  ext m; by_cases h : m = n <;> simp [single_apply, h]

/-- `single n` as a continuous linear map. -/
def singleL (n : ι) : E →L[ℝ] Θ ι E :=
  LinearMap.toContinuousLinearMap
    { toFun := single n
      map_add' := single_add n
      map_smul' := single_smul n }

@[simp] lemma singleL_apply (n : ι) (w : E) : (singleL n : E →L[ℝ] Θ ι E) w = single n w := rfl

@[simp] lemma zeroOut_apply (B : Finset ι) (θ : Θ ι E) (m : ι) :
    zeroOut B θ m = if m ∈ B then 0 else θ m := rfl

lemma zeroAt_apply (n : ι) (θ : Θ ι E) (m : ι) :
    zeroAt n θ m = if m = n then 0 else θ m := by
  simp

lemma proj_apply (A : Finset ι) (θ : Θ ι E) (m : ι) :
    proj A θ m = if m ∈ A then θ m else 0 := by
  by_cases h : m ∈ A <;> simp [h]

lemma insertAt_apply (θ : Θ ι E) (n : ι) (w : E) (m : ι) :
    insertAt θ n w m = if m = n then w else θ m := by
  by_cases h : m = n
  · subst h; simp [insertAt]
  · simp [insertAt, h, single_apply_of_ne h]

@[simp] lemma insertAt_apply_self (θ : Θ ι E) (n : ι) (w : E) : insertAt θ n w n = w := by
  simp [insertAt_apply]

lemma insertAt_apply_of_ne (θ : Θ ι E) {n m : ι} (h : m ≠ n) (w : E) :
    insertAt θ n w m = θ m := by
  simp [insertAt_apply, h]

@[simp] lemma insertAt_self (θ : Θ ι E) (n : ι) : insertAt θ n (θ n) = θ := by
  ext m; by_cases h : m = n
  · subst h; simp
  · simp [insertAt_apply_of_ne θ h]

@[simp] lemma insertAt_zero (θ : Θ ι E) (n : ι) : insertAt θ n 0 = zeroAt n θ := by
  simp [insertAt]

lemma insertAt_zeroAt (θ : Θ ι E) (n : ι) (w : E) : insertAt (zeroAt n θ) n w = insertAt θ n w := by
  ext m; by_cases h : m = n
  · subst h; simp
  · simp [insertAt_apply_of_ne _ h, h]

lemma zeroAt_insertAt (θ : Θ ι E) (n : ι) (w : E) : zeroAt n (insertAt θ n w) = zeroAt n θ := by
  ext m; by_cases h : m = n
  · subst h; simp
  · simp [insertAt_apply_of_ne _ h, h]

lemma insertAt_add_single (θ : Θ ι E) (n : ι) (v w : E) :
    insertAt θ n (v + w) = insertAt θ n v + single n w := by
  simp [insertAt, single_add, add_assoc]

lemma insertAt_eq_add (θ : Θ ι E) (n : ι) (w : E) (h : θ n = 0) :
    insertAt θ n w = θ + single n w := by
  ext m; by_cases hm : m = n
  · subst hm; simp [h]
  · simp [insertAt_apply_of_ne _ hm, single_apply_of_ne hm]

/-! ### Norms and inner products -/

lemma inner_eq_sum (x y : Θ ι E) : ⟪x, y⟫ = ∑ m, ⟪x m, y m⟫ := PiLp.inner_apply x y

lemma norm_sq_eq_sum (θ : Θ ι E) : ‖θ‖ ^ 2 = ∑ m, ‖θ m‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

lemma norm_apply_le (θ : Θ ι E) (n : ι) : ‖θ n‖ ≤ ‖θ‖ := PiLp.norm_apply_le θ n

@[simp] lemma norm_single (n : ι) (w : E) : ‖(single n w : Θ ι E)‖ = ‖w‖ := by
  exact PiLp.norm_single 2 (fun _ : ι => E) n w

lemma inner_single_right (θ : Θ ι E) (n : ι) (w : E) : ⟪θ, single n w⟫ = ⟪θ n, w⟫ := by
  rw [inner_eq_sum, Finset.sum_eq_single n]
  · simp
  · intro m _ hm; simp [single_apply_of_ne hm]
  · simp

lemma inner_single_left (θ : Θ ι E) (n : ι) (w : E) : ⟪single n w, θ⟫ = ⟪w, θ n⟫ := by
  rw [real_inner_comm, inner_single_right, real_inner_comm]

lemma inner_zeroOut_left (B : Finset ι) (x y : Θ ι E) :
    ⟪zeroOut B x, y⟫ = ⟪x, zeroOut B y⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : m ∈ B <;> simp [h]

lemma norm_sq_zeroOut_add (B : Finset ι) (θ : Θ ι E) :
    ‖zeroOut B θ‖ ^ 2 + ‖θ - zeroOut B θ‖ ^ 2 = ‖θ‖ ^ 2 := by
  rw [norm_sq_eq_sum, norm_sq_eq_sum, norm_sq_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : m ∈ B <;> simp [h]

lemma norm_zeroOut_le (B : Finset ι) (θ : Θ ι E) : ‖zeroOut B θ‖ ≤ ‖θ‖ := by
  have h := norm_sq_zeroOut_add B θ
  have h1 : ‖zeroOut B θ‖ ^ 2 ≤ ‖θ‖ ^ 2 := by nlinarith [sq_nonneg ‖θ - zeroOut B θ‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

lemma norm_sub_zeroOut_le (B : Finset ι) (θ : Θ ι E) : ‖θ - zeroOut B θ‖ ≤ ‖θ‖ := by
  have h := norm_sq_zeroOut_add B θ
  have h1 : ‖θ - zeroOut B θ‖ ^ 2 ≤ ‖θ‖ ^ 2 := by nlinarith [sq_nonneg ‖zeroOut B θ‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

lemma norm_zeroOut_opNorm_le (B : Finset ι) : ‖(zeroOut B : Θ ι E →L[ℝ] Θ ι E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun θ => by
    simpa using norm_zeroOut_le B θ

/-! ### The subspaces `S_A` -/

lemma mem_S_iff (A : Finset ι) (θ : Θ ι E) : θ ∈ S A ↔ ∀ m ∉ A, θ m = 0 := Iff.rfl

lemma proj_mem_S (A : Finset ι) (θ : Θ ι E) : proj A θ ∈ S A := by
  intro m hm; simp [proj_apply, hm]

lemma proj_eq_self_of_mem_S {A : Finset ι} {θ : Θ ι E} (h : θ ∈ S A) : proj A θ = θ := by
  ext m; by_cases hm : m ∈ A
  · simp [proj_apply, hm]
  · simp [proj_apply, hm, h m hm]

lemma proj_proj (A : Finset ι) (θ : Θ ι E) : proj A (proj A θ) = proj A θ :=
  proj_eq_self_of_mem_S (proj_mem_S A θ)

lemma zero_mem_S (A : Finset ι) : (0 : Θ ι E) ∈ S A := fun _ _ => rfl

lemma S_add {A : Finset ι} {x y : Θ ι E} (hx : x ∈ S A) (hy : y ∈ S A) : x + y ∈ S A := by
  intro m hm; simp [hx m hm, hy m hm]

lemma S_sub {A : Finset ι} {x y : Θ ι E} (hx : x ∈ S A) (hy : y ∈ S A) : x - y ∈ S A := by
  intro m hm; simp [hx m hm, hy m hm]

lemma S_smul {A : Finset ι} (c : ℝ) {x : Θ ι E} (hx : x ∈ S A) : c • x ∈ S A := by
  intro m hm; simp [hx m hm]

lemma S_mono {A B : Finset ι} (h : A ⊆ B) {x : Θ ι E} (hx : x ∈ S A) : x ∈ S B :=
  fun m hm => hx m (fun hmA => hm (h hmA))

lemma single_mem_S {A : Finset ι} {n : ι} (hn : n ∈ A) (w : E) : (single n w : Θ ι E) ∈ S A := by
  intro m hm
  have : m ≠ n := fun h => hm (h ▸ hn)
  simp [single_apply_of_ne this]

/-- `S_A` as a submodule. -/
def SA (A : Finset ι) : Submodule ℝ (Θ ι E) where
  carrier := S A
  add_mem' := S_add
  zero_mem' := zero_mem_S A
  smul_mem' := S_smul

lemma mem_SA (A : Finset ι) (θ : Θ ι E) : θ ∈ SA A ↔ θ ∈ S A := Iff.rfl

lemma isClosed_S (A : Finset ι) : IsClosed (S A : Set (Θ ι E)) := by
  have : (S A : Set (Θ ι E)) = ⋂ m ∈ (Aᶜ : Finset ι), {θ | θ m = 0} := by
    ext θ; simp [S]
  rw [this]
  refine isClosed_biInter fun m _ => isClosed_eq ?_ continuous_const
  exact (PiLp.continuous_apply 2 _ m)

lemma inner_proj_eq_of_mem_S {A : Finset ι} {x : Θ ι E} (hx : x ∈ S A) (y : Θ ι E) :
    ⟪x, proj A y⟫ = ⟪x, y⟫ := by
  rw [← inner_zeroOut_left, proj_eq_self_of_mem_S hx]

/-- Decomposition `θ = π_A θ + ι_n(w_n) + z` for `n ∉ A`, with `z = θ - π_{A ∪ {n}} θ`. -/
lemma decomp {A : Finset ι} {n : ι} (hn : n ∉ A) (θ : Θ ι E) :
    θ = proj A θ + single n (θ n) + (θ - proj (insert n A) θ) := by
  ext m
  by_cases hm : m = n
  · subst hm; simp [proj_apply, hn]
  · by_cases hmA : m ∈ A
    · simp [proj_apply, hmA, single_apply_of_ne hm]
    · simp [proj_apply, hmA, hm, single_apply_of_ne hm]

lemma zeroAt_eq_proj_add {A : Finset ι} {n : ι} (hn : n ∉ A) (θ : Θ ι E) :
    zeroAt n θ = proj A θ + (θ - proj (insert n A) θ) := by
  ext m
  by_cases hm : m = n
  · subst hm; simp [proj_apply, hn]
  · by_cases hmA : m ∈ A
    · simp [proj_apply, hmA, hm]
    · simp [proj_apply, hmA, hm]

lemma proj_insert_eq {A : Finset ι} {n : ι} (hn : n ∉ A) (θ : Θ ι E) :
    proj (insert n A) θ = proj A θ + single n (θ n) := by
  ext m
  by_cases hm : m = n
  · subst hm; simp [proj_apply, hn]
  · by_cases hmA : m ∈ A
    · simp [proj_apply, hmA, single_apply_of_ne hm]
    · simp [proj_apply, hmA, hm, single_apply_of_ne hm]

lemma sub_proj_apply_of_mem {A : Finset ι} {m : ι} (hm : m ∈ A) (θ : Θ ι E) :
    (θ - proj A θ) m = 0 := by
  simp [proj_apply, hm]

lemma norm_apply_le_norm_sub_proj {A : Finset ι} {m : ι} (hm : m ∉ A) (θ : Θ ι E) :
    ‖θ m‖ ≤ ‖θ - proj A θ‖ := by
  have := norm_apply_le (θ - proj A θ) m
  simpa [proj_apply, hm] using this

/-! ### Gradient components -/

lemma inner_gradient_single (F : Θ ι E → ℝ) (θ : Θ ι E) (n : ι) (v : E) :
    ⟪(gradient F θ) n, v⟫ = fderiv ℝ F θ (single n v) := by
  rw [← inner_single_right, gradient, InnerProductSpace.toDual_symm_apply]

lemma inner_gradient (F : Θ ι E → ℝ) (θ v : Θ ι E) :
    ⟪gradient F θ, v⟫ = fderiv ℝ F θ v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma inner_gradient_E (f : E → ℝ) (x v : E) : ⟪gradient f x, v⟫ = fderiv ℝ f x v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma norm_gradient_eq (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient]; exact LinearIsometryEquiv.norm_map _ _

lemma norm_gradientΘ_eq (F : Θ ι E → ℝ) (x : Θ ι E) : ‖gradient F x‖ = ‖fderiv ℝ F x‖ := by
  rw [gradient]; exact LinearIsometryEquiv.norm_map _ _

/-! ### `ζ_A` -/

lemma zeta_nonneg (k : ℕ) (A : Finset ι) (θ : Θ ι E) : 0 ≤ zeta k A θ :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

end S2S
