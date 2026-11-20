import SaddleToSaddle.Axioms
import SaddleToSaddle.Calculus

/-!
# Lemma 1 (Flatness) and the structure of the utilities

From `(H)` and Hadamard's lemma (Taylor's formula with smooth remainder) we derive:

* the polar form `-∇_{w_n}F(θ^{\n} + ι_n(ρu)) = ρ^{k-1} G(ρ, u, θ)` with `G` smooth and
  `G(0, u, θ) = ∇U_n(θ; u)` (used in Lemmas 2 and 3);
* Lemma 1(a): `|∇_{w_n}F(θ)| = O(|w_n|^{k-1})`, and `∇_{w_n}F = 0` on `{w_n = 0}`;
* Lemma 1(b): `∇_A F(θ) - ∇_A F(π_A θ) = O(ζ_A(θ))`;
* the expansion `F(θ + ι_n(w)) = F(θ) - U_n(θ; w) + o(|w|^k)` at points with `w_n = 0`;
* `U_n(θ; ·)` is a `k`-form: homogeneity and Euler's identity.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- The gradient-flow vector field is smooth. -/
theorem gf_contDiff (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (gf F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun θ => (InnerProductSpace.toDual ℝ (Θ ι E)).symm (fderiv ℝ F θ)) :=
    (InnerProductSpace.toDual ℝ (Θ ι E)).symm.contDiff.comp h1
  exact h2.neg

/-! ### The utility is a `k`-form -/

/-- The gradient of a smooth function on `E` is smooth. -/
private lemma contDiff_gradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.comp (hf.fderiv_right (by simp))

theorem U_smul (n : ι) (θ : Θ ι E) (c : ℝ) (w : E) : U F k n θ (c • w) = c ^ k * U F k n θ w := by
  have h := (iteratedFDeriv ℝ k (fun v : E => F (insertAt θ n v)) 0).map_smul_univ
    (fun _ => c) (fun _ => w)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [U, h]
  ring

theorem U_zeroAt (n : ι) (θ : Θ ι E) : U F k n (zeroAt n θ) = U F k n θ := by
  funext w
  simp only [U, insertAt_zeroAt]

theorem U_contDiff (n : ι) (θ : Θ ι E) : ContDiff ℝ ∞ (U F k n θ) := by
  have h1 : ContDiff ℝ ∞ (fun w : E => (fun _ : Fin k => w)) := contDiff_pi.2 fun _ => contDiff_id
  have h2 := (iteratedFDeriv ℝ k (fun v : E => F (insertAt θ n v)) 0).contDiff.comp h1
  exact (contDiff_const.mul h2).neg

/-- Derivative of `t ↦ U(t • w)`. -/
private lemma hasDerivAt_U_smul (n : ι) (θ : Θ ι E) (w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U F k n θ (s • w)) (fderiv ℝ (U F k n θ) (t • w) w) t := by
  have hd : DifferentiableAt ℝ (U F k n θ) (t • w) :=
    (U_contDiff n θ).differentiable (by simp) _
  have h := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)
  simpa [Function.comp_def] using h

/-- The derivative of `t ↦ U(t • w) = t ^ k U(w)`. -/
private lemma hasDerivAt_pow_U (n : ι) (θ : Θ ι E) (w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U F k n θ (s • w)) ((k : ℝ) * t ^ (k - 1) * U F k n θ w) t := by
  have h : (fun s : ℝ => U F k n θ (s • w)) = fun s => s ^ k * U F k n θ w := by
    funext s; exact U_smul n θ s w
  rw [h]
  exact (hasDerivAt_pow k t).mul_const _

private lemma fderivU_smul_apply (n : ι) (θ : Θ ι E) (w : E) (t : ℝ) :
    fderiv ℝ (U F k n θ) (t • w) w = (k : ℝ) * t ^ (k - 1) * U F k n θ w :=
  (hasDerivAt_U_smul n θ w t).unique (hasDerivAt_pow_U n θ w t)

theorem gradU_smul (hk : 3 ≤ k) (n : ι) (θ : Θ ι E) (c : ℝ) (w : E) :
    gradient (U F k n θ) (c • w) = c ^ (k - 1) • gradient (U F k n θ) w := by
  set u := U F k n θ with hu_def
  have hu : ContDiff ℝ ∞ u := U_contDiff n θ
  have hdiff : Differentiable ℝ u := hu.differentiable (by simp)
  by_cases hc : c = 0
  · subst hc
    have hk1 : k - 1 ≠ 0 := by omega
    rw [zero_smul, zero_pow hk1, zero_smul]
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_E, inner_zero_left]
    have h := fderivU_smul_apply (F := F) (k := k) n θ v 0
    rw [zero_smul, zero_pow hk1] at h
    simpa using h
  · apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_E, real_inner_smul_left, inner_gradient_E]
    -- differentiate `x ↦ u (c • x) = c ^ k * u x` at `w`
    have h1 : HasFDerivAt (fun x => u (c • x))
        ((fderiv ℝ u (c • w)).comp (c • ContinuousLinearMap.id ℝ E)) w :=
      (hdiff (c • w)).hasFDerivAt.comp w ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul c)
    have h2 : HasFDerivAt (fun x => u (c • x)) (c ^ k • fderiv ℝ u w) w := by
      have : (fun x => u (c • x)) = fun x => c ^ k * u x := by
        funext x; exact U_smul n θ c x
      rw [this]
      exact (hdiff w).hasFDerivAt.const_mul _
    have h3 := congrArg (fun L : E →L[ℝ] ℝ => L (c⁻¹ • v)) (h1.unique h2)
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at h3
    have h4 : fderiv ℝ u (c • w) v = c⁻¹ * (c ^ k * fderiv ℝ u w v) := by
      rw [← h3]; field_simp
    rw [h4]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- Euler's identity `⟨w, ∇U(w)⟩ = k U(w)`. -/
theorem euler (n : ι) (θ : Θ ι E) (w : E) : ⟪w, gradient (U F k n θ) w⟫ = k * U F k n θ w := by
  rw [real_inner_comm, inner_gradient_E]
  have h := fderivU_smul_apply (F := F) (k := k) n θ w 1
  simpa using h

/-- Euler's identity for `∇U`: `∇²U(w) w = (k - 1) ∇U(w)`. -/
theorem hessU_self (hk : 3 ≤ k) (n : ι) (θ : Θ ι E) (w : E) :
    fderiv ℝ (gradient (U F k n θ)) w w = ((k : ℝ) - 1) • gradient (U F k n θ) w := by
  have hg : ContDiff ℝ ∞ (gradient (U F k n θ)) := contDiff_gradient (U_contDiff n θ)
  have hd : DifferentiableAt ℝ (gradient (U F k n θ)) ((1 : ℝ) • w) :=
    hg.differentiable (by simp) _
  have h1 : HasDerivAt (fun s : ℝ => gradient (U F k n θ) (s • w))
      (fderiv ℝ (gradient (U F k n θ)) w w) 1 := by
    have h := hd.hasFDerivAt.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const w)
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun s : ℝ => gradient (U F k n θ) (s • w))
      ((((k - 1 : ℕ) : ℝ) * (1 : ℝ) ^ (k - 1 - 1)) • gradient (U F k n θ) w) 1 := by
    have : (fun s : ℝ => gradient (U F k n θ) (s • w)) =
        fun s => s ^ (k - 1) • gradient (U F k n θ) w := by
      funext s; exact gradU_smul hk n θ s w
    rw [this]
    exact (hasDerivAt_pow (k - 1) (1 : ℝ)).smul_const _
  rw [h1.unique h2, one_pow, mul_one, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]

private lemma inner_fderiv_gradU_aux (n : ι) (θ : Θ ι E) (w v v' : E) :
    ⟪fderiv ℝ (gradient (U F k n θ)) w v, v'⟫ = fderiv ℝ (fderiv ℝ (U F k n θ)) w v v' := by
  have hgrad : gradient (U F k n θ) = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ (U F k n θ) :=
    rfl
  rw [hgrad, LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- The Hessian of `U` is symmetric. -/
theorem hessU_symm (n : ι) (θ : Θ ι E) (w v v' : E) :
    ⟪fderiv ℝ (gradient (U F k n θ)) w v, v'⟫ = ⟪v, fderiv ℝ (gradient (U F k n θ)) w v'⟫ := by
  rw [inner_fderiv_gradU_aux, real_inner_comm, inner_fderiv_gradU_aux]
  exact ((U_contDiff n θ).contDiffAt.isSymmSndFDerivAt (by simp)) v v'

/-- The Hessian of `U` as the derivative of its gradient. -/
theorem inner_fderiv_gradU (n : ι) (θ : Θ ι E) (w v v' : E) :
    ⟪fderiv ℝ (gradient (U F k n θ)) w v, v'⟫ = fderiv ℝ (fderiv ℝ (U F k n θ)) w v v' :=
  inner_fderiv_gradU_aux n θ w v v'

/-! ### Polar form and Lemma 1 -/

private lemma contDiff_singleL (n : ι) : ContDiff ℝ ∞ (fun w : E => (singleL n : E →L[ℝ] Θ ι E) w) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E) (F := Θ ι E) (singleL n)

private lemma contDiff_zeroAt (n : ι) : ContDiff ℝ ∞ (fun θ : Θ ι E => zeroAt n θ) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Θ ι E) (F := Θ ι E) (zeroAt n)

private lemma zeroAt_zeroAt (n : ι) (θ : Θ ι E) : zeroAt n (zeroAt n θ) = zeroAt n θ := by
  have h := zeroAt_insertAt θ n 0
  rwa [insertAt_zero] at h

private lemma hasFDerivAt_insertAt (θ : Θ ι E) (n : ι) (w : E) :
    HasFDerivAt (fun w' : E => insertAt θ n w') (singleL n : E →L[ℝ] Θ ι E) w := by
  have : (fun w' : E => insertAt θ n w') = fun w' => zeroAt n θ + singleL n w' := by
    funext w'; rfl
  rw [this]
  exact (singleL n).hasFDerivAt.const_add _

private lemma contDiff_F_insertAt (hF : ContDiff ℝ ∞ F) (θ : Θ ι E) (n : ι) :
    ContDiff ℝ ∞ (fun w : E => F (insertAt θ n w)) := by
  have : (fun w : E => F (insertAt θ n w)) = fun w => F (zeroAt n θ + singleL n w) := by
    funext w; rfl
  rw [this]
  exact hF.comp (contDiff_const.add (contDiff_singleL n))

/-- `∇_{w_n} F = 0` on `{w_n = 0}` (proved before the polar form, which uses it). -/
private lemma grad_apply_eq_zero_aux (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
    {θ : Θ ι E} {n : ι} (h : θ n = 0) : (gradient F θ) n = 0 := by
  have h1 := hH n θ 1 le_rfl (by omega)
  have hθ : insertAt θ n 0 = θ := by
    conv_rhs => rw [← insertAt_self θ n]
    rw [h]
  have hd : HasFDerivAt (fun w : E => F (insertAt θ n w)) ((fderiv ℝ F θ).comp (singleL n)) 0 := by
    have := ((hF.differentiable (by simp)) (insertAt θ n 0)).hasFDerivAt.comp (0 : E)
      (hasFDerivAt_insertAt θ n 0)
    rwa [hθ] at this
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_single, inner_zero_left]
  have h2 := congrArg (fun M => M (fun _ => v)) h1
  simp only [iteratedFDeriv_one_apply] at h2
  rw [hd.fderiv] at h2
  simpa using h2

/-- The `ρ`-derivatives of `ρ ↦ F(θ^{\n} + ι_n(ρu)) - F(θ^{\n})` at `0` of order `≥ 1`. -/
private lemma iteratedDeriv_line (hF : ContDiff ℝ ∞ F) (n : ι) (θ : Θ ι E) (u : E) {j : ℕ}
    (hj : 1 ≤ j) :
    iteratedDeriv j (fun ρ : ℝ => F (insertAt θ n (ρ • u)) - F (zeroAt n θ)) 0 =
      iteratedFDeriv ℝ j (fun w : E => F (insertAt θ n w)) 0 (fun _ => u) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hderiv : deriv (fun ρ : ℝ => F (insertAt θ n (ρ • u)) - F (zeroAt n θ)) =
      deriv (fun ρ : ℝ => F (insertAt θ n (ρ • u))) := by
    funext x; exact deriv_sub_const _
  rw [iteratedDeriv_succ', hderiv, ← iteratedDeriv_succ']
  have h := iteratedDeriv_comp_line (contDiff_F_insertAt hF θ n) 0 u (i + 1)
  simpa only [zero_add] using h

/-- The Hadamard construction: `F(θ^{\n} + ι_n(ρu)) = F(θ^{\n}) + ρ^k Ψ(ρ, u, θ)` with `Ψ`
smooth, `Ψ(0, u, θ) = -U_n(θ; u)`, and `Ψ` depending on `θ` only through `θ^{\n}`. -/
private lemma exists_Psi (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k) (n : ι) :
    ∃ Ψ : ℝ × E × Θ ι E → ℝ, ContDiff ℝ ∞ Ψ ∧
      (∀ ρ u θ, F (insertAt θ n (ρ • u)) = F (zeroAt n θ) + ρ ^ k * Ψ (ρ, u, θ)) ∧
      (∀ u θ, Ψ (0, u, θ) = -U F k n θ u) ∧
      (∀ ρ u θ, Ψ (ρ, u, zeroAt n θ) = Ψ (ρ, u, θ)) := by
  let φ : ℝ × (E × Θ ι E) → ℝ := fun q => F (insertAt q.2.2 n (q.1 • q.2.1)) - F (zeroAt n q.2.2)
  have hins : ContDiff ℝ ∞ (fun q : ℝ × (E × Θ ι E) => insertAt q.2.2 n (q.1 • q.2.1)) := by
    have : (fun q : ℝ × (E × Θ ι E) => insertAt q.2.2 n (q.1 • q.2.1)) =
        fun q => zeroAt n q.2.2 + singleL n (q.1 • q.2.1) := by funext q; rfl
    rw [this]
    exact ((contDiff_zeroAt n).comp (contDiff_snd.comp contDiff_snd)).add
      ((contDiff_singleL n).comp (contDiff_fst.smul (contDiff_fst.comp contDiff_snd)))
  have hφ : ContDiff ℝ ∞ φ :=
    (hF.comp hins).sub (hF.comp ((contDiff_zeroAt n).comp (contDiff_snd.comp contDiff_snd)))
  have h0 : ∀ p : E × Θ ι E, ∀ j < k, iteratedDeriv j (fun ρ => φ (ρ, p)) 0 = 0 := by
    rintro ⟨u, θ⟩ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp [φ]
    · change iteratedDeriv j (fun ρ : ℝ => F (insertAt θ n (ρ • u)) - F (zeroAt n θ)) 0 = 0
      rw [iteratedDeriv_line hF n θ u hj1, hH n θ j hj1 hj]
      rfl
  obtain ⟨Ψ₀, hΨ₀, hφΨ, hΨ0⟩ := hadamard φ hφ k h0
  refine ⟨fun q => Ψ₀ (q.1, (q.2.1, zeroAt n q.2.2)), ?_, ?_, ?_, ?_⟩
  · exact hΨ₀.comp (contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
      ((contDiff_zeroAt n).comp (contDiff_snd.comp contDiff_snd))))
  · intro ρ u θ
    have h := hφΨ ρ (u, zeroAt n θ)
    simp only [φ, insertAt_zeroAt, zeroAt_zeroAt, smul_eq_mul] at h
    simp only
    linarith
  · intro u θ
    simp only
    rw [hΨ0]
    change (k.factorial : ℝ)⁻¹ • iteratedDeriv k (fun ρ : ℝ =>
      F (insertAt (zeroAt n θ) n (ρ • u)) - F (zeroAt n (zeroAt n θ))) 0 = _
    rw [iteratedDeriv_line hF n (zeroAt n θ) u (by omega), ← U_zeroAt (F := F) (k := k) n θ]
    simp only [U, smul_eq_mul, neg_neg]
  · intro ρ u θ
    simp only [zeroAt_zeroAt]

/-- Writing `w = ‖w‖ • (‖w‖⁻¹ • w)` with `‖‖w‖⁻¹ • w‖ ≤ 1`. -/
private lemma polar_decomp (w : E) : ‖w‖ • (‖w‖⁻¹ • w) = w ∧ ‖‖w‖⁻¹ • w‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp [hw]
  · have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    refine ⟨smul_inv_smul₀ hw' w, ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw']

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

/-- Polar form of the gradient in `w_n` (proof of Lemma 3, "Polar coordinates"):
`-∇_{w_n}F(θ^{\n} + ι_n(ρu)) = ρ^{k-1} G(ρ, u, θ)`, with `G` smooth, `G(0, u, θ) = ∇U_n(θ; u)`,
and `G` depending on `θ` only through `θ^{\n}`. -/
theorem exists_polar (n : ι) :
    ∃ G : ℝ × E × Θ ι E → E, ContDiff ℝ ∞ G ∧
      (∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ)) ∧
      (∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) ∧
      (∀ ρ u θ, G (ρ, u, θ) = G (ρ, u, zeroAt n θ)) := by
  obtain ⟨Ψ, hΨ, hFΨ, hΨ0, hΨz⟩ := exists_Psi hF hk hH n
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  -- the partial derivative of `Ψ` in the `u`-slot
  let L : E →L[ℝ] ℝ × E × Θ ι E := (0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod 0)
  let D : ℝ × E × Θ ι E → (E →L[ℝ] ℝ) := fun q => (fderiv ℝ Ψ q).comp L
  have hD : ContDiff ℝ ∞ D := (hΨ.fderiv_right (by simp)).clm_comp contDiff_const
  have hpartial : ∀ ρ u θ, HasFDerivAt (fun u' => Ψ (ρ, u', θ)) (D (ρ, u, θ)) u := by
    intro ρ u θ
    have hin : HasFDerivAt (fun u' : E => ((ρ, u', θ) : ℝ × E × Θ ι E)) L u :=
      (hasFDerivAt_const ρ u).prodMk ((hasFDerivAt_id (𝕜 := ℝ) u).prodMk (hasFDerivAt_const θ u))
    exact (hΨd (ρ, u, θ)).hasFDerivAt.comp u hin
  refine ⟨fun q => -(InnerProductSpace.toDual ℝ E).symm (D q), ?_, ?_, ?_, ?_⟩
  · exact ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp hD).neg
  · intro ρ u θ
    by_cases hρ : ρ = 0
    · subst hρ
      have hz : (zeroAt n θ) n = 0 := by simp
      rw [zero_smul, insertAt_zero, grad_apply_eq_zero_aux hF hk hH hz,
        zero_pow (by omega : k - 1 ≠ 0), zero_smul, neg_zero]
    · -- differentiate `u ↦ F(θ^{\n} + ι_n(ρu)) = F(θ^{\n}) + ρ^k Ψ(ρ, u, θ)`
      have hkey : ∀ v, ρ * fderiv ℝ F (insertAt θ n (ρ • u)) (single n v) =
          ρ ^ k * D (ρ, u, θ) v := by
        have h1 : HasFDerivAt (fun u' : E => F (insertAt θ n (ρ • u')))
            ((fderiv ℝ F (insertAt θ n (ρ • u))).comp
              ((singleL n).comp (ρ • ContinuousLinearMap.id ℝ E))) u := by
          have hin : HasFDerivAt (fun u' : E => insertAt θ n (ρ • u'))
              ((singleL n).comp (ρ • ContinuousLinearMap.id ℝ E)) u :=
            (hasFDerivAt_insertAt θ n (ρ • u)).comp u
              ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul ρ)
          exact (hFd _).hasFDerivAt.comp u hin
        have h2 : HasFDerivAt (fun u' : E => F (insertAt θ n (ρ • u')))
            (ρ ^ k • D (ρ, u, θ)) u := by
          have : (fun u' : E => F (insertAt θ n (ρ • u'))) =
              fun u' => F (zeroAt n θ) + ρ ^ k * Ψ (ρ, u', θ) := by
            funext u'; exact hFΨ ρ u' θ
          rw [this]
          exact ((hpartial ρ u θ).const_mul (ρ ^ k)).const_add _
        intro v
        have := congrArg (fun M : E →L[ℝ] ℝ => M v) (h1.unique h2)
        simpa [single_smul] using this
      apply ext_inner_right ℝ
      intro v
      simp only
      rw [inner_neg_left, inner_gradient_single, real_inner_smul_left, inner_neg_left,
        InnerProductSpace.toDual_symm_apply]
      have hpow : ρ ^ k = ρ * ρ ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h := hkey v
      rw [hpow, mul_assoc] at h
      rw [mul_left_cancel₀ hρ h]
      ring
  · intro u θ
    have h1 := hpartial 0 u θ
    have h2 : HasFDerivAt (fun u' => Ψ (0, u', θ)) (-fderiv ℝ (U F k n θ) u) u := by
      have : (fun u' => Ψ (0, u', θ)) = fun u' => -U F k n θ u' := by
        funext u'; exact hΨ0 u' θ
      rw [this]
      exact ((U_contDiff n θ).differentiable (by simp) u).hasFDerivAt.neg
    simp only
    rw [h1.unique h2, map_neg, neg_neg]
    rfl
  · intro ρ u θ
    have h1 := hpartial ρ u θ
    have h2 := hpartial ρ u (zeroAt n θ)
    have : (fun u' => Ψ (ρ, u', zeroAt n θ)) = fun u' => Ψ (ρ, u', θ) := by
      funext u'; exact hΨz ρ u' θ
    rw [this] at h2
    simp only
    rw [h1.unique h2]

/-- `∇U_n(θ; w)` is jointly smooth in `(w, θ)`. -/
theorem gradU_contDiff (n : ι) :
    ContDiff ℝ ∞ (fun p : E × Θ ι E => gradient (U F k n p.2) p.1) := by
  obtain ⟨G, hG, -, hG0, -⟩ := exists_polar hF hk hH n
  have : (fun p : E × Θ ι E => gradient (U F k n p.2) p.1) = fun p => G (0, p.1, p.2) := by
    funext p; exact (hG0 p.1 p.2).symm
  rw [this]
  exact hG.comp (contDiff_const.prodMk contDiff_id)

/-- `∇_{w_n} F = 0` on `{w_n = 0}`. -/
theorem grad_apply_eq_zero {θ : Θ ι E} {n : ι} (h : θ n = 0) : (gradient F θ) n = 0 :=
  grad_apply_eq_zero_aux hF hk hH h

/-- Lemma 1(a): `|∇_{w_n} F(θ)| ≤ C |w_n|^{k-1}` on bounded sets. -/
theorem grad_apply_le (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (n : ι) (θ : Θ ι E), ‖θ‖ ≤ R → ‖(gradient F θ) n‖ ≤ C * ‖θ n‖ ^ (k - 1) := by
  have hb : ∀ n : ι, ∃ C, 0 ≤ C ∧ ∀ θ : Θ ι E, ‖θ‖ ≤ R →
      ‖(gradient F θ) n‖ ≤ C * ‖θ n‖ ^ (k - 1) := by
    intro n
    obtain ⟨G, hG, hpol, -, -⟩ := exists_polar hF hk hH n
    have hK : IsCompact (Icc (0 : ℝ) R ×ˢ (closedBall (0 : E) 1 ×ˢ closedBall (0 : Θ ι E) R)) :=
      isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
    obtain ⟨h1, h2⟩ := polar_decomp (θ n)
    have hmem : ((‖θ n‖, ‖θ n‖⁻¹ • θ n, θ) : ℝ × E × Θ ι E) ∈
        Icc (0 : ℝ) R ×ˢ (closedBall (0 : E) 1 ×ˢ closedBall (0 : Θ ι E) R) :=
      ⟨⟨norm_nonneg _, (norm_apply_le θ n).trans hθ⟩, mem_closedBall_zero_iff.mpr h2,
        mem_closedBall_zero_iff.mpr hθ⟩
    have h := hpol ‖θ n‖ (‖θ n‖⁻¹ • θ n) θ
    rw [h1, insertAt_self] at h
    calc ‖(gradient F θ) n‖ = ‖-(gradient F θ) n‖ := (norm_neg _).symm
      _ = ‖θ n‖ ^ (k - 1) * ‖G (‖θ n‖, ‖θ n‖⁻¹ • θ n, θ)‖ := by
        rw [h, norm_smul, norm_pow, norm_norm]
      _ ≤ ‖θ n‖ ^ (k - 1) * max C 0 := by
        gcongr
        exact (hC _ hmem).trans (le_max_left _ _)
      _ = max C 0 * ‖θ n‖ ^ (k - 1) := mul_comm _ _
  choose C hC0 hC using hb
  refine ⟨∑ m, C m, Finset.sum_nonneg fun m _ => hC0 m, fun n θ hθ => ?_⟩
  calc ‖(gradient F θ) n‖ ≤ C n * ‖θ n‖ ^ (k - 1) := hC n θ hθ
    _ ≤ (∑ m, C m) * ‖θ n‖ ^ (k - 1) := by
      gcongr
      exact Finset.single_le_sum (fun m _ => hC0 m) (Finset.mem_univ n)

/-- Lemma 1(b) for one neuron: `|∇_A F(θ) - ∇_A F(θ^{\n})| ≤ C |w_n|^k` for `n ∉ A`. -/
theorem proj_grad_sub_zeroAt_le (A : Finset ι) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ n ∉ A, ∀ θ : Θ ι E, ‖θ‖ ≤ R →
      ‖proj A (gradient F θ) - proj A (gradient F (zeroAt n θ))‖ ≤ C * ‖θ n‖ ^ k := by
  have hb : ∀ n : ι, ∃ C, 0 ≤ C ∧ (n ∉ A → ∀ θ : Θ ι E, ‖θ‖ ≤ R →
      ‖proj A (gradient F θ) - proj A (gradient F (zeroAt n θ))‖ ≤ C * ‖θ n‖ ^ k) := by
    intro n
    obtain ⟨Ψ, hΨ, hFΨ, -, -⟩ := exists_Psi hF hk hH n
    have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    have hFd : Differentiable ℝ F := hF.differentiable (by simp)
    have hK : IsCompact (Icc (0 : ℝ) R ×ˢ (closedBall (0 : E) 1 ×ˢ closedBall (0 : Θ ι E) R)) :=
      isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    obtain ⟨M, hM⟩ :=
      hK.exists_bound_of_continuousOn (hΨ.continuous_fderiv (by simp)).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun hn θ hθ => ?_⟩
    obtain ⟨h1, h2⟩ := polar_decomp (θ n)
    set ρ := ‖θ n‖ with hρ
    set u := ρ⁻¹ • θ n with hu
    have hmem : ((ρ, u, θ) : ℝ × E × Θ ι E) ∈
        Icc (0 : ℝ) R ×ˢ (closedBall (0 : E) 1 ×ˢ closedBall (0 : Θ ι E) R) :=
      ⟨⟨norm_nonneg _, (norm_apply_le θ n).trans hθ⟩, mem_closedBall_zero_iff.mpr h2,
        mem_closedBall_zero_iff.mpr hθ⟩
    -- the inclusion of the `θ`-slot
    let Lθ : Θ ι E →L[ℝ] ℝ × E × Θ ι E :=
      (0 : Θ ι E →L[ℝ] ℝ).prod ((0 : Θ ι E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ (Θ ι E)))
    have hLθ : ∀ y, ‖Lθ y‖ = ‖y‖ := by
      intro y
      simp [Lθ, Prod.norm_def]
    -- differentiate `θ' ↦ F(insertAt θ' n (ρu)) = F(θ'^{\n}) + ρ^k Ψ(ρ, u, θ')` at `θ`
    have hkey : ∀ y : Θ ι E, y ∈ S A →
        fderiv ℝ F θ y = fderiv ℝ F (zeroAt n θ) y + ρ ^ k * fderiv ℝ Ψ (ρ, u, θ) (Lθ y) := by
      intro y hy
      have hyn : zeroAt n y = y := by
        ext m
        by_cases hm : m = n
        · subst hm; simp [hy m hn]
        · simp [hm]
      have hins : HasFDerivAt (fun θ' : Θ ι E => insertAt θ' n (ρ • u)) (zeroAt n) θ := by
        have : (fun θ' : Θ ι E => insertAt θ' n (ρ • u)) =
            fun θ' => zeroAt n θ' + single n (ρ • u) := by
          funext θ'; rfl
        rw [this]
        exact (zeroAt n).hasFDerivAt.add_const _
      have hF1 : HasFDerivAt (fun θ' => F (insertAt θ' n (ρ • u)))
          ((fderiv ℝ F (insertAt θ n (ρ • u))).comp (zeroAt n)) θ :=
        (hFd _).hasFDerivAt.comp θ hins
      have hin : HasFDerivAt (fun θ' : Θ ι E => ((ρ, u, θ') : ℝ × E × Θ ι E)) Lθ θ :=
        (hasFDerivAt_const ρ θ).prodMk
          ((hasFDerivAt_const u θ).prodMk (hasFDerivAt_id (𝕜 := ℝ) θ))
      have hF2 : HasFDerivAt (fun θ' => F (zeroAt n θ') + ρ ^ k * Ψ (ρ, u, θ'))
          ((fderiv ℝ F (zeroAt n θ)).comp (zeroAt n) +
            ρ ^ k • (fderiv ℝ Ψ (ρ, u, θ)).comp Lθ) θ :=
        ((hFd _).hasFDerivAt.comp θ (zeroAt n).hasFDerivAt).add
          (((hΨd _).hasFDerivAt.comp θ hin).const_mul (ρ ^ k))
      have heq : (fun θ' => F (insertAt θ' n (ρ • u))) =
          fun θ' => F (zeroAt n θ') + ρ ^ k * Ψ (ρ, u, θ') := by
        funext θ'; exact hFΨ ρ u θ'
      rw [heq] at hF1
      have := congrArg (fun M : Θ ι E →L[ℝ] ℝ => M y) (hF1.unique hF2)
      simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul, hyn] at this
      rwa [h1, insertAt_self] at this
    -- the bound, tested against `v`
    have hinner : ∀ v : Θ ι E,
        ⟪proj A (gradient F θ) - proj A (gradient F (zeroAt n θ)), v⟫ =
          ρ ^ k * fderiv ℝ Ψ (ρ, u, θ) (Lθ (proj A v)) := by
      intro v
      rw [inner_sub_left, inner_zeroOut_left, inner_zeroOut_left, inner_gradient, inner_gradient,
        hkey _ (proj_mem_S A v)]
      ring
    set d := proj A (gradient F θ) - proj A (gradient F (zeroAt n θ)) with hd
    have hX : fderiv ℝ Ψ (ρ, u, θ) (Lθ (proj A d)) ≤ max M 0 * ‖d‖ := by
      calc fderiv ℝ Ψ (ρ, u, θ) (Lθ (proj A d))
          ≤ ‖fderiv ℝ Ψ (ρ, u, θ) (Lθ (proj A d))‖ := Real.le_norm_self _
        _ ≤ ‖fderiv ℝ Ψ (ρ, u, θ)‖ * ‖Lθ (proj A d)‖ := (fderiv ℝ Ψ (ρ, u, θ)).le_opNorm _
        _ ≤ max M 0 * ‖d‖ := by
          rw [hLθ]
          exact mul_le_mul ((hM _ hmem).trans (le_max_left _ _)) (norm_zeroOut_le _ _)
            (norm_nonneg _) (le_max_right _ _)
    have hsq : ‖d‖ * ‖d‖ ≤ (max M 0 * ρ ^ k) * ‖d‖ := by
      have h := hinner d
      rw [real_inner_self_eq_norm_mul_norm] at h
      rw [h]
      have hρk : 0 ≤ ρ ^ k := by positivity
      calc ρ ^ k * fderiv ℝ Ψ (ρ, u, θ) (Lθ (proj A d)) ≤ ρ ^ k * (max M 0 * ‖d‖) :=
            mul_le_mul_of_nonneg_left hX hρk
        _ = (max M 0 * ρ ^ k) * ‖d‖ := by ring
    by_cases hd0 : ‖d‖ = 0
    · rw [hd0]; positivity
    · exact le_of_mul_le_mul_right hsq (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0))
  choose C hC0 hC using hb
  refine ⟨∑ m, C m, Finset.sum_nonneg fun m _ => hC0 m, fun n hn θ hθ => ?_⟩
  calc _ ≤ C n * ‖θ n‖ ^ k := hC n hn θ hθ
    _ ≤ (∑ m, C m) * ‖θ n‖ ^ k := by
      gcongr
      exact Finset.single_le_sum (fun m _ => hC0 m) (Finset.mem_univ n)

/-- Lemma 1(b): `|∇_A F(θ) - ∇_A F(π_A θ)| ≤ C ζ_A(θ)` on bounded sets. -/
theorem proj_grad_sub_proj_le (A : Finset ι) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ θ : Θ ι E, ‖θ‖ ≤ R →
      ‖proj A (gradient F θ) - proj A (gradient F (proj A θ))‖ ≤ C * zeta k A θ := by
  obtain ⟨C, hC0, hC⟩ := proj_grad_sub_zeroAt_le hF hk hH A R
  refine ⟨C, hC0, fun θ hθ => ?_⟩
  -- set the inactive weights to zero one at a time
  have key : ∀ B : Finset ι, B ⊆ Aᶜ →
      ‖proj A (gradient F θ) - proj A (gradient F (zeroOut B θ))‖ ≤ C * ∑ m ∈ B, ‖θ m‖ ^ k := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro _
      have h0 : zeroOut (∅ : Finset ι) θ = θ := by ext m; simp
      simp [h0]
    | insert m B hmB ih =>
      intro hsub
      have hmA : m ∉ A := Finset.mem_compl.mp (hsub (Finset.mem_insert_self m B))
      have hB : B ⊆ Aᶜ := (Finset.subset_insert m B).trans hsub
      have hz : zeroOut (insert m B) θ = zeroAt m (zeroOut B θ) := by
        ext i
        by_cases him : i = m
        · subst him; simp
        · simp [him]
      have h1 := ih hB
      have h2 := hC m hmA (zeroOut B θ) ((norm_zeroOut_le B θ).trans hθ)
      have h3 : (zeroOut B θ) m = θ m := by simp [hmB]
      rw [h3] at h2
      rw [hz, Finset.sum_insert hmB]
      calc ‖proj A (gradient F θ) - proj A (gradient F (zeroAt m (zeroOut B θ)))‖
          ≤ ‖proj A (gradient F θ) - proj A (gradient F (zeroOut B θ))‖ +
            ‖proj A (gradient F (zeroOut B θ)) -
              proj A (gradient F (zeroAt m (zeroOut B θ)))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * ∑ i ∈ B, ‖θ i‖ ^ k + C * ‖θ m‖ ^ k := add_le_add h1 h2
        _ = C * (‖θ m‖ ^ k + ∑ i ∈ B, ‖θ i‖ ^ k) := by ring
  exact key Aᶜ subset_rfl

/-- Taylor expansion along `w_n` (the "Consequences" paragraph):
`F(θ^{\n} + ι_n(ρu)) = F(θ^{\n}) + ρ^k Ψ(ρ, u, θ)` with `Ψ` continuous and
`Ψ(0, u, θ) = -U_n(θ; u)`. -/
theorem F_insertAt_expansion (n : ι) :
    ∃ Ψ : ℝ × E × Θ ι E → ℝ, Continuous Ψ ∧
      (∀ ρ u θ, F (insertAt θ n (ρ • u)) = F (zeroAt n θ) + ρ ^ k * Ψ (ρ, u, θ)) ∧
      ∀ u θ, Ψ (0, u, θ) = -U F k n θ u := by
  obtain ⟨Ψ, hΨ, hFΨ, hΨ0, -⟩ := exists_Psi hF hk hH n
  exact ⟨Ψ, hΨ.continuous, hFΨ, hΨ0⟩

end S2S
