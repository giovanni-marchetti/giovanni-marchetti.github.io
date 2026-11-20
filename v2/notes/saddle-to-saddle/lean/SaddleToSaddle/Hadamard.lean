import Mathlib

/-!
# Hadamard's lemma with parameters

Taylor's formula in `ρ` with integral remainder, with a remainder that is smooth in all
variables: if `φ(ρ, p)` is smooth and its `ρ`-derivatives of order `< m` vanish at `ρ = 0`, then
`φ(ρ, p) = ρ^m Ψ(ρ, p)` with `Ψ(ρ, p) = (1/(m-1)!) ∫₀¹ (1-t)^{m-1} ∂_ρ^m φ(tρ, p) dt` smooth and
`Ψ(0, p) = ∂_ρ^m φ(0, p) / m!`. Proved from Mathlib's Taylor formula with integral remainder
(`map_add_eq_sum_add_integral_iteratedFDeriv`) and the smoothness of parametric integrals
(`ContDiff.parametric_integral`).
-/

open scoped ContDiff Topology
open Set Filter

noncomputable section

namespace S2S

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Iterated derivatives in the first variable are iterated Fréchet derivatives in the
direction `(1, 0)`. -/
private lemma iteratedDeriv_fst (φ : ℝ × P → V) (hφ : ContDiff ℝ ∞ φ) (p : P) (j : ℕ) :
    iteratedDeriv j (fun ρ => φ (ρ, p)) =
      fun ρ => iteratedFDeriv ℝ j φ (ρ, p) (fun _ => ((1 : ℝ), (0 : P))) := by
  induction j with
  | zero => ext ρ; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    ext ρ
    have hline : ∀ s : ℝ, ((s, p) : ℝ × P) = ((0 : ℝ), p) + s • ((1 : ℝ), (0 : P)) := by
      intro s; ext <;> simp
    have h := ContDiffAt.deriv_fderiv_add_smul (𝕜 := ℝ) (f := φ) (x := ((0 : ℝ), p))
      (y := ((1 : ℝ), (0 : P))) (t := ρ) (n := j)
      (hφ.contDiffAt.of_le (by exact_mod_cast le_top))
    simp only [← hline] at h
    exact h

private lemma contDiff_iteratedDeriv_fst (φ : ℝ × P → V) (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × P => iteratedDeriv j (fun ρ => φ (ρ, q.2)) q.1) := by
  have : (fun q : ℝ × P => iteratedDeriv j (fun ρ => φ (ρ, q.2)) q.1) =
      fun q => iteratedFDeriv ℝ j φ q (fun _ => ((1 : ℝ), (0 : P))) := by
    ext q
    rw [iteratedDeriv_fst φ hφ q.2 j]
  rw [this]
  have h1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ j φ) :=
    hφ.iteratedFDeriv_right (by exact_mod_cast le_top)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ × P) V
    (fun _ => ((1 : ℝ), (0 : P)))).contDiff.comp h1

/-- **Hadamard's lemma with parameters.** -/
theorem hadamard (φ : ℝ × P → V) (hφ : ContDiff ℝ ∞ φ) (m : ℕ)
    (h0 : ∀ p, ∀ j < m, iteratedDeriv j (fun ρ => φ (ρ, p)) 0 = 0) :
    ∃ Ψ : ℝ × P → V, ContDiff ℝ ∞ Ψ ∧ (∀ ρ p, φ (ρ, p) = ρ ^ m • Ψ (ρ, p)) ∧
      ∀ p, Ψ (0, p) = (m.factorial : ℝ)⁻¹ • iteratedDeriv m (fun ρ => φ (ρ, p)) 0 := by
  rcases m with _ | n
  · refine ⟨φ, hφ, fun ρ p => by simp, fun p => by simp⟩
  -- the `(n+1)`-th partial derivative in `ρ`
  set Dφ : ℝ × P → V := fun q => iteratedDeriv (n + 1) (fun ρ => φ (ρ, q.2)) q.1 with hDφ
  have hD : ContDiff ℝ ∞ Dφ := contDiff_iteratedDeriv_fst φ hφ (n + 1)
  refine ⟨fun q => (n.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t) ^ n • Dφ (t * q.1, q.2),
    ?_, ?_, ?_⟩
  · -- smoothness of the parametric integral
    refine ContDiff.const_smul _ ?_
    have hint : ContDiff ℝ ∞ (Function.uncurry fun (q : ℝ × P) (t : ℝ) =>
        (1 - t) ^ n • Dφ (t * q.1, q.2)) := by
      apply ContDiff.smul
      · exact (contDiff_const.sub contDiff_snd).pow n
      · exact hD.comp ((contDiff_snd.mul (contDiff_fst.comp contDiff_fst)).prodMk
          (contDiff_snd.comp contDiff_fst))
    have := hint.parametric_integral (μ := MeasureTheory.volume) (k := Icc (0 : ℝ) 1)
      (s₀ := Ioc (0 : ℝ) 1) isCompact_Icc Ioc_subset_Icc_self (by simp)
    simpa [intervalIntegral.integral_of_le zero_le_one] using this
  · -- Taylor's formula with integral remainder
    intro ρ p
    set f : ℝ → V := fun s => φ (s, p) with hf
    have hfs : ContDiff ℝ ∞ f := hφ.comp (contDiff_id.prodMk contDiff_const)
    have htay := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := ρ) (n := n)
      (fun t _ => hfs.contDiffAt.of_le (by exact_mod_cast le_top))
    simp only [zero_add] at htay
    rw [show φ (ρ, p) = f ρ from rfl, htay]
    have hsum : ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k f 0 (fun _ => ρ) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, h0 p j (Finset.mem_range.mp hj)]
      simp
    rw [hsum, zero_add]
    have hrem : ∀ t : ℝ, (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (t • ρ) (fun _ => ρ) =
        ρ ^ (n + 1) • ((1 - t) ^ n • Dφ (t * ρ, p)) := by
      intro t
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_comm]
      simp [hDφ, hf, smul_eq_mul, Finset.prod_const]
    simp_rw [hrem, intervalIntegral.integral_smul, smul_comm (ρ ^ (n + 1))]
  · intro p
    simp only [mul_zero]
    rw [intervalIntegral.integral_smul_const]
    have hI : ∫ t in (0 : ℝ)..1, (1 - t) ^ n = 1 / (n + 1) := by
      have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (a := 0) (b := 1)
        (d := (1 : ℝ))
      simp only [sub_zero, sub_self] at this
      rw [this, integral_pow]
      simp
    rw [hI, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp

end S2S
