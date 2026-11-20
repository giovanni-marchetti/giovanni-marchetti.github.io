import SaddleToSaddle.EscapeInvariance

/-!
# Lemma 3 (Escape): centre manifold, blow-up, and uniqueness `(⋆)`

* *Centre manifold.* The linearization at `θ*` of the gradient flow of `F_{A ∪ {n}}` is
  `-∇²F_A(θ*) ⊕ 0`. By the centre manifold theorem there is a locally invariant manifold
  `W^c = {a = h(w_n)}`, and a trajectory of `S_{A ∪ {n}}` that stays near `θ*` for all `t ≤ t'`
  lies in `W^c`.
* *Blow-up.* On `W^c`, in the time `dτ = ρ^{k-2} dt`, the flow in polar coordinates `(ρ, u)` is
  the flow of a `C¹` vector field `X` with a hyperbolic equilibrium at `(0, u*)`, whose unstable
  manifold is a curve transverse to `{ρ = 0}`.
* `(⋆)`: two gradient-flow trajectories in `S_{A ∪ {n}}` with `0 < ρ ≤ ρ₁`, `|u - u*| ≤ r`,
  `|a - θ*| ≤ r` for all `t ≤ t'` pass through a common point, hence are time translates of
  each other.

We also record the consequence `|a - θ*| ≤ |w_n|` of `a = h(w_n)`, `Dh(0) = 0`, which is used to
normalize the escape orbit.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Θ ι E → ℝ} {k : ℕ}

/-- A backward gradient-flow trajectory on `(-∞, t']` in `S_{A ∪ {n}}` staying in the region
`0 < ρ ≤ ρ₁`, `|u - u*| ≤ r`, `|a - θ*| ≤ r`. -/
def BackwardNear (F : Θ ι E → ℝ) (A : Finset ι) (n : ι) (θ₀ : Θ ι E) (u₀ : E) (ρ₁ r : ℝ)
    (θ : ℝ → Θ ι E) (t' : ℝ) : Prop :=
  (∀ t ≤ t', HasDerivWithinAt θ (gf F (θ t)) (Iic t') t) ∧
  ∀ t ≤ t', θ t ∈ S (insert n A) ∧ 0 < ‖θ t n‖ ∧ ‖θ t n‖ ≤ ρ₁ ∧
    ‖‖θ t n‖⁻¹ • θ t n - u₀‖ ≤ r ∧ ‖proj A (θ t) - θ₀‖ ≤ r

namespace EscapeUnique

/-! ### Generic lemmas -/

/-- A function bounded by `C ‖p‖²` near `0` has derivative `0` at `0`. -/
private lemma hasFDerivAt_zero_of_le_sq {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {φ : P → Q} {C ε : ℝ} (hε : 0 < ε)
    (h : ∀ p, ‖p‖ ≤ ε → ‖φ p‖ ≤ C * ‖p‖ ^ 2) : HasFDerivAt φ (0 : P →L[ℝ] Q) 0 := by
  have h0 : φ 0 = 0 := by
    have := h 0 (by simp [hε.le])
    simpa using this
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun p : P => φ p) =O[𝓝 0] (fun p : P => ‖p‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Metric.closedBall_mem_nhds (0 : P) hε] with p hp
    rw [mem_closedBall, dist_zero_right] at hp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h p hp
  have := hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (E' := P) one_lt_two)
  simpa [h0] using this

/-- Backward decay: if `⟪d, d'⟫ ≤ -μ‖d‖²` on `(-∞, t']` and `d` is bounded, then `d = 0`. -/
private lemma eq_zero_of_backward_decay {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {d d' : ℝ → V} {t' μ M : ℝ} (hμ : 0 < μ)
    (hd : ∀ t ≤ t', HasDerivWithinAt d (d' t) (Iic t') t)
    (hineq : ∀ t ≤ t', ⟪d t, d' t⟫ ≤ -μ * ‖d t‖ ^ 2)
    (hM : ∀ t ≤ t', ‖d t‖ ≤ M) : ∀ t ≤ t', d t = 0 := by
  set φ : ℝ → ℝ := fun t => Real.exp (2 * μ * t) * ‖d t‖ ^ 2 with hφ
  have hφ' : ∀ t ≤ t', HasDerivWithinAt φ
      (Real.exp (2 * μ * t) * (2 * μ) * ‖d t‖ ^ 2 + Real.exp (2 * μ * t) * (2 * ⟪d t, d' t⟫))
      (Iic t') t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t => Real.exp (2 * μ * t)) (Real.exp (2 * μ * t) * (2 * μ))
        (Iic t') t := by
      have := ((hasDerivAt_id t).const_mul (2 * μ)).exp
      simpa using this.hasDerivWithinAt
    have h2 := (hd t ht).norm_sq
    exact h1.mul h2
  have hcont : ContinuousOn φ (Iic t') := fun t ht => (hφ' t ht).continuousWithinAt
  have hanti : AntitoneOn φ (Iic t') := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic t') hcont
    · intro x hx
      rw [interior_Iic] at hx ⊢
      exact ((hφ' x (le_of_lt hx)).hasDerivAt (Iic_mem_nhds hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      have hx' : x ≤ t' := le_of_lt hx
      have := hineq x hx'
      have he : 0 < Real.exp (2 * μ * x) := Real.exp_pos _
      nlinarith
  intro t ht
  have key : ∀ s ≤ t, ‖d t‖ ^ 2 ≤ Real.exp (2 * μ * (s - t)) * M ^ 2 := by
    intro s hs
    have hst : φ t ≤ φ s := hanti (show s ∈ Iic t' from le_trans hs ht) ht hs
    simp only [hφ] at hst
    have hMs : ‖d s‖ ^ 2 ≤ M ^ 2 := by
      have := hM s (le_trans hs ht)
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have he : Real.exp (2 * μ * (s - t)) = Real.exp (2 * μ * s) / Real.exp (2 * μ * t) := by
      rw [← Real.exp_sub]; ring_nf
    rw [he, div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos _)]
    calc ‖d t‖ ^ 2 * Real.exp (2 * μ * t) = Real.exp (2 * μ * t) * ‖d t‖ ^ 2 := by ring
      _ ≤ Real.exp (2 * μ * s) * ‖d s‖ ^ 2 := hst
      _ ≤ Real.exp (2 * μ * s) * M ^ 2 := by gcongr
  have hlim : Tendsto (fun s => Real.exp (2 * μ * (s - t)) * M ^ 2) atBot (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 2 * μ * (s - t)) atBot atBot := by
      apply Tendsto.const_mul_atBot (by positivity)
      exact tendsto_atBot_add_const_right _ _ tendsto_id
    have := (Real.tendsto_exp_atBot.comp h1).mul_const (M ^ 2)
    simpa using this
  have hle : ‖d t‖ ^ 2 ≤ 0 :=
    ge_of_tendsto hlim (eventually_atBot.2 ⟨t, fun s hs => key s hs⟩)
  have : ‖d t‖ = 0 := by nlinarith [norm_nonneg (d t)]
  exact norm_eq_zero.1 this

/-- A point of `S_{A ∪ {n}}` is `π_A θ + ι_n(θ_n)`. -/
private lemma eq_proj_add_single {A : Finset ι} {n : ι} (hn : n ∉ A) {θ : Θ ι E}
    (h : θ ∈ S (insert n A)) : θ = proj A θ + single n (θ n) := by
  rw [← proj_insert_eq hn, proj_eq_self_of_mem_S h]

/-- The `n`-th component of a trajectory. -/
private lemma hasDerivWithinAt_apply {θ : ℝ → Θ ι E} {θ' : Θ ι E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt θ θ' s t) (n : ι) :
    HasDerivWithinAt (fun t => θ t n) (θ' n) s t :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) n).hasFDerivAt.comp_hasDerivWithinAt t h

/-- Growth of `ρ` from `κρ^{k-1} ≤ ρ' ≤ Cρ^{k-1}` on `(-∞, t']`: `ρ → 0` as `t → -∞`, and
`∫_{-∞}^t ρ^{k-2} = ∞` in the form required by `time_change`. -/
private lemma rho_facts {ρ ρ' : ℝ → ℝ} {t' κ C : ℝ} (hk : 3 ≤ k) (hκ : 0 < κ) (hC : 0 < C)
    (hd : ∀ t ≤ t', HasDerivWithinAt ρ (ρ' t) (Iic t') t)
    (hpos : ∀ t ≤ t', 0 < ρ t)
    (hlow : ∀ t ≤ t', κ * ρ t ^ (k - 1) ≤ ρ' t)
    (hup : ∀ t ≤ t', ρ' t ≤ C * ρ t ^ (k - 1)) :
    (∀ ε > 0, ∃ s ≤ t', ρ s ≤ ε) ∧
    (∀ t ≤ t', ∃ g g' : ℝ → ℝ, Tendsto g atBot atBot ∧ (∀ s ≤ t, HasDerivAt g (g' s) s) ∧
      ∀ s ≤ t, g' s ≤ ρ s ^ (k - 2)) := by
  have hcont : ContinuousOn ρ (Iic t') := fun t ht => (hd t ht).continuousWithinAt
  have hderiv : ∀ a b, b ≤ t' → ∀ x ∈ Ico a b, HasDerivWithinAt ρ (ρ' x) (Ici x) x := by
    intro a b hb x hx
    have hxt : x < t' := lt_of_lt_of_le hx.2 hb
    exact ((hd x hxt.le).hasDerivAt (Iic_mem_nhds hxt)).hasDerivWithinAt
  have hk2 : ((k : ℝ) - 2) > 0 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkn : k - 2 ≠ 0 := by omega
  constructor
  · intro ε hε
    set T := (ε ^ (k - 2))⁻¹ / (((k : ℝ) - 2) * κ) with hT
    have hT0 : 0 ≤ T := by positivity
    refine ⟨t' - T, by linarith, ?_⟩
    have hab : t' - T ≤ t' := by linarith
    have h := inv_pow_le_of_deriv_ge hk (hcont.mono (Icc_subset_Iic_self))
      (hderiv (t' - T) t' le_rfl) (fun x hx => hpos x hx.2)
      (fun x hx => hlow x (le_of_lt (lt_of_lt_of_le hx.2 le_rfl))) t' ⟨hab, le_rfl⟩
    have hpos1 : 0 < (ρ t' ^ (k - 2))⁻¹ := by have := hpos t' le_rfl; positivity
    have h2 : (ε ^ (k - 2))⁻¹ ≤ (ρ (t' - T) ^ (k - 2))⁻¹ := by
      have e : ((k : ℝ) - 2) * κ * (t' - (t' - T)) = (ε ^ (k - 2))⁻¹ := by
        rw [hT]; field_simp; ring
      rw [e] at h
      linarith
    have hρs := hpos (t' - T) hab
    have h3 : ρ (t' - T) ^ (k - 2) ≤ ε ^ (k - 2) :=
      (inv_le_inv₀ (by positivity) (by positivity)).1 h2
    exact (pow_le_pow_iff_left₀ hρs.le hε.le hkn).1 h3
  · intro t ht
    set c := (ρ t ^ (k - 2))⁻¹ with hc
    set K := ((k : ℝ) - 2) * C with hK
    have hc0 : 0 < c := by have := hpos t ht; positivity
    have hK0 : 0 < K := by positivity
    refine ⟨fun s => -(1 / K) * Real.log (c + K * (t - s)), fun s => (c + K * (t - s))⁻¹,
      ?_, ?_, ?_⟩
    · have h1 : Tendsto (fun s : ℝ => c + K * (t - s)) atBot atTop := by
        have : Tendsto (fun s : ℝ => t - s) atBot atTop := by
          have := tendsto_neg_atBot_atTop (G := ℝ)
          simpa [sub_eq_add_neg, add_comm] using tendsto_atTop_add_const_left _ t this
        exact tendsto_atTop_add_const_left _ c (this.const_mul_atTop hK0)
      exact (Real.tendsto_log_atTop.comp h1).const_mul_atTop_of_neg (by
        have : 0 < 1 / K := by positivity
        linarith)
    · intro s hs
      have hpos' : 0 < c + K * (t - s) := by nlinarith
      have h1 : HasDerivAt (fun s : ℝ => c + K * (t - s)) (-K) s := by
        have := ((hasDerivAt_id' s).const_sub t).const_mul K
        simpa using this.const_add c
      have h2 := (h1.log hpos'.ne').const_mul (-(1 / K))
      convert h2 using 1
      field_simp
    · intro s hs
      have hab : s ≤ t := hs
      have h := inv_pow_ge_of_deriv_le hk (hcont.mono (Icc_subset_Iic_self.trans
        (Iic_subset_Iic.2 ht)))
        (hderiv s t ht) (fun x hx => hpos x (hx.2.trans ht))
        (fun x hx => hup x ((le_of_lt hx.2).trans ht)) t ⟨hab, le_rfl⟩
      have hρs := hpos s (hs.trans ht)
      have h2 : (ρ s ^ (k - 2))⁻¹ ≤ c + K * (t - s) := by rw [hc, hK]; linarith
      exact inv_le_of_inv_le₀ (by positivity) h2

/-- A backward solution of `Φ' = ρ^m X(Φ)` (with `ρ = Φ.1 > 0`) along which `∫ ρ^m = ∞` and which
stays in the ball of the unstable manifold theorem lies on the unstable manifold `u = ψ(ρ)`. -/
private lemma traj_on_curve {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {X : ℝ × W → ℝ × W} {ψ : ℝ → W} {δu : ℝ} {u₀ : W}
    (hψ : ∀ y : ℝ → ℝ × W, (∀ τ ≤ 0, HasDerivWithinAt y (X (y τ)) (Iic 0) τ) →
      (∀ τ ≤ 0, dist (y τ) (0, u₀) < δu) → (y 0).2 = ψ (y 0).1)
    {Φ : ℝ → ℝ × W} {t' : ℝ} {m : ℕ}
    (hΦ : ∀ t ≤ t', HasDerivWithinAt Φ ((Φ t).1 ^ m • X (Φ t)) (Iic t') t)
    (hpos : ∀ t ≤ t', 0 < (Φ t).1)
    (hdist : ∀ t ≤ t', dist (Φ t) (0, u₀) < δu)
    (hdiv : ∀ t ≤ t', ∃ g g' : ℝ → ℝ, Tendsto g atBot atBot ∧ (∀ s ≤ t, HasDerivAt g (g' s) s) ∧
      ∀ s ≤ t, g' s ≤ (Φ s).1 ^ m) :
    ∀ t ≤ t', (Φ t).2 = ψ (Φ t).1 := by
  have hcont : ContinuousOn Φ (Iic t') := fun t ht => (hΦ t ht).continuousWithinAt
  intro t ht
  have hsub : Iic t ⊆ Iic t' := Iic_subset_Iic.2 ht
  have hlam : ContinuousOn (fun s => (Φ s).1 ^ m) (Iic t) :=
    (continuous_fst.comp_continuousOn (hcont.mono hsub)).pow m
  obtain ⟨Yc, hY0, hYsol, hYrange⟩ := time_change X Φ (fun s => (Φ s).1 ^ m) t hlam
    (fun s hs => pow_pos (hpos s (hs.trans ht)) m)
    (fun s hs => (hΦ s (hs.trans ht)).mono hsub) (hdiv t ht)
  have := hψ Yc hYsol (fun τ hτ => by
    obtain ⟨s, hs, hYs⟩ := hYrange τ hτ
    rw [hYs]; exact hdist s (hs.trans ht))
  rw [hY0] at this
  exact this

/-! ### The centre manifold: notation and smoothness -/

/-- `∇F` is smooth. -/
private lemma gradient_contDiff (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (gradient F) := by
  have := (gf_contDiff hF).neg
  convert this using 1
  ext1 θ; simp [gf]

/-- The derivative of `∇F` is the Hessian. -/
private lemma inner_fderiv_gradient (hF : ContDiff ℝ ∞ F) (x v w : Θ ι E) :
    ⟪fderiv ℝ (gradient F) x v, w⟫ = fderiv ℝ (fderiv ℝ F) x v w := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((contDiff_infty_iff_fderiv.1 hF).2.differentiable (by simp)) x
  have hd1 : DifferentiableAt ℝ (gradient F) x :=
    (gradient_contDiff hF).differentiable (by simp) x
  have h1 := hd1.hasFDerivAt.inner ℝ (hasFDerivAt_const w x)
  have h2 := hd2.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have heq : (fun y => ⟪gradient F y, w⟫) = fun y => fderiv ℝ F y w := by
    ext1 y; exact inner_gradient F y w
  rw [heq] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simpa using this

/-! ### The centre manifold -/

/-- `π_A` with codomain `S_A`. -/
private def cmP (A : Finset ι) : Θ ι E →L[ℝ] ↥(SA (ι := ι) (E := E) A) :=
  (proj A).codRestrict (SA A) (proj_mem_S A)

private lemma cmP_coe (A : Finset ι) (v : Θ ι E) : ((cmP A v : ↥(SA A)) : Θ ι E) = proj A v := rfl

/-- The linear part `B = -∇²F_A(θ*)`. -/
private def cmB (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) :
    ↥(SA (ι := ι) (E := E) A) →L[ℝ] ↥(SA (ι := ι) (E := E) A) :=
  -((cmP A).comp ((fderiv ℝ (gradient F) θ₀).comp (SA A).subtypeL))

private lemma cmB_coe (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) (y : ↥(SA (ι := ι) (E := E) A)) :
    ((cmB F A θ₀ y : ↥(SA A)) : Θ ι E) = -proj A (fderiv ℝ (gradient F) θ₀ y) := rfl

/-- The point `θ* + y + ι_n(w)`. -/
private def cmx (A : Finset ι) (θ₀ : Θ ι E) (n : ι) (p : E × ↥(SA (ι := ι) (E := E) A)) :
    Θ ι E :=
  θ₀ + (p.2 : Θ ι E) + single n p.1

/-- The `w_n`-component of the vector field. -/
private def cmf (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι)
    (p : E × ↥(SA (ι := ι) (E := E) A)) : E :=
  -(gradient F (cmx A θ₀ n p)) n

/-- The nonlinear part of the `S_A`-component of the vector field. -/
private def cmg (F : Θ ι E → ℝ) (A : Finset ι) (θ₀ : Θ ι E) (n : ι)
    (p : E × ↥(SA (ι := ι) (E := E) A)) : ↥(SA (ι := ι) (E := E) A) :=
  cmP A (-(gradient F (cmx A θ₀ n p))) - cmB F A θ₀ p.2

private lemma cmx_apply_n {A : Finset ι} {θ₀ : Θ ι E} {n : ι} (hθ₀ : θ₀ ∈ S A) (hn : n ∉ A)
    (p : E × ↥(SA (ι := ι) (E := E) A)) : cmx A θ₀ n p n = p.1 := by
  have h1 : θ₀ n = 0 := hθ₀ n hn
  have h2 : (p.2 : Θ ι E) n = 0 := p.2.2 n hn
  simp [cmx, h1, h2]

private lemma zeroAt_cmx {A : Finset ι} {θ₀ : Θ ι E} {n : ι} (hθ₀ : θ₀ ∈ S A) (hn : n ∉ A)
    (p : E × ↥(SA (ι := ι) (E := E) A)) : zeroAt n (cmx A θ₀ n p) = cmx A θ₀ n (0, p.2) := by
  have h1 : θ₀ n = 0 := hθ₀ n hn
  have h2 : (p.2 : Θ ι E) n = 0 := p.2.2 n hn
  ext m
  by_cases hm : m = n
  · subst hm; simp [cmx, h1, h2]
  · simp [cmx, hm, single_apply_of_ne hm]

private lemma cmx_contDiff (A : Finset ι) (θ₀ : Θ ι E) (n : ι) :
    ContDiff ℝ ∞ (cmx A θ₀ n) := by
  have h1 : ContDiff ℝ ∞ (fun p : E × ↥(SA (ι := ι) (E := E) A) => (p.2 : Θ ι E)) :=
    (SA (ι := ι) (E := E) A).subtypeL.contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun p : E × ↥(SA (ι := ι) (E := E) A) => (single n p.1 : Θ ι E)) :=
    (singleL (E := E) n).contDiff.comp contDiff_fst
  exact (contDiff_const.add h1).add h2

private lemma cmx_norm_le (A : Finset ι) (θ₀ : Θ ι E) (n : ι)
    (p : E × ↥(SA (ι := ι) (E := E) A)) (hp : ‖p‖ ≤ 1) : ‖cmx A θ₀ n p‖ ≤ ‖θ₀‖ + 2 := by
  have h1 : ‖(p.2 : Θ ι E)‖ ≤ 1 := by
    rw [Submodule.norm_coe]; exact (norm_snd_le p).trans hp
  have h2 : ‖(single n p.1 : Θ ι E)‖ ≤ 1 := by
    rw [norm_single]; exact (norm_fst_le p).trans hp
  calc ‖cmx A θ₀ n p‖ ≤ ‖θ₀ + (p.2 : Θ ι E)‖ + ‖(single n p.1 : Θ ι E)‖ := norm_add_le _ _
    _ ≤ ‖θ₀‖ + ‖(p.2 : Θ ι E)‖ + ‖(single n p.1 : Θ ι E)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖θ₀‖ + 2 := by linarith

private lemma cmf_contDiff (hF : ContDiff ℝ ∞ F) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) :
    ContDiff ℝ 2 (cmf F A θ₀ n) := by
  have : ContDiff ℝ ∞ (cmf F A θ₀ n) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) n).contDiff.comp
      ((gradient_contDiff hF).comp (cmx_contDiff A θ₀ n))).neg
  exact contDiff_infty.1 this 2

private lemma cmg_contDiff (hF : ContDiff ℝ ∞ F) (A : Finset ι) (θ₀ : Θ ι E) (n : ι) :
    ContDiff ℝ 2 (cmg F A θ₀ n) := by
  have h1 : ContDiff ℝ ∞ (fun p => gradient F (cmx A θ₀ n p)) :=
    (gradient_contDiff hF).comp (cmx_contDiff A θ₀ n)
  have h2 : ContDiff ℝ ∞ (fun p => cmP A (-(gradient F (cmx A θ₀ n p)))) :=
    (cmP (E := E) A).contDiff.comp h1.neg
  have h3 : ContDiff ℝ ∞ (fun p : E × ↥(SA (ι := ι) (E := E) A) => cmB F A θ₀ p.2) :=
    (cmB F A θ₀).contDiff.comp contDiff_snd
  have : ContDiff ℝ ∞ (cmg F A θ₀ n) := h2.sub h3
  exact contDiff_infty.1 this 2

private lemma cmx_zero (A : Finset ι) (θ₀ : Θ ι E) (n : ι) :
    cmx A θ₀ n (0 : E × ↥(SA (ι := ι) (E := E) A)) = θ₀ := by
  simp [cmx]

/-! ### The blow-up -/

/-- `G̃(ρ, u) = G(ρ, u, θ* + h(ρu))`. -/
private def bG (G : ℝ × E × Θ ι E → E) (θ₀ : Θ ι E) (hc : E → Θ ι E) (p : ℝ × E) : E :=
  G (p.1, p.2, θ₀ + hc (p.1 • p.2))

/-- The blown-up vector field `X(ρ, u) = (ρ⟪u, G̃⟫, G̃ - ⟪u, G̃⟫ u)`. -/
private def bX (G : ℝ × E × Θ ι E → E) (θ₀ : Θ ι E) (hc : E → Θ ι E) (p : ℝ × E) : ℝ × E :=
  (p.1 * ⟪p.2, bG G θ₀ hc p⟫, bG G θ₀ hc p - ⟪p.2, bG G θ₀ hc p⟫ • p.2)

private lemma bG_contDiff {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) (θ₀ : Θ ι E)
    {hc : E → Θ ι E} (hhc : ContDiff ℝ 1 hc) : ContDiff ℝ 1 (bG G θ₀ hc) := by
  have h1 : ContDiff ℝ 1 (fun p : ℝ × E => p.1 • p.2) := contDiff_fst.smul contDiff_snd
  have h2 : ContDiff ℝ 1 (fun p : ℝ × E => θ₀ + hc (p.1 • p.2)) :=
    contDiff_const.add (hhc.comp h1)
  have h3 : ContDiff ℝ 1 (fun p : ℝ × E => (p.1, p.2, θ₀ + hc (p.1 • p.2))) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk h2)
  exact (contDiff_infty.1 hG 1).comp h3

private lemma bX_contDiff {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) (θ₀ : Θ ι E)
    {hc : E → Θ ι E} (hhc : ContDiff ℝ 1 hc) : ContDiff ℝ 1 (bX G θ₀ hc) := by
  have hb := bG_contDiff hG θ₀ hhc
  have hD : ContDiff ℝ 1 (fun p : ℝ × E => ⟪p.2, bG G θ₀ hc p⟫) := contDiff_snd.inner ℝ hb
  exact (contDiff_fst.mul hD).prodMk (hb.sub (hD.smul contDiff_snd))

private lemma bG_zero {G : ℝ × E × Θ ι E → E} {θ₀ : Θ ι E} {hc : E → Θ ι E} (hc0 : hc 0 = 0)
    {n : ι} (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) (u : E) :
    bG G θ₀ hc (0, u) = gradient (U F k n θ₀) u := by
  simp [bG, hc0, hG0]

private lemma bX_zero_left {G : ℝ × E × Θ ι E → E} {θ₀ : Θ ι E} {hc : E → Θ ι E}
    (hc0 : hc 0 = 0) {n : ι} (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) (u : E) :
    bX G θ₀ hc (0, u) = (0, gradient (U F k n θ₀) u -
      ⟪u, gradient (U F k n θ₀) u⟫ • u) := by
  simp only [bX, bG_zero hc0 hG0, zero_mul]

/-- At a critical point of `U` on the sphere, `∇U(u*) = k U(u*) u*`. -/
private lemma gradU_eq {n : ι} {θ₀ : Θ ι E} {u₀ : E} (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) :
    gradient (U F k n θ₀) u₀ = ((k : ℝ) * U F k n θ₀ u₀) • u₀ := by
  set g₀ := gradient (U F k n θ₀) u₀
  set lam := (k : ℝ) * U F k n θ₀ u₀
  have he : ⟪u₀, g₀⟫ = lam := euler n θ₀ u₀
  have hu1 : ⟪u₀, u₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu.norm_eq]; norm_num
  set v := g₀ - lam • u₀ with hv
  have hvu : ⟪v, u₀⟫ = 0 := by
    rw [hv, inner_sub_left, real_inner_smul_left, hu1, real_inner_comm, he]; ring
  have hgv : ⟪g₀, v⟫ = 0 := by
    rw [inner_gradient_E]; exact hu.crit v hvu
  have hvv : ⟪v, v⟫ = 0 := by
    conv_lhs => rw [hv]
    rw [inner_sub_left, hgv, real_inner_smul_left, real_inner_comm, hvu]; ring
  have : v = 0 := inner_self_eq_zero.1 hvv
  rw [hv, sub_eq_zero] at this
  exact this

private lemma bX_zero {G : ℝ × E × Θ ι E → E} {θ₀ : Θ ι E} {hc : E → Θ ι E}
    (hc0 : hc 0 = 0) {n : ι} (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) {u₀ : E}
    (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) : bX G θ₀ hc (0, u₀) = 0 := by
  rw [bX_zero_left hc0 hG0, gradU_eq hu, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu.norm_eq]
  simp

/-- The linearization of `V(u) = ∇U(u) - ⟪u, ∇U(u)⟫ u` at `u*` is negative definite. -/
private lemma negdef_core {u₀ g₀ : E} {Hs : E →L[ℝ] E} {lam c kk : ℝ}
    (hu1 : ‖u₀‖ = 1) (hg₀ : g₀ = lam • u₀)
    (hsym : ∀ x y, ⟪Hs x, y⟫ = ⟪x, Hs y⟫) (hself : Hs u₀ = (kk - 1) • g₀)
    (hhess : ∀ v, ⟪v, u₀⟫ = 0 → ⟪Hs v, v⟫ - lam * ‖v‖ ^ 2 ≤ -c * ‖v‖ ^ 2) (v : E) :
    ⟪Hs v - (⟪u₀, g₀⟫ • v + (⟪u₀, Hs v⟫ + ⟪v, g₀⟫) • u₀), v⟫ ≤
      -(min c (2 * lam)) * ‖v‖ ^ 2 := by
  have hu1' : ⟪u₀, u₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu1]; norm_num
  set β := ⟪u₀, v⟫ with hβ
  have hug : ⟪u₀, g₀⟫ = lam := by rw [hg₀, real_inner_smul_right, hu1']; ring
  have hvg : ⟪v, g₀⟫ = lam * β := by rw [hg₀, real_inner_smul_right, real_inner_comm]
  have huHv : ⟪u₀, Hs v⟫ = (kk - 1) * lam * β := by
    rw [← hsym, hself, hg₀, smul_smul, real_inner_smul_left]
  have hHvu : ⟪Hs v, u₀⟫ = (kk - 1) * lam * β := by
    rw [real_inner_comm, huHv]
  have hHuu : ⟪Hs u₀, u₀⟫ = (kk - 1) * lam := by
    rw [hself, hg₀, smul_smul, real_inner_smul_left, hu1']; ring
  have hHuv : ⟪Hs u₀, v⟫ = (kk - 1) * lam * β := by
    rw [hsym, huHv]
  set w := v - β • u₀ with hw
  have hwu : ⟪w, u₀⟫ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hu1', real_inner_comm]; ring
  have hww : ‖w‖ ^ 2 = ‖v‖ ^ 2 - β ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hw, inner_sub_left,
      inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, hu1', real_inner_comm u₀ v, ← hβ]
    ring
  have hHww : ⟪Hs w, w⟫ = ⟪Hs v, v⟫ - (kk - 1) * lam * β ^ 2 := by
    rw [hw, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      hHvu, hHuv, hHuu]
    ring
  have h1 := hhess w hwu
  rw [hHww, hww] at h1
  have hLHS : ⟪Hs v - (⟪u₀, g₀⟫ • v + (⟪u₀, Hs v⟫ + ⟪v, g₀⟫) • u₀), v⟫ =
      ⟪Hs v, v⟫ - lam * ‖v‖ ^ 2 - kk * lam * β ^ 2 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hug, huHv, hvg, ← hβ]
    ring
  rw [hLHS]
  have hm1 : min c (2 * lam) ≤ c := min_le_left _ _
  have hm2 : min c (2 * lam) ≤ 2 * lam := min_le_right _ _
  have hw0 : 0 ≤ ‖v‖ ^ 2 - β ^ 2 := by rw [← hww]; positivity
  have hb0 : 0 ≤ β ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.2 hm1) hw0, mul_nonneg (sub_nonneg.2 hm2) hb0]

/-- `V(u) = ∇U(u) - ⟪u, ∇U(u)⟫ u`, the spherical gradient of `U`. -/
private def sphV (F : Θ ι E → ℝ) (k : ℕ) (n : ι) (θ₀ : Θ ι E) (u : E) : E :=
  gradient (U F k n θ₀) u - ⟪u, gradient (U F k n θ₀) u⟫ • u

private lemma gradU_contDiff' {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) (θ₀ : Θ ι E) :
    ContDiff ℝ ∞ (gradient (U F k n θ₀)) := by
  have : gradient (U F k n θ₀) = fun u => G (0, u, θ₀) := by
    ext1 u; exact (hG0 u θ₀).symm
  rw [this]
  exact hG.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))

/-- The linearization of the blown-up vector field at `(0, u*)`. -/
private lemma bX_fderiv {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {θ₀ : Θ ι E}
    {hc : E → Θ ι E} (hhc : ContDiff ℝ 1 hc) (hc0 : hc 0 = 0) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) {u₀ : E} (r : ℝ) (v : E) :
    fderiv ℝ (bX G θ₀ hc) (0, u₀) (r, v) =
      ((k : ℝ) * U F k n θ₀ u₀ * r, r • (fderiv ℝ (bX G θ₀ hc) (0, u₀) (1, 0)).2 +
        fderiv ℝ (sphV F k n θ₀) u₀ v) := by
  set DX := fderiv ℝ (bX G θ₀ hc) (0, u₀) with hDX
  have hXd : HasFDerivAt (bX G θ₀ hc) DX (0, u₀) :=
    ((bX_contDiff hG θ₀ hhc).differentiable (by norm_num) (0, u₀)).hasFDerivAt
  have hgU := gradU_contDiff' hG hG0 θ₀
  have hVc : ContDiff ℝ ∞ (sphV F k n θ₀) := by
    unfold sphV
    exact hgU.sub ((contDiff_id.inner ℝ hgU).smul contDiff_id)
  have hVd : HasFDerivAt (sphV F k n θ₀) (fderiv ℝ (sphV F k n θ₀) u₀) u₀ :=
    (hVc.differentiable (by simp) u₀).hasFDerivAt
  -- the derivative in the `u`-direction
  have ha : DX (0, v) = (0, fderiv ℝ (sphV F k n θ₀) u₀ v) := by
    have hcomp : HasFDerivAt (fun u => bX G θ₀ hc (0, u))
        (DX.comp (ContinuousLinearMap.inr ℝ ℝ E)) u₀ :=
      hXd.comp u₀ (hasFDerivAt_prodMk_right (0 : ℝ) u₀)
    have hfun : (fun u => bX G θ₀ hc (0, u)) = fun u => ((0 : ℝ), sphV F k n θ₀ u) := by
      ext1 u; exact bX_zero_left hc0 hG0 u
    rw [hfun] at hcomp
    have hV' : HasFDerivAt (fun u => ((0 : ℝ), sphV F k n θ₀ u))
        ((0 : E →L[ℝ] ℝ).prod (fderiv ℝ (sphV F k n θ₀) u₀)) u₀ :=
      (hasFDerivAt_const (0 : ℝ) u₀).prodMk hVd
    have heq := hcomp.unique hV'
    have := congrArg (fun L : E →L[ℝ] ℝ × E => L v) heq
    simpa using this
  -- the derivative in the `ρ`-direction
  have hb : (DX (1, 0)).1 = (k : ℝ) * U F k n θ₀ u₀ := by
    have hline : HasDerivAt (fun s : ℝ => (s, u₀)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id' 0).prodMk (hasDerivAt_const 0 u₀)
    have h1₀ := hXd.comp_hasDerivAt (0 : ℝ) hline
    have h1 : HasDerivAt (fun s => bX G θ₀ hc (s, u₀)) (DX (1, 0)) 0 := h1₀
    have h1fst₀ := (hasFDerivAt_fst (p := bX G θ₀ hc (0, u₀))).comp_hasDerivAt (0 : ℝ) h1
    have h1fst : HasDerivAt (fun s => (bX G θ₀ hc (s, u₀)).1) (DX (1, 0)).1 0 := h1fst₀
    have hbG₀ := ((bG_contDiff hG θ₀ hhc).differentiable (by norm_num)
      (0, u₀)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
    have hbG : HasDerivAt (fun s => bG G θ₀ hc (s, u₀))
        (fderiv ℝ (bG G θ₀ hc) (0, u₀) (1, 0)) 0 := hbG₀
    have hD := (hasDerivAt_const (0 : ℝ) u₀).inner ℝ hbG
    have hm := (hasDerivAt_id' (0 : ℝ)).fun_mul hD
    have heq := h1fst.unique hm
    rw [heq]
    simp only [one_mul, zero_mul, add_zero, inner_zero_left]
    rw [bG_zero hc0 hG0]
    exact euler n θ₀ u₀
  have hsplit : ((r, v) : ℝ × E) = r • ((1 : ℝ), (0 : E)) + ((0 : ℝ), v) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, ha]
  ext
  · simp [hb]; ring
  · simp

/-- The derivative of the spherical gradient `V` at `u*`. -/
private lemma sphV_fderiv_apply {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) (θ₀ : Θ ι E) (u₀ v : E) :
    fderiv ℝ (sphV F k n θ₀) u₀ v =
      fderiv ℝ (gradient (U F k n θ₀)) u₀ v -
        (⟪u₀, gradient (U F k n θ₀) u₀⟫ • v +
          (⟪u₀, fderiv ℝ (gradient (U F k n θ₀)) u₀ v⟫ + ⟪v, gradient (U F k n θ₀) u₀⟫) • u₀) := by
  have hgU := gradU_contDiff' hG hG0 θ₀
  have hVc : ContDiff ℝ ∞ (sphV F k n θ₀) := by
    unfold sphV
    exact hgU.sub ((contDiff_id.inner ℝ hgU).smul contDiff_id)
  set g := gradient (U F k n θ₀)
  set Hs := fderiv ℝ g u₀
  have hℓ : HasDerivAt (fun s : ℝ => u₀ + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add u₀
  have hℓ0 : u₀ + (0 : ℝ) • v = u₀ := by simp
  have hg : HasDerivAt (fun s : ℝ => g (u₀ + s • v)) (Hs v) 0 :=
    (hgU.differentiable (by simp) u₀).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0.symm
  have hin := hℓ.inner ℝ hg
  have hsm := hin.smul hℓ
  have hV := hg.sub hsm
  have hV' : HasDerivAt (fun s : ℝ => sphV F k n θ₀ (u₀ + s • v))
      (fderiv ℝ (sphV F k n θ₀) u₀ v) 0 :=
    (hVc.differentiable (by simp) u₀).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0.symm
  rw [hV'.unique hV]
  simp only [hℓ0]

/-- The linearization `H` of `V` at `u*` is negative definite. -/
private lemma sphV_negdef (hk : 3 ≤ k) {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) {θ₀ : Θ ι E} {u₀ : E}
    (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀) :
    ∃ c > 0, ∀ v, ⟪fderiv ℝ (sphV F k n θ₀) u₀ v, v⟫ ≤ -c * ‖v‖ ^ 2 := by
  obtain ⟨c, hc, hhess⟩ := hu.hess
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam : 0 < (k : ℝ) * U F k n θ₀ u₀ := mul_pos hk0 hU
  refine ⟨min c (2 * ((k : ℝ) * U F k n θ₀ u₀)), lt_min hc (by positivity), fun v => ?_⟩
  rw [sphV_fderiv_apply hG hG0 θ₀ u₀ v]
  apply negdef_core hu.norm_eq (gradU_eq hu) (hessU_symm n θ₀ u₀)
    (hessU_self hk n θ₀ u₀)
  intro w hw
  have := hhess w hw
  rw [← inner_fderiv_gradU] at this
  linarith

/-- The local unstable manifold of `(0, u*)` for the blown-up vector field. -/
private lemma unstable_data (hk : 3 ≤ k) {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) {θ₀ : Θ ι E} {hc : E → Θ ι E}
    (hhc : ContDiff ℝ 1 hc) (hc0 : hc 0 = 0) {u₀ : E}
    (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀) :
    ∃ δ > 0, ∃ ψ : ℝ → E, ∀ y : ℝ → ℝ × E,
      (∀ τ ≤ 0, HasDerivWithinAt y (bX G θ₀ hc (y τ)) (Iic 0) τ) →
      (∀ τ ≤ 0, dist (y τ) (0, u₀) < δ) → (y 0).2 = ψ (y 0).1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨δ, hδ, ψ, -, -, hψ, -⟩ := unstable_manifold (bX G θ₀ hc) (bX_contDiff hG θ₀ hhc) u₀
    (bX_zero hc0 hG0 hu) ((k : ℝ) * U F k n θ₀ u₀) (mul_pos hk0 hU) _
    (fderiv ℝ (sphV F k n θ₀) u₀) (sphV_negdef hk hG hG0 hu hU)
    (fun r v => bX_fderiv hG hhc hc0 hG0 r v)
  exact ⟨δ, hδ, ψ, hψ⟩

/-- Polar coordinates on the centre manifold: `(ρ, u)` solves `Φ' = ρ^{k-2} X(Φ)`. -/
private lemma polar_deriv (hk : 3 ≤ k) {A : Finset ι} {n : ι} (hn : n ∉ A)
    {G : ℝ × E × Θ ι E → E} {θ₀ : Θ ι E} {hc : E → Θ ι E}
    (hpolar : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    {θ : ℝ → Θ ι E} {s : Set ℝ} {t : ℝ} (hθd : HasDerivWithinAt θ (gf F (θ t)) s t)
    (hdec : θ t = θ₀ + hc (θ t n) + single n (θ t n)) (hS : θ₀ + hc (θ t n) ∈ S A)
    (hpos : 0 < ‖θ t n‖) :
    HasDerivWithinAt (fun t => (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n))
      (‖θ t n‖ ^ (k - 2) • bX G θ₀ hc (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n)) s t := by
  obtain ⟨w, hw⟩ : ∃ w, w = θ t n := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = ‖w‖ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = ρ⁻¹ • w := ⟨_, rfl⟩
  rw [← hw] at hdec hS hpos ⊢
  rw [← hρ] at hpos ⊢
  rw [← hu]
  have hρ0 : ρ ≠ 0 := hpos.ne'
  have hρu : ρ • u = w := by rw [hu, smul_inv_smul₀ hρ0]
  have hx0 : (θ₀ + hc w) n = 0 := hS n hn
  have hins : insertAt (θ₀ + hc w) n (ρ • u) = θ t := by
    rw [hρu, insertAt_eq_add _ _ _ hx0, ← hdec]
  set g := bG G θ₀ hc (ρ, u) with hg
  set D := ⟪u, g⟫ with hD
  have hgfn : (gf F (θ t)) n = ρ ^ (k - 1) • g := by
    have := hpolar ρ u (θ₀ + hc w)
    rw [hins] at this
    have e : (gf F (θ t)) n = -(gradient F (θ t)) n := by simp [gf]
    rw [e, this, hg]
    simp only [bG, hρu]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  -- the derivative of `w`
  have hwd : HasDerivWithinAt (fun t => θ t n) (ρ ^ (k - 1) • g) s t := by
    rw [← hgfn]; exact hasDerivWithinAt_apply hθd n
  -- the derivative of `ρ = ‖w‖`
  have hρd : HasDerivWithinAt (fun t => ‖θ t n‖) (ρ ^ (k - 2) * (ρ * D)) s t := by
    have h2 := hwd.norm_sq
    have h3 := h2.sqrt (by rw [← hw, ← hρ]; positivity)
    have e : (fun t => √(‖θ t n‖ ^ 2)) = fun t => ‖θ t n‖ := by
      ext1 t; exact Real.sqrt_sq (norm_nonneg _)
    rw [e] at h3
    convert h3 using 1
    rw [← hw, ← hρ, Real.sqrt_sq hpos.le, ← hρu, real_inner_smul_left, real_inner_smul_right,
      ← hD, hk1, pow_succ]
    field_simp
  -- the derivative of `u = ρ⁻¹ w`
  have hud : HasDerivWithinAt (fun t => ‖θ t n‖⁻¹ • θ t n)
      (ρ ^ (k - 2) • (g - D • u)) s t := by
    have h1 := (hρd.fun_inv (by rw [← hw, ← hρ]; exact hρ0)).fun_smul hwd
    convert h1 using 1
    rw [← hw, ← hρ]
    conv_rhs => rw [← hρu]
    rw [smul_smul, smul_smul, smul_sub, smul_smul, hk1, pow_succ]
    have e1 : ρ⁻¹ * (ρ ^ (k - 2) * ρ) = ρ ^ (k - 2) := by field_simp
    have e2 : -(ρ ^ (k - 2) * (ρ * D)) / ρ ^ 2 * ρ = -(ρ ^ (k - 2) * D) := by field_simp
    rw [e1, e2, neg_smul, ← sub_eq_add_neg]
  have := hρd.prodMk hud
  convert this using 1
  rw [show bX G θ₀ hc (ρ, u) = (ρ * D, g - D • u) from rfl, Prod.smul_mk, smul_eq_mul]

/-- `⟪u, G̃⟫` is close to `λ = kU(u*)` near `(0, u*)`. -/
private lemma bD_bounds {G : ℝ × E × Θ ι E → E} (hG : ContDiff ℝ ∞ G) {θ₀ : Θ ι E}
    {hc : E → Θ ι E} (hhc : ContDiff ℝ 1 hc) (hc0 : hc 0 = 0) {n : ι}
    (hG0 : ∀ u θ, G (0, u, θ) = gradient (U F k n θ) u) {u₀ : E} {lam : ℝ} (hlam : 0 < lam)
    (hval : ⟪u₀, gradient (U F k n θ₀) u₀⟫ = lam) :
    ∃ δ₁ > 0, ∀ p : ℝ × E, dist p (0, u₀) < δ₁ →
      lam / 2 ≤ ⟪p.2, bG G θ₀ hc p⟫ ∧ ⟪p.2, bG G θ₀ hc p⟫ ≤ 3 * lam / 2 := by
  have hcont : Continuous (fun p : ℝ × E => ⟪p.2, bG G θ₀ hc p⟫) :=
    continuous_snd.inner (bG_contDiff hG θ₀ hhc).continuous
  have h0 : ⟪((0 : ℝ), u₀).2, bG G θ₀ hc (0, u₀)⟫ = lam := by
    rw [bG_zero hc0 hG0]; exact hval
  obtain ⟨δ₁, hδ₁, h⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := ((0 : ℝ), u₀)))
    (lam / 2) (by positivity)
  refine ⟨δ₁, hδ₁, fun p hp => ?_⟩
  have := h hp
  rw [h0, Real.dist_eq, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

/-- Along a backward trajectory on the centre manifold staying near `(ρ, u) = (0, u*)`,
`u = ψ(ρ)`, and `ρ → 0` as `t → -∞`. -/
private lemma key_traj (hk : 3 ≤ k) {A : Finset ι} {n : ι} (hn : n ∉ A)
    {G : ℝ × E × Θ ι E → E} {θ₀ : Θ ι E} {hc : E → Θ ι E} {u₀ : E}
    (hpolar : ∀ ρ u θ, -(gradient F (insertAt θ n (ρ • u))) n = ρ ^ (k - 1) • G (ρ, u, θ))
    (hcS : ∀ w, hc w ∈ S A) (hθ₀ : θ₀ ∈ S A) {ψ : ℝ → E} {δu : ℝ}
    (hψ : ∀ y : ℝ → ℝ × E, (∀ τ ≤ 0, HasDerivWithinAt y (bX G θ₀ hc (y τ)) (Iic 0) τ) →
      (∀ τ ≤ 0, dist (y τ) (0, u₀) < δu) → (y 0).2 = ψ (y 0).1)
    {lam δ₁ : ℝ} (hlam : 0 < lam)
    (hD : ∀ p : ℝ × E, dist p (0, u₀) < δ₁ →
      lam / 2 ≤ ⟪p.2, bG G θ₀ hc p⟫ ∧ ⟪p.2, bG G θ₀ hc p⟫ ≤ 3 * lam / 2)
    {θ : ℝ → Θ ι E} {t' : ℝ}
    (hθd : ∀ t ≤ t', HasDerivWithinAt θ (gf F (θ t)) (Iic t') t)
    (hdec : ∀ t ≤ t', θ t = θ₀ + hc (θ t n) + single n (θ t n))
    (hpos : ∀ t ≤ t', 0 < ‖θ t n‖)
    (hnear : ∀ t ≤ t', dist ((‖θ t n‖, ‖θ t n‖⁻¹ • θ t n) : ℝ × E) (0, u₀) < min δu δ₁) :
    (∀ t ≤ t', ‖θ t n‖⁻¹ • θ t n = ψ ‖θ t n‖) ∧ (∀ ε > 0, ∃ s ≤ t', ‖θ s n‖ ≤ ε) := by
  set Φ : ℝ → ℝ × E := fun t => (‖θ t n‖, ‖θ t n‖⁻¹ • θ t n) with hΦdef
  have hΦ : ∀ t ≤ t', HasDerivWithinAt Φ ((Φ t).1 ^ (k - 2) • bX G θ₀ hc (Φ t)) (Iic t') t :=
    fun t ht => polar_deriv hk hn hpolar (hθd t ht) (hdec t ht) (S_add hθ₀ (hcS _)) (hpos t ht)
  set ρ' : ℝ → ℝ := fun t => (Φ t).1 ^ (k - 2) * ((Φ t).1 * ⟪(Φ t).2, bG G θ₀ hc (Φ t)⟫)
    with hρ'
  have hρd : ∀ t ≤ t', HasDerivWithinAt (fun t => ‖θ t n‖) (ρ' t) (Iic t') t := by
    intro t ht
    have h := (hasFDerivAt_fst (p := Φ t)).comp_hasDerivWithinAt t (hΦ t ht)
    exact h
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have hρ'eq : ∀ t, ρ' t = ‖θ t n‖ ^ (k - 1) * ⟪(Φ t).2, bG G θ₀ hc (Φ t)⟫ := by
    intro t
    simp only [hρ', hΦdef, hk1, pow_succ]
    ring
  have hlow : ∀ t ≤ t', lam / 2 * ‖θ t n‖ ^ (k - 1) ≤ ρ' t := by
    intro t ht
    rw [hρ'eq]
    have h1 := (hD (Φ t) (lt_of_lt_of_le (hnear t ht) (min_le_right _ _))).1
    have h2 : 0 ≤ ‖θ t n‖ ^ (k - 1) := by positivity
    nlinarith
  have hup : ∀ t ≤ t', ρ' t ≤ 3 * lam / 2 * ‖θ t n‖ ^ (k - 1) := by
    intro t ht
    rw [hρ'eq]
    have h1 := (hD (Φ t) (lt_of_lt_of_le (hnear t ht) (min_le_right _ _))).2
    have h2 : 0 ≤ ‖θ t n‖ ^ (k - 1) := by positivity
    nlinarith
  obtain ⟨hzero, hdiv⟩ := rho_facts hk (by positivity) (by positivity) hρd hpos hlow hup
  refine ⟨?_, hzero⟩
  exact traj_on_curve hψ hΦ hpos
    (fun t ht => lt_of_lt_of_le (hnear t ht) (min_le_left _ _)) hdiv

end EscapeUnique

variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
include hF hk hH

namespace EscapeUnique

/-! ### The centre manifold theorem and attraction -/

private lemma cmf_zero {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) (n : ι) :
    cmf F A θ₀ n 0 = 0 := by
  simp [cmf, cmx_zero, gradient_eq_zero_of_isNondegMin hF hk hH hmin]

private lemma cmg_zero {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) (n : ι) :
    cmg F A θ₀ n 0 = 0 := by
  simp [cmg, cmx_zero, gradient_eq_zero_of_isNondegMin hF hk hH hmin]

private lemma cmf_fderiv {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι}
    (hn : n ∉ A) : fderiv ℝ (cmf F A θ₀ n) 0 = 0 := by
  obtain ⟨C, hC0, hC⟩ := grad_apply_le hF hk hH (‖θ₀‖ + 2)
  apply HasFDerivAt.fderiv
  apply hasFDerivAt_zero_of_le_sq (C := C) zero_lt_one
  intro p hp
  have h1 := hC n (cmx A θ₀ n p) (cmx_norm_le A θ₀ n p hp)
  rw [cmx_apply_n hmin.mem hn] at h1
  have h2 : ‖p.1‖ ^ (k - 1) ≤ ‖p‖ ^ (k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le p) _
  have h3 : ‖p‖ ^ (k - 1) ≤ ‖p‖ ^ 2 :=
    pow_le_pow_of_le_one (norm_nonneg _) hp (by omega)
  calc ‖cmf F A θ₀ n p‖ = ‖(gradient F (cmx A θ₀ n p)) n‖ := by simp [cmf]
    _ ≤ C * ‖p.1‖ ^ (k - 1) := h1
    _ ≤ C * ‖p‖ ^ 2 := by gcongr; exact h2.trans h3

private lemma cmg_fderiv {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι}
    (hn : n ∉ A) : fderiv ℝ (cmg F A θ₀ n) 0 = 0 := by
  obtain ⟨C, hC0, hC⟩ := proj_grad_sub_zeroAt_le hF hk hH A (‖θ₀‖ + 2)
  -- the part depending on `w`
  have h1 : HasFDerivAt (fun p => cmg F A θ₀ n p - cmg F A θ₀ n (0, p.2))
      (0 : E × ↥(SA (ι := ι) (E := E) A) →L[ℝ] ↥(SA (ι := ι) (E := E) A)) 0 := by
    apply hasFDerivAt_zero_of_le_sq (C := C) zero_lt_one
    intro p hp
    have h1 := hC n hn (cmx A θ₀ n p) (cmx_norm_le A θ₀ n p hp)
    rw [cmx_apply_n hmin.mem hn, zeroAt_cmx hmin.mem hn] at h1
    have h2 : ‖p.1‖ ^ k ≤ ‖p‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le p) _
    have h3 : ‖p‖ ^ k ≤ ‖p‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hp (by omega)
    have heq : ((cmg F A θ₀ n p - cmg F A θ₀ n (0, p.2) : ↥(SA A)) : Θ ι E) =
        -(proj A (gradient F (cmx A θ₀ n p)) - proj A (gradient F (cmx A θ₀ n (0, p.2)))) := by
      have e1 : cmg F A θ₀ n p - cmg F A θ₀ n (0, p.2) =
          cmP A (-(gradient F (cmx A θ₀ n p))) - cmP A (-(gradient F (cmx A θ₀ n (0, p.2)))) := by
        simp only [cmg]; abel
      rw [e1, Submodule.coe_sub, cmP_coe, cmP_coe, map_neg, map_neg]
      abel
    rw [← Submodule.norm_coe, heq, norm_neg]
    calc _ ≤ C * ‖p.1‖ ^ k := h1
      _ ≤ C * ‖p‖ ^ 2 := by gcongr; exact h2.trans h3
  -- the part depending on `y` only
  have h2 : HasFDerivAt (fun p : E × ↥(SA (ι := ι) (E := E) A) => cmg F A θ₀ n (0, p.2))
      (0 : E × ↥(SA (ι := ι) (E := E) A) →L[ℝ] ↥(SA (ι := ι) (E := E) A)) 0 := by
    let ιY := (SA (ι := ι) (E := E) A).subtypeL
    let Dg := fderiv ℝ (gradient F) θ₀
    have hD : HasFDerivAt (gradient F) Dg (θ₀ + ιY 0) := by
      rw [map_zero, add_zero]
      exact ((gradient_contDiff hF).differentiable (by simp) θ₀).hasFDerivAt
    have haff : HasFDerivAt (fun y => θ₀ + ιY y) ιY 0 := ιY.hasFDerivAt.const_add θ₀
    have e0 : HasFDerivAt (gradient F ∘ fun y => θ₀ + ιY y) (Dg.comp ιY) 0 :=
      hD.comp (0 : ↥(SA (ι := ι) (E := E) A)) haff
    have e1 : HasFDerivAt (fun y => gradient F (θ₀ + ιY y)) (Dg.comp ιY) 0 := e0
    have e2 : HasFDerivAt (fun y => -(gradient F (θ₀ + ιY y))) (-(Dg.comp ιY)) 0 := e1.fun_neg
    have e3 : HasFDerivAt (fun y => cmP (E := E) A (-(gradient F (θ₀ + ιY y))))
        ((cmP A).comp (-(Dg.comp ιY))) 0 :=
      (cmP (E := E) A).hasFDerivAt.comp (0 : ↥(SA (ι := ι) (E := E) A)) e2
    have hφ : HasFDerivAt (fun y => cmP A (-(gradient F (θ₀ + ιY y))) - cmB F A θ₀ y)
        ((cmP A).comp (-(Dg.comp ιY)) - cmB F A θ₀) 0 :=
      e3.fun_sub (cmB F A θ₀).hasFDerivAt
    have hzero : (cmP A).comp (-(Dg.comp ιY)) - cmB F A θ₀ = 0 := by
      ext1 y
      show cmP A (-(Dg (ιY y))) - cmB F A θ₀ y = 0
      rw [sub_eq_zero]
      show cmP A (-(Dg (ιY y))) = -(cmP A (Dg (ιY y)))
      exact map_neg _ _
    rw [hzero] at hφ
    have hφ' : HasFDerivAt (fun y => cmP A (-(gradient F (θ₀ + ιY y))) - cmB F A θ₀ y)
        (0 : ↥(SA (ι := ι) (E := E) A) →L[ℝ] ↥(SA (ι := ι) (E := E) A))
        ((0 : E × ↥(SA (ι := ι) (E := E) A)).2) := hφ
    have e4 := hφ'.comp (0 : E × ↥(SA (ι := ι) (E := E) A)) hasFDerivAt_snd
    rw [ContinuousLinearMap.zero_comp] at e4
    have hfun : (fun p : E × ↥(SA (ι := ι) (E := E) A) => cmg F A θ₀ n (0, p.2)) =
        (fun y => cmP A (-(gradient F (θ₀ + ιY y))) - cmB F A θ₀ y) ∘ Prod.snd := by
      ext1 p
      simp only [Function.comp_apply, cmg, cmx, single_zero, add_zero]
      rfl
    rw [hfun]
    exact e4
  have := h1.fun_add h2
  simp only [sub_add_cancel, add_zero] at this
  exact this.fderiv

private lemma cmB_negdef {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) :
    ∃ c > 0, ∀ y, ⟪cmB F A θ₀ y, y⟫ ≤ -c * ‖y‖ ^ 2 := by
  obtain ⟨c, hc, hpos⟩ := hmin.posdef
  refine ⟨c, hc, fun y => ?_⟩
  rw [Submodule.coe_inner, cmB_coe, inner_neg_left, inner_zeroOut_left,
    proj_eq_self_of_mem_S y.2, inner_fderiv_gradient hF, ← Submodule.norm_coe]
  have := hpos y y.2
  linarith

/-- The centre manifold `a = θ* + h(w_n)` of the gradient flow on `S_{A ∪ {n}}` at `θ*`. -/
private lemma centre_data {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι}
    (hn : n ∉ A) :
    ∃ (hc : E → Θ ι E) (δ : ℝ), 0 < δ ∧ ContDiff ℝ 1 hc ∧ hc 0 = 0 ∧ fderiv ℝ hc 0 = 0 ∧
      (∀ w, hc w ∈ S A) ∧
      ∀ w, ‖w‖ < δ → fderiv ℝ hc w (-(gradient F (θ₀ + hc w + single n w)) n) =
        -proj A (gradient F (θ₀ + hc w + single n w)) := by
  obtain ⟨h, δ, hδ, hh1, hh0, hDh0, htan⟩ := centre_manifold (cmf F A θ₀ n) (cmg F A θ₀ n)
    (cmB F A θ₀) (cmf_contDiff hF A θ₀ n) (cmg_contDiff hF A θ₀ n) (cmf_zero hF hk hH hmin n)
    (cmg_zero hF hk hH hmin n) (cmf_fderiv hF hk hH hmin hn) (cmg_fderiv hF hk hH hmin hn)
    (cmB_negdef hF hk hH hmin)
  set ιY := (SA (ι := ι) (E := E) A).subtypeL
  have hdiff : ∀ w, HasFDerivAt (fun w => ιY (h w)) (ιY.comp (fderiv ℝ h w)) w := fun w =>
    ιY.hasFDerivAt.comp w ((hh1.differentiable (by simp) w).hasFDerivAt)
  refine ⟨fun w => ιY (h w), δ, hδ, ιY.contDiff.comp hh1, by simp [hh0], ?_, fun w => (h w).2, ?_⟩
  · rw [(hdiff 0).fderiv, hDh0]; simp
  · intro w hw
    rw [(hdiff w).fderiv]
    have := htan w hw
    have hfw : cmf F A θ₀ n (w, h w) = -(gradient F (θ₀ + ιY (h w) + single n w)) n := rfl
    rw [hfw] at this
    rw [ContinuousLinearMap.comp_apply, this]
    have e1 : cmB F A θ₀ (h w) + cmg F A θ₀ n (w, h w) =
        cmP A (-(gradient F (cmx A θ₀ n (w, h w)))) := by
      simp only [cmg]; abel
    rw [e1]
    show proj A (-(gradient F (cmx A θ₀ n (w, h w)))) = _
    rw [map_neg]; rfl

/-- Attraction: a backward trajectory near `θ*` in `S_{A ∪ {n}}` lies on the centre manifold. -/
private lemma attract {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι} (hn : n ∉ A)
    {hc : E → Θ ι E} {δ : ℝ} (hδ : 0 < δ) (hhc : ContDiff ℝ 1 hc) (hc0 : hc 0 = 0)
    (hDc0 : fderiv ℝ hc 0 = 0) (hcS : ∀ w, hc w ∈ S A)
    (htan : ∀ w, ‖w‖ < δ → fderiv ℝ hc w (-(gradient F (θ₀ + hc w + single n w)) n) =
        -proj A (gradient F (θ₀ + hc w + single n w))) :
    ∃ ρ₂ > 0, ∃ r₂ > 0, (∀ w : E, ‖w‖ ≤ ρ₂ → ‖hc w‖ ≤ ‖w‖) ∧
      ∀ (u₀ : E) (ρ₁ r : ℝ) (θ : ℝ → Θ ι E) (t' : ℝ), ρ₁ ≤ ρ₂ → r ≤ r₂ →
        BackwardNear F A n θ₀ u₀ ρ₁ r θ t' → ∀ t ≤ t', proj A (θ t) = θ₀ + hc (θ t n) := by
  obtain ⟨μ, rs, hμ, hrs, hmono⟩ := strong_mono hF hmin
  obtain ⟨L, hL⟩ := gf_lipschitzOnWith hF (‖θ₀‖ + rs)
  have hL0 : (0 : ℝ) ≤ L := L.2
  set εh : ℝ := μ / (2 * (L + 1)) with hεh
  have hεh0 : 0 < εh := by positivity
  have hεhL : εh * L ≤ μ / 2 := by
    rw [hεh, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- smallness of `Dh` near `0`
  have hcont : Continuous (fun w => ‖fderiv ℝ hc w‖) :=
    (hhc.continuous_fderiv (by simp)).norm
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) εh hεh0
  -- `‖h(w)‖ ≤ ‖w‖` near `0`
  have hdiff0 : HasFDerivAt hc (0 : E →L[ℝ] Θ ι E) 0 := by
    have := (hhc.differentiable (by simp) 0).hasFDerivAt
    rwa [hDc0] at this
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff0).def one_pos)
  set ρ₂ := min (δ / 2) (min (δ₂ / 2) (min (δ₃ / 2) (rs / 2))) with hρ₂
  have hρ₂0 : 0 < ρ₂ := by positivity
  have hρ₂δ : ρ₂ < δ := by
    have : ρ₂ ≤ δ / 2 := min_le_left _ _
    linarith
  have hρ₂δ₂ : ρ₂ < δ₂ := by
    have : ρ₂ ≤ δ₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hρ₂δ₃ : ρ₂ < δ₃ := by
    have : ρ₂ ≤ δ₃ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hρ₂rs : ρ₂ ≤ rs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : ∀ w : E, ‖w‖ ≤ ρ₂ → ‖hc w‖ ≤ ‖w‖ := by
    intro w hw
    have := hδ₃' (y := w) (by rw [dist_zero_right]; linarith)
    simpa [hc0] using this
  have hDsmall : ∀ w : E, ‖w‖ ≤ ρ₂ → ‖fderiv ℝ hc w‖ ≤ εh := by
    intro w hw
    have := hδ₂' (x := w) (by rw [dist_zero_right]; linarith)
    have hz : ‖fderiv ℝ hc 0‖ = 0 := by rw [hDc0]; exact ContinuousLinearMap.opNorm_zero
    rw [hz, Real.dist_eq, sub_zero] at this
    exact (abs_lt.1 this).2.le
  refine ⟨ρ₂, hρ₂0, rs / 2, by positivity, hsmall, ?_⟩
  intro u₀ ρ₁ r θ t' hρ₁ hr hθ
  obtain ⟨hθd, hθp⟩ := hθ
  -- the deviation from the centre manifold
  set d : ℝ → Θ ι E := fun t => proj A (θ t) - θ₀ - hc (θ t n) with hd
  set d' : ℝ → Θ ι E := fun t =>
    proj A (gf F (θ t)) - fderiv ℝ hc (θ t n) ((gf F (θ t)) n) with hd'
  have hderiv : ∀ t ≤ t', HasDerivWithinAt d (d' t) (Iic t') t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t => proj A (θ t)) (proj A (gf F (θ t))) (Iic t') t :=
      (proj A).hasFDerivAt.comp_hasDerivWithinAt t (hθd t ht)
    have h2 : HasDerivWithinAt (fun t => hc (θ t n))
        (fderiv ℝ hc (θ t n) ((gf F (θ t)) n)) (Iic t') t :=
      (hhc.differentiable (by simp) _).hasFDerivAt.comp_hasDerivWithinAt t
        (hasDerivWithinAt_apply (hθd t ht) n)
    exact (h1.sub_const θ₀).sub h2
  have hineq : ∀ t ≤ t', ⟪d t, d' t⟫ ≤ -(μ / 2) * ‖d t‖ ^ 2 := by
    intro t ht
    obtain ⟨hS, hpos, hρ, hu, ha⟩ := hθp t ht
    obtain ⟨θc, hθc⟩ : ∃ θc, θc = θ₀ + hc (θ t n) + single n (θ t n) := ⟨_, rfl⟩
    have hwρ : ‖θ t n‖ ≤ ρ₂ := hρ.trans hρ₁
    have hdS : d t ∈ S A := S_sub (S_sub (proj_mem_S A _) hmin.mem) (hcS _)
    have hθdec : θ t = proj A (θ t) + single n (θ t n) := eq_proj_add_single hn hS
    have hdiff : θ t - θc = d t := by
      have e : θ t - θc =
          (proj A (θ t) + single n (θ t n)) - (θ₀ + hc (θ t n) + single n (θ t n)) := by
        rw [hθc, ← hθdec]
      rw [e, hd]; beta_reduce; abel
    have hθball : θ t ∈ closedBall θ₀ rs := by
      rw [mem_closedBall, dist_eq_norm]
      have : θ t - θ₀ = (proj A (θ t) - θ₀) + single n (θ t n) := by
        calc θ t - θ₀ = (proj A (θ t) + single n (θ t n)) - θ₀ := by rw [← hθdec]
          _ = _ := by abel
      rw [this]
      calc ‖(proj A (θ t) - θ₀) + single n (θ t n)‖
          ≤ ‖proj A (θ t) - θ₀‖ + ‖(single n (θ t n) : Θ ι E)‖ := norm_add_le _ _
        _ ≤ rs / 2 + rs / 2 := by
            rw [norm_single]; gcongr
            · exact ha.trans hr
            · exact hwρ.trans hρ₂rs
        _ = rs := by ring
    have hθcball : θc ∈ closedBall θ₀ rs := by
      rw [mem_closedBall, dist_eq_norm]
      have : θc - θ₀ = hc (θ t n) + single n (θ t n) := by rw [hθc]; abel
      rw [this]
      calc ‖hc (θ t n) + single n (θ t n)‖
          ≤ ‖hc (θ t n)‖ + ‖(single n (θ t n) : Θ ι E)‖ := norm_add_le _ _
        _ ≤ ρ₂ + ρ₂ := by
            rw [norm_single]; gcongr
            exact (hsmall _ hwρ).trans hwρ
        _ ≤ rs := by linarith
    have hR : ∀ x ∈ closedBall θ₀ rs, x ∈ closedBall (0 : Θ ι E) (‖θ₀‖ + rs) := by
      intro x hx
      rw [mem_closedBall, dist_zero_right]
      rw [mem_closedBall, dist_eq_norm] at hx
      calc ‖x‖ = ‖(x - θ₀) + θ₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - θ₀‖ + ‖θ₀‖ := norm_add_le _ _
        _ ≤ ‖θ₀‖ + rs := by linarith
    -- strong monotonicity
    have hmon := hmono (θ t) θc hθball hθcball (by rw [hdiff]; exact hdS)
    rw [hdiff] at hmon
    -- Lipschitz bound
    have hlip : ‖gradient F (θ t) - gradient F θc‖ ≤ L * ‖d t‖ := by
      have := hL.dist_le_mul (θ t) (hR _ hθball) θc (hR _ hθcball)
      rw [dist_eq_norm, dist_eq_norm, hdiff] at this
      have e : gf F (θ t) - gf F θc = -(gradient F (θ t) - gradient F θc) := by
        simp only [gf]; abel
      rwa [e, norm_neg] at this
    -- tangency
    have htw : fderiv ℝ hc (θ t n) (-(gradient F θc) n) = -proj A (gradient F θc) := by
      rw [hθc]; exact htan _ (lt_of_le_of_lt hwρ hρ₂δ)
    -- the derivative of `d`
    have hd'eq : d' t = -proj A (gradient F (θ t) - gradient F θc) +
        fderiv ℝ hc (θ t n) ((gradient F (θ t) - gradient F θc) n) := by
      have e2 : fderiv ℝ hc (θ t n) ((gradient F (θ t) - gradient F θc) n) =
          fderiv ℝ hc (θ t n) ((gradient F (θ t)) n) +
            fderiv ℝ hc (θ t n) (-(gradient F θc) n) := by
        rw [← map_add]; congr 1; simp [sub_eq_add_neg]
      rw [e2, htw, hd']
      simp only [gf, map_neg, map_sub, PiLp.neg_apply]
      abel
    have hinner1 : ⟪d t, proj A (gradient F (θ t) - gradient F θc)⟫ =
        ⟪d t, gradient F (θ t) - gradient F θc⟫ := inner_proj_eq_of_mem_S hdS _
    have hinner2 : ⟪d t, fderiv ℝ hc (θ t n) ((gradient F (θ t) - gradient F θc) n)⟫ ≤
        ‖d t‖ * (εh * (L * ‖d t‖)) := by
      calc _ ≤ ‖d t‖ * ‖fderiv ℝ hc (θ t n) ((gradient F (θ t) - gradient F θc) n)‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖d t‖ * (‖fderiv ℝ hc (θ t n)‖ * ‖(gradient F (θ t) - gradient F θc) n‖) := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖d t‖ * (εh * (L * ‖d t‖)) := by
            gcongr
            · exact hDsmall _ hwρ
            · exact (norm_apply_le _ n).trans hlip
    rw [hd'eq, inner_add_right, inner_neg_right, hinner1]
    have : ‖d t‖ * (εh * (L * ‖d t‖)) = (εh * L) * ‖d t‖ ^ 2 := by ring
    rw [this] at hinner2
    have hsq : 0 ≤ ‖d t‖ ^ 2 := sq_nonneg _
    nlinarith
  have hbound : ∀ t ≤ t', ‖d t‖ ≤ rs / 2 + ρ₂ := by
    intro t ht
    obtain ⟨hS, hpos, hρ, hu, ha⟩ := hθp t ht
    calc ‖d t‖ = ‖(proj A (θ t) - θ₀) - hc (θ t n)‖ := rfl
      _ ≤ ‖proj A (θ t) - θ₀‖ + ‖hc (θ t n)‖ := norm_sub_le _ _
      _ ≤ rs / 2 + ρ₂ := by
          gcongr
          · exact ha.trans hr
          · exact (hsmall _ (hρ.trans hρ₁)).trans (hρ.trans hρ₁)
  have hzero := eq_zero_of_backward_decay (by positivity : 0 < μ / 2) hderiv hineq hbound
  intro t ht
  have := hzero t ht
  rw [hd] at this
  simp only at this
  rw [sub_sub, sub_eq_zero] at this
  exact this

end EscapeUnique

/-- `(⋆)` and the slaving `|a - θ*| ≤ |w_n|` on the centre manifold. -/
theorem escape_unique {A : Finset ι} {θ₀ : Θ ι E} (hmin : IsNondegMin F A θ₀) {n : ι}
    (hn : n ∉ A) {u₀ : E} (hu : IsNondegMaxSphere (U F k n θ₀) k u₀) (hU : 0 < U F k n θ₀ u₀) :
    ∃ rB > 0, ∃ ρB > 0,
      (∀ (θa θb : ℝ → Θ ι E) (t₁' t₂' : ℝ),
        BackwardNear F A n θ₀ u₀ ρB rB θa t₁' → BackwardNear F A n θ₀ u₀ ρB rB θb t₂' →
        ∃ s₁ ≤ t₁', ∃ s₂ ≤ t₂', θa s₁ = θb s₂) ∧
      (∀ (θ : ℝ → Θ ι E) (t' : ℝ), BackwardNear F A n θ₀ u₀ ρB rB θ t' →
        ∀ t ≤ t', ‖proj A (θ t) - θ₀‖ ≤ ‖θ t n‖) := by
  -- centre manifold `a = θ* + h(w_n)`, and attraction to it
  obtain ⟨hc, δ, hδ, hhc, hc0, hDc0, hcS, htan⟩ := EscapeUnique.centre_data hF hk hH hmin hn
  obtain ⟨ρa, hρa, ra, hra, hsmall, hattr⟩ :=
    EscapeUnique.attract hF hk hH hmin hn hδ hhc hc0 hDc0 hcS htan
  -- blow-up and unstable manifold
  obtain ⟨G, hG, hpolar, hG0, -⟩ := exists_polar hF hk hH n
  obtain ⟨δu, hδu, ψ, hψ⟩ := EscapeUnique.unstable_data hk hG hG0 hhc hc0 hu hU
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlam : 0 < (k : ℝ) * U F k n θ₀ u₀ := mul_pos hk0 hU
  obtain ⟨δ₁, hδ₁, hD⟩ := EscapeUnique.bD_bounds hG hhc hc0 hG0 hlam (euler n θ₀ u₀)
  -- the constants
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, ε₀ = min δu δ₁ / 2 := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; exact half_pos (lt_min hδu hδ₁)
  have hε₀lt : ε₀ < min δu δ₁ := by rw [hε₀]; linarith [lt_min hδu hδ₁]
  obtain ⟨rB, hrB⟩ : ∃ rB, rB = min ra ε₀ := ⟨_, rfl⟩
  obtain ⟨ρB, hρB⟩ : ∃ ρB, ρB = min ρa ε₀ := ⟨_, rfl⟩
  have hrB0 : 0 < rB := by rw [hrB]; exact lt_min hra hε₀0
  have hρB0 : 0 < ρB := by rw [hρB]; exact lt_min hρa hε₀0
  have hrBa : rB ≤ ra := by rw [hrB]; exact min_le_left _ _
  have hρBa : ρB ≤ ρa := by rw [hρB]; exact min_le_left _ _
  have hrBε : rB ≤ ε₀ := by rw [hrB]; exact min_le_right _ _
  have hρBε : ρB ≤ ε₀ := by rw [hρB]; exact min_le_right _ _
  -- the facts for one trajectory
  have key : ∀ (θ : ℝ → Θ ι E) (t' : ℝ), BackwardNear F A n θ₀ u₀ ρB rB θ t' →
      (∀ t ≤ t', proj A (θ t) = θ₀ + hc (θ t n)) ∧
      (∀ t ≤ t', θ t = θ₀ + hc (θ t n) + single n (θ t n)) ∧
      (∀ t ≤ t', ‖θ t n‖⁻¹ • θ t n = ψ ‖θ t n‖) ∧ (∀ ε > 0, ∃ s ≤ t', ‖θ s n‖ ≤ ε) := by
    intro θ t' hθ
    have hatt := hattr u₀ ρB rB θ t' hρBa hrBa hθ
    have hdec : ∀ t ≤ t', θ t = θ₀ + hc (θ t n) + single n (θ t n) := by
      intro t ht
      rw [← hatt t ht]
      exact EscapeUnique.eq_proj_add_single hn (hθ.2 t ht).1
    have hnear : ∀ t ≤ t',
        dist ((‖θ t n‖, ‖θ t n‖⁻¹ • θ t n) : ℝ × E) (0, u₀) < min δu δ₁ := by
      intro t ht
      obtain ⟨-, hpos, hρ, hu', -⟩ := hθ.2 t ht
      rw [Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hpos, dist_eq_norm]
      exact lt_of_le_of_lt (max_le (hρ.trans hρBε) (hu'.trans hrBε)) hε₀lt
    obtain ⟨hcurve, hzero⟩ := EscapeUnique.key_traj hk hn hpolar hcS hmin.mem hψ hlam hD hθ.1 hdec
      (fun t ht => (hθ.2 t ht).2.1) hnear
    exact ⟨hatt, hdec, hcurve, hzero⟩
  refine ⟨rB, hrB0, ρB, hρB0, ?_, ?_⟩
  · intro θa θb t₁' t₂' ha hb
    obtain ⟨-, hdeca, hcurvea, hzeroa⟩ := key θa t₁' ha
    obtain ⟨-, hdecb, hcurveb, hzerob⟩ := key θb t₂' hb
    have hposa : 0 < ‖θa t₁' n‖ := (ha.2 t₁' le_rfl).2.1
    have hposb : 0 < ‖θb t₂' n‖ := (hb.2 t₂' le_rfl).2.1
    obtain ⟨ρc, hρc⟩ : ∃ ρc, ρc = min ‖θa t₁' n‖ ‖θb t₂' n‖ := ⟨_, rfl⟩
    have hρc0 : 0 < ρc := by rw [hρc]; exact lt_min hposa hposb
    -- a time at which `ρ = ρc`, by the intermediate value theorem
    have hivt : ∀ (θ : ℝ → Θ ι E) (t' : ℝ), BackwardNear F A n θ₀ u₀ ρB rB θ t' →
        (∀ ε > 0, ∃ s ≤ t', ‖θ s n‖ ≤ ε) → ρc ≤ ‖θ t' n‖ → ∃ s ≤ t', ‖θ s n‖ = ρc := by
      intro θ t' hθ hzero hle
      obtain ⟨s, hs, hsle⟩ := hzero ρc hρc0
      have hcont : ContinuousOn (fun t => ‖θ t n‖) (Icc s t') := by
        intro t ht
        exact ((EscapeUnique.hasDerivWithinAt_apply (hθ.1 t ht.2) n).continuousWithinAt.norm).mono
          Icc_subset_Iic_self
      obtain ⟨s', hs', heq⟩ := intermediate_value_Icc hs hcont ⟨hsle, hle⟩
      exact ⟨s', hs'.2, heq⟩
    obtain ⟨s₁, hs₁, h₁⟩ := hivt θa t₁' ha hzeroa (by rw [hρc]; exact min_le_left _ _)
    obtain ⟨s₂, hs₂, h₂⟩ := hivt θb t₂' hb hzerob (by rw [hρc]; exact min_le_right _ _)
    refine ⟨s₁, hs₁, s₂, hs₂, ?_⟩
    have hw : θa s₁ n = θb s₂ n := by
      have e1 : θa s₁ n = ρc • ψ ρc := by
        have hne : ‖θa s₁ n‖ ≠ 0 := by rw [h₁]; exact hρc0.ne'
        rw [← h₁, ← hcurvea s₁ hs₁, smul_inv_smul₀ hne]
      have e2 : θb s₂ n = ρc • ψ ρc := by
        have hne : ‖θb s₂ n‖ ≠ 0 := by rw [h₂]; exact hρc0.ne'
        rw [← h₂, ← hcurveb s₂ hs₂, smul_inv_smul₀ hne]
      rw [e1, e2]
    rw [hdeca s₁ hs₁, hdecb s₂ hs₂, hw]
  · intro θ t' hθ t ht
    obtain ⟨hatt, -, -, -⟩ := key θ t' hθ
    rw [hatt t ht, add_sub_cancel_left]
    exact hsmall _ (((hθ.2 t ht).2.2.1).trans hρBa)

end S2S
