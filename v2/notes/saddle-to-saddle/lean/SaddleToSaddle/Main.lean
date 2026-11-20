import SaddleToSaddle.Stages

/-!
# Theorem A

Let `F ∈ C^∞((ℝ^p)^N)` satisfy `(H)` with `k ≥ 3` (e.g. the loss of a deep polynomial ResNet),
let `ξ ∈ Θ`, and let `θ^α` be the (maximal) gradient flow `θ̇ = -∇F(θ)` with `θ^α(0) = α ξ`.
Assume that stages `0, …, M-1` of the saddle-to-saddle process are non-degenerate, and let
`S ∈ (s_M, s_{M+1})`. Then, for `α` small, `θ^α` is defined on `[0, α^{2-k} S]`, and as `α → 0`,
in the time `s = α^{k-2} t`:

* (i) plateaus: `θ^α(α^{2-k} s) → θ̄(s)` uniformly away from the jump times, the loss converges
  to the step function `F(θ̄(s))`, and `F(θ^{(0)}) > ⋯ > F(θ^{(M)})`;
* (ii) dormant neurons: `α^{-1} w_n^α(α^{2-k} s) → Ξ_n(s)` uniformly on `[0, min(S, s̄_n - δ)]`;
* (iii) jumps: there are times `t_m^α` with `α^{k-2} t_m^α → s_m` such that
  `θ^α(t_m^α + ·)` converges to a time translate of `γ_m` locally uniformly, and the curve
  `{θ^α(α^{2-k} s) : |s - s_m| ≤ δ}` converges in Hausdorff distance to the closure of `γ_m(ℝ)`.

Each `θ^{(m)}` is a critical point of `F`, and a saddle point for `m < M`.

In (ii), `s̄_n = s_m` if `n = n_m`, and `s̄_n > S` if `n ∉ A_M`, so the statement is split
accordingly.
-/

open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open Set Filter Metric

noncomputable section

set_option linter.unusedSectionVars false

namespace S2S

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


/-! ### Auxiliary lemmas: time conversion and limits

Throughout, `(α ^ (k - 2))⁻¹ = α^{2-k}` is the slow time scale: the time `t = α^{2-k} σ`
corresponds to the slow time `σ = α^{k-2} t`. -/

section Aux

private lemma tA_rescale_inv {k : ℕ} {α : ℝ} (hα : 0 < α) (σ : ℝ) :
    α ^ (k - 2) * ((α ^ (k - 2))⁻¹ * σ) = σ := by
  rw [← mul_assoc, mul_inv_cancel₀ (pow_pos hα _).ne', one_mul]

private lemma tA_inv_rescale {k : ℕ} {α : ℝ} (hα : 0 < α) (t : ℝ) :
    (α ^ (k - 2))⁻¹ * (α ^ (k - 2) * t) = t := by
  rw [← mul_assoc, inv_mul_cancel₀ (pow_pos hα _).ne', one_mul]

private lemma tA_le_shift_iff {k : ℕ} {α x y τ : ℝ} (hα : 0 < α) :
    (α ^ (k - 2))⁻¹ * x ≤ τ + (α ^ (k - 2))⁻¹ * y ↔ x ≤ α ^ (k - 2) * τ + y := by
  rw [← mul_le_mul_iff_of_pos_left (pow_pos hα (k - 2)), mul_add, tA_rescale_inv hα,
    tA_rescale_inv hα]

private lemma tA_shift_le_iff {k : ℕ} {α x y τ : ℝ} (hα : 0 < α) :
    τ + (α ^ (k - 2))⁻¹ * y ≤ (α ^ (k - 2))⁻¹ * x ↔ α ^ (k - 2) * τ + y ≤ x := by
  rw [← mul_le_mul_iff_of_pos_left (pow_pos hα (k - 2)), mul_add, tA_rescale_inv hα,
    tA_rescale_inv hα]

/-- If `α^{k-2} τ_α → s₀` and `x < s₀ + y`, then eventually `α^{2-k} x' ≤ τ_α + α^{2-k} y` for
all `x' ≤ x`. -/
private lemma tA_ev_le_shift {k : ℕ} {τ : ℝ → ℝ} {s₀ x y : ℝ}
    (h : Tendsto (fun α => α ^ (k - 2) * τ α) (𝓝[>] 0) (𝓝 s₀)) (hxy : x < s₀ + y) :
    ∀ᶠ α in 𝓝[>] 0, ∀ x' ≤ x, (α ^ (k - 2))⁻¹ * x' ≤ τ α + (α ^ (k - 2))⁻¹ * y := by
  filter_upwards [h.eventually_const_lt (show x - y < s₀ by linarith), self_mem_nhdsWithin]
    with α h1 hα x' hx'
  rw [tA_le_shift_iff hα]
  linarith

/-- If `α^{k-2} τ_α → s₀` and `s₀ + y < x`, then eventually `τ_α + α^{2-k} y ≤ α^{2-k} x'` for
all `x' ≥ x`. -/
private lemma tA_ev_shift_le {k : ℕ} {τ : ℝ → ℝ} {s₀ x y : ℝ}
    (h : Tendsto (fun α => α ^ (k - 2) * τ α) (𝓝[>] 0) (𝓝 s₀)) (hxy : s₀ + y < x) :
    ∀ᶠ α in 𝓝[>] 0, ∀ x' ≥ x, τ α + (α ^ (k - 2))⁻¹ * y ≤ (α ^ (k - 2))⁻¹ * x' := by
  filter_upwards [h.eventually_lt_const (show s₀ < x - y by linarith), self_mem_nhdsWithin]
    with α h1 hα x' hx'
  rw [tA_shift_le_iff hα]
  linarith

private lemma tA_tendsto_pow {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun α : ℝ => α ^ (k - 2)) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun α : ℝ => α ^ (k - 2)) (𝓝 0) (𝓝 (0 ^ (k - 2))) :=
    (continuous_pow _).tendsto 0
  rw [zero_pow (by omega)] at this
  exact this.mono_left nhdsWithin_le_nhds

private lemma tA_tendsto_inv_pow {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun α : ℝ => (α ^ (k - 2))⁻¹) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun α : ℝ => α ^ (k - 2)) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tA_tendsto_pow hk, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact pow_pos (show (0 : ℝ) < α from hα) _
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- `e^{-μ α^{2-k} d} r + K α → 0` as `α → 0⁺`. -/
private lemma tA_ev_small {k : ℕ} (hk : 3 ≤ k) {μ d r K ε : ℝ} (hμ : 0 < μ) (hd : 0 < d)
    (hε : 0 < ε) :
    ∀ᶠ α in 𝓝[>] (0 : ℝ), Real.exp (-μ * ((α ^ (k - 2))⁻¹ * d)) * r + K * α < ε := by
  have h1 : Tendsto (fun α : ℝ => -μ * ((α ^ (k - 2))⁻¹ * d)) (𝓝[>] 0) atBot :=
    ((tA_tendsto_inv_pow hk).atTop_mul_const hd).const_mul_atTop_of_neg (neg_lt_zero.mpr hμ)
  have h2 : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun α : ℝ => Real.exp (-μ * ((α ^ (k - 2))⁻¹ * d)) * r + K * α) (𝓝[>] 0)
      (𝓝 (0 * r + K * 0)) :=
    ((Real.tendsto_exp_atBot.comp h1).mul_const r).add (h2.const_mul K)
  rw [zero_mul, mul_zero, add_zero] at h3
  exact h3.eventually_lt_const hε

private lemma tA_ev_lin {K ε : ℝ} (hε : 0 < ε) : ∀ᶠ α in 𝓝[>] (0 : ℝ), K * α < ε := by
  have h : Tendsto (fun α : ℝ => K * α) (𝓝[>] 0) (𝓝 (K * 0)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).const_mul K
  rw [mul_zero] at h
  exact h.eventually_lt_const hε

/-! ### Norms -/

private lemma tA_norm_le_card_mul {x : Θ ι E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, ‖x i‖ ≤ b) :
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

/-- `‖x - π_A x‖ ≤ N c` if all the components of `x` outside `A` have norm `≤ c`. -/
private lemma tA_norm_sub_proj_le {A : Finset ι} {x : Θ ι E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∉ A, ‖x i‖ ≤ c) : ‖x - proj A x‖ ≤ Fintype.card ι * c := by
  refine tA_norm_le_card_mul hc fun m => ?_
  by_cases hm : m ∈ A
  · simp [hm, hc]
  · simpa [proj_apply, hm] using h m hm

/-! ### Bookkeeping for the process -/

variable {F : Θ ι E → ℝ} {k : ℕ} {ξ : Θ ι E} {M : ℕ} {S : ℝ}

/-- Every `σ ≥ 0` lies in some stage `m ≤ M`: `s_m ≤ σ`, and `σ < s_{m+1}` if `m < M`. -/
private lemma tA_exists_stage (P : Process F k ξ M S) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ m ≤ M, P.s m ≤ σ ∧ (m < M → σ < P.s (m + 1)) := by
  classical
  have hex : ∃ m, m = M ∨ σ < P.s (m + 1) := ⟨M, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, P.s_zero]; exact hσ
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
      simp only [not_or, not_lt] at hmin
      rw [hj]; exact hmin.2
  · intro hlt
    rcases Nat.find_spec hex with h | h
    · omega
    · exact h

/-- A horizon `σ₁` for the plateau of stage `m`, and a bound `b < σ₁` for the slow times of
stage `m` that stay `δ`-away from the next jump time (or `≤ S` at the last stage). -/
private lemma tA_exists_horizon (P : Process F k ξ M S) {m : ℕ} (hm : m ≤ M) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ σ₁ b, P.s m < σ₁ ∧ ((m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ < P.S')) ∧ b < σ₁ ∧
      ∀ σ, σ ≤ S → (m < M → σ ≤ P.s (m + 1) - δ) → σ ≤ b := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · have h1 : P.s m < P.s (m + 1) := P.s_lt m hlt
    refine ⟨max (P.s (m + 1) - δ / 2) ((P.s m + P.s (m + 1)) / 2), P.s (m + 1) - δ, ?_,
      ⟨fun _ => ?_, fun h => absurd h hlt.ne⟩, ?_, fun σ _ h => h hlt⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact max_lt (by linarith) (by linarith)
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · have h1 : P.s m < S := by rw [heq]; exact P.s_lt_S
    have h2 := P.S_lt_S'
    refine ⟨(S + P.S') / 2, S, by linarith, ⟨fun h => absurd heq h.ne, fun _ => by linarith⟩,
      by linarith, fun σ hσ _ => hσ⟩


/-- The Hausdorff estimate for a fixed `α`. The curve `φ(λσ)`, `σ ∈ [a, b]`, is split into four
parts: near `p = θ^{(m-1)}` (up to `t₀'`), shadowing the escape orbit `γ` on `[t₀, t₁]`, close to
`γ(· + c)` on `[t₁, t₁ + T]`, and near `q = θ^{(m)}` afterwards. Conversely, every point of
`closure (γ ℝ)` is close to `γ(u + c)` for some `u`, and the tails of `γ` are close to `p`
and `q`. -/
private lemma tA_hausdorff_core {φ γ : ℝ → Θ ι E} {p q : Θ ι E}
    {lam a b t₀ t₀' t₁ c T T' T'' η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hp : p ∈ closure (range γ)) (hq : q ∈ closure (range γ))
    (hTT : T ≤ T'') (hT'T : T' ≤ T'') (hT0 : 0 ≤ T) (ht₀ : t₀ ≤ t₀')
    (h_early : ∀ t ∈ Icc (lam * a) t₀', ‖φ t - p‖ < η)
    (h_jump : ∀ t ∈ Icc t₀ t₁, ∃ s : ℝ, ‖φ t - γ (s + c)‖ < η)
    (h_loc : ∀ u ∈ Icc (-T'') T'', dist (γ (u + c)) (φ (t₁ + u)) < η)
    (h_late : ∀ t ∈ Icc (t₁ + T) (lam * b), ‖φ t - q‖ < 3 * η)
    (h_top : ∀ u ≥ T, dist (γ (u + c)) q < η)
    (h_bot : ∀ u ≤ -T', dist (γ (u + c)) p < η)
    (h_in : ∀ u ∈ Icc (-T'') T'', ∃ σ ∈ Icc a b, lam * σ = t₁ + u)
    (h_a : lam * a ≤ t₀') (h_b : t₁ + T ≤ lam * b) (hab : a ≤ b) :
    hausdorffDist ((fun σ => φ (lam * σ)) '' Icc a b) (closure (range γ)) ≤ 5 * η := by
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · rintro x ⟨σ, hσ, rfl⟩
    have ht1 : lam * a ≤ lam * σ := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    have ht2 : lam * σ ≤ lam * b := mul_le_mul_of_nonneg_left hσ.2 hlam.le
    show ∃ y ∈ closure (range γ), dist (φ (lam * σ)) y ≤ 5 * η
    rcases le_or_gt (lam * σ) t₀' with h1 | h1
    · exact ⟨p, hp, by rw [dist_eq_norm]; linarith [h_early _ ⟨ht1, h1⟩]⟩
    rcases le_or_gt (lam * σ) t₁ with h2 | h2
    · obtain ⟨s, hs⟩ := h_jump _ ⟨by linarith, h2⟩
      exact ⟨γ (s + c), subset_closure (mem_range_self _), by rw [dist_eq_norm]; linarith⟩
    rcases le_or_gt (lam * σ) (t₁ + T) with h3 | h3
    · have hu : lam * σ - t₁ ∈ Icc (-T'') T'' := ⟨by linarith, by linarith⟩
      have h4 := h_loc _ hu
      have e : t₁ + (lam * σ - t₁) = lam * σ := by ring
      rw [e, dist_comm] at h4
      exact ⟨γ (lam * σ - t₁ + c), subset_closure (mem_range_self _), by linarith⟩
    · exact ⟨q, hq, by rw [dist_eq_norm]; linarith [h_late _ ⟨h3.le, ht2⟩]⟩
  · intro y hy
    obtain ⟨z, ⟨u₀, rfl⟩, hz⟩ := Metric.mem_closure_iff.mp hy η hη
    have hu₀ : γ u₀ = γ (u₀ - c + c) := by rw [sub_add_cancel]
    rcases lt_or_ge (u₀ - c) (-T') with h1 | h1
    · refine ⟨φ (lam * a), ⟨a, ⟨le_rfl, hab⟩, rfl⟩, ?_⟩
      have e1 := h_early _ ⟨le_rfl, h_a⟩
      have e2 := h_bot _ h1.le
      rw [← hu₀] at e2
      rw [← dist_eq_norm, dist_comm] at e1
      linarith [dist_triangle4 y (γ u₀) p (φ (lam * a))]
    rcases le_or_gt (u₀ - c) T with h2 | h2
    · have hu : u₀ - c ∈ Icc (-T'') T'' := ⟨by linarith, by linarith⟩
      obtain ⟨σ, hσ, hσeq⟩ := h_in _ hu
      refine ⟨φ (t₁ + (u₀ - c)), ⟨σ, hσ, ?_⟩, ?_⟩
      · show φ (lam * σ) = φ (t₁ + (u₀ - c))
        rw [hσeq]
      have e1 := h_loc _ hu
      rw [← hu₀] at e1
      linarith [dist_triangle y (γ u₀) (φ (t₁ + (u₀ - c)))]
    · refine ⟨φ (lam * b), ⟨b, ⟨hab, le_rfl⟩, rfl⟩, ?_⟩
      have e1 := h_late _ ⟨h_b, le_rfl⟩
      have e2 := h_top _ h2.le
      rw [← hu₀] at e2
      rw [← dist_eq_norm, dist_comm] at e1
      linarith [dist_triangle4 y (γ u₀) q (φ (lam * b))]

end Aux

/-! ### The stages -/

section Stages

variable {F : Θ ι E → ℝ} {k : ℕ} {ξ : Θ ι E} {M : ℕ} {S : ℝ}
variable (hF : ContDiff ℝ ∞ F) (hk : 3 ≤ k) (hH : Flat F k)
  (P : Process F k ξ M S) (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ)
  (hθ : ∀ α > 0, IsMaxFwd (gf F) (θ α) (D α) ∧ θ α 0 = α • ξ)
include hF hk hH P hθ

/-- The inductive claim `(C_m)` holds at every stage `m ≤ M`, with `r₀` from Lemma 2. -/
private lemma tA_claims :
    ∀ m ≤ M, ∃ r₀ μ τ, PlateauProp F k (P.A m) (P.θs m) r₀ μ ∧ Claim P θ D m r₀ τ := by
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨r₀, μ, hpl⟩ := plateau hF hk hH (P.isMin 0 (Nat.zero_le _))
    exact ⟨r₀, μ, fun _ => 0, hpl, claim_zero hF hk hH P θ D hθ hpl.1⟩
  | succ m ih =>
    intro hm
    obtain ⟨r₀, μ, τ, hpl, hC⟩ := ih (by omega)
    obtain ⟨r₀', μ', hpl'⟩ := plateau hF hk hH (P.isMin (m + 1) hm)
    obtain ⟨t₁, c, -, -, -, ⟨T₀, hT₀⟩, -⟩ :=
      stage_jump hF hk hH P θ D hθ (by omega) hpl hC hpl'
    exact ⟨r₀', μ', _, hpl', hT₀ T₀ le_rfl⟩

/-- Closeness to the plateau during stage `m`: the active coordinates relax exponentially, and
the inactive ones are `O(α)`. -/
private lemma tA_close {m : ℕ} (hm : m ≤ M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {σ₁ : ℝ} (hσ : P.s m < σ₁) (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ < P.S')) :
    ∃ K, 0 ≤ K ∧ ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc (τ α) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
      ‖θ α t - P.θs m‖ ≤
        Real.exp (-μ * (t - τ α)) * ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ + K * α := by
  obtain ⟨-, -, ⟨K, hK⟩, ⟨R, hR⟩⟩ := stage_plateau hF hk hH P θ D hθ hm hpl hC hσ hσ₁
  refine ⟨|K| + Fintype.card ι * |R|, by positivity, ?_⟩
  filter_upwards [hK, hR, Ioo_mem_nhdsGT one_pos] with α hKα hRα hα t ht
  obtain ⟨hα0, hα1⟩ := hα
  have h1 := hKα t ht
  have h2 : ‖θ α t - proj (P.A m) (θ α t)‖ ≤ Fintype.card ι * (α * |R|) :=
    tA_norm_sub_proj_le (by positivity) fun i hi =>
      (hRα t ht i hi).trans (mul_le_mul_of_nonneg_left (le_abs_self R) hα0.le)
  have h3 : K * α ^ k ≤ |K| * α := by
    have : α ^ k ≤ α := by
      calc α ^ k ≤ α ^ 1 := pow_le_pow_of_le_one hα0.le hα1.le (by omega)
        _ = α := pow_one α
    calc K * α ^ k ≤ |K| * α ^ k := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * α := mul_le_mul_of_nonneg_left this (abs_nonneg K)
  have h4 : ‖θ α t - P.θs m‖ ≤
      ‖proj (P.A m) (θ α t) - P.θs m‖ + ‖θ α t - proj (P.A m) (θ α t)‖ := by
    calc ‖θ α t - P.θs m‖
        = ‖(proj (P.A m) (θ α t) - P.θs m) + (θ α t - proj (P.A m) (θ α t))‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h5 : (|K| + Fintype.card ι * |R|) * α = |K| * α + Fintype.card ι * (α * |R|) := by ring
  linarith

/-- After a delay `α^{2-k}(a - s_m)`, the trajectory is uniformly close to `θ^{(m)}` until the
end of the plateau. -/
private lemma tA_close_t {m : ℕ} (hm : m ≤ M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {σ₁ : ℝ} (hσ : P.s m < σ₁) (hσ₁ : (m < M → σ₁ < P.s (m + 1)) ∧ (m = M → σ₁ < P.S'))
    {a : ℝ} (ha : P.s m < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ α in 𝓝[>] 0, ∀ t ∈ Icc ((α ^ (k - 2))⁻¹ * a) (τ α + (α ^ (k - 2))⁻¹ * (σ₁ - P.s m)),
      ‖θ α t - P.θs m‖ < ε := by
  obtain ⟨K, -, hK⟩ := tA_close hF hk hH P θ D hθ hm hpl hC hσ hσ₁
  obtain ⟨-, hμ, -⟩ := hpl
  have hd0 : 0 < (a - P.s m) / 2 := by linarith
  filter_upwards [hK, hC.near, tA_ev_shift_le hC.time (x := a) (y := (a - P.s m) / 2)
    (by linarith), tA_ev_small hk hμ hd0 hε (r := r₀) (K := K), self_mem_nhdsWithin]
    with α hKα hnear hsh hsmall hα t ht
  have hα0 : (0 : ℝ) < α := hα
  have hsc : 0 ≤ (α ^ (k - 2))⁻¹ * ((a - P.s m) / 2) := by
    have := pow_pos hα0 (k - 2)
    positivity
  have htτ : τ α + (α ^ (k - 2))⁻¹ * ((a - P.s m) / 2) ≤ t := (hsh a le_rfl).trans ht.1
  have h1 := hKα t ⟨by linarith, ht.2⟩
  have h2 : Real.exp (-μ * (t - τ α)) ≤ Real.exp (-μ * ((α ^ (k - 2))⁻¹ * ((a - P.s m) / 2))) := by
    apply Real.exp_le_exp.mpr
    have h3 : (α ^ (k - 2))⁻¹ * ((a - P.s m) / 2) ≤ t - τ α := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hμ.le
    linarith
  have h5 : Real.exp (-μ * (t - τ α)) * ‖proj (P.A m) (θ α (τ α)) - P.θs m‖ ≤
      Real.exp (-μ * ((α ^ (k - 2))⁻¹ * ((a - P.s m) / 2))) * r₀ :=
    mul_le_mul h2 hnear (norm_nonneg _) (Real.exp_pos _).le
  linarith


/-- (i) at stage `m`: `θ^α(α^{2-k} σ) → θ^{(m)}` uniformly for `σ ∈ [s_m + δ, s_{m+1} - δ]` (or
`[s_M + δ, S]` at the last stage), and from `σ = 0` at stage `0`. -/
private lemma tA_plateau_stage {m : ℕ} (hm : m ≤ M) {r₀ μ : ℝ}
    (hpl : PlateauProp F k (P.A m) (P.θs m) r₀ μ) {τ : ℝ → ℝ} (hC : Claim P θ D m r₀ τ)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ α in 𝓝[>] 0, ∀ σ ∈ Icc 0 S, (1 ≤ m → P.s m + δ ≤ σ) → (m < M → σ ≤ P.s (m + 1) - δ) →
      ‖θ α ((α ^ (k - 2))⁻¹ * σ) - P.θs m‖ < ε := by
  obtain ⟨σ₁, b, hσ, hσ₁, hb, hbσ⟩ := tA_exists_horizon P hm hδ
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- stage `0`: use `claim_zero` (`τ = 0`), where the active part vanishes initially
    have hC0 := claim_zero hF hk hH P θ D hθ hpl.1
    obtain ⟨K, -, hK⟩ := tA_close hF hk hH P θ D hθ hm hpl hC0 hσ hσ₁
    filter_upwards [hK, tA_ev_lin (K := K) hε, self_mem_nhdsWithin] with α hKα hlin hα σ hσS _ hσb
    have hα0 : (0 : ℝ) < α := hα
    have hc : 0 < (α ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos hα0 _)
    have hσb' : σ ≤ b := hbσ σ hσS.2 hσb
    have ht : (α ^ (k - 2))⁻¹ * σ ∈ Icc (0 : ℝ) (0 + (α ^ (k - 2))⁻¹ * (σ₁ - P.s 0)) := by
      rw [P.s_zero, sub_zero, zero_add]
      exact ⟨mul_nonneg hc.le hσS.1, mul_le_mul_of_nonneg_left (by linarith) hc.le⟩
    have h1 := hKα _ ht
    have h0 : proj (P.A 0) (θ α 0) - P.θs 0 = 0 := by
      have : proj (P.A 0) (θ α 0) = 0 := by rw [P.A_zero]; ext i; simp
      rw [this, P.θs_zero, sub_zero]
    rw [h0, norm_zero, mul_zero, zero_add] at h1
    linarith
  · -- stage `m ≥ 1`: exponential relaxation after the delay `α^{2-k} δ/2`
    have h := tA_close_t hF hk hH P θ D hθ hm hpl hC hσ hσ₁ (a := P.s m + δ / 2) (by linarith) hε
    filter_upwards [h, tA_ev_le_shift hC.time (x := b) (y := σ₁ - P.s m) (by linarith),
      self_mem_nhdsWithin] with α h1 h2 hα σ hσS hσa hσb
    have hα0 : (0 : ℝ) < α := hα
    have hc : 0 < (α ^ (k - 2))⁻¹ := inv_pos.mpr (pow_pos hα0 _)
    have hσa' := hσa hm1
    exact h1 _ ⟨mul_le_mul_of_nonneg_left (by linarith) hc.le, h2 σ (hbσ σ hσS.2 hσb)⟩

/-- Part (i) of Theorem A. -/
private lemma tA_part_i {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun α σ => θ α ((α ^ (k - 2))⁻¹ * σ)) P.limitPath (𝓝[>] 0)
      (Icc 0 S \ ⋃ m ∈ Finset.Icc 1 M, Ioo (P.s m - δ) (P.s m + δ)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hall : ∀ m ∈ Finset.range (M + 1), ∀ᶠ α in 𝓝[>] 0, ∀ σ ∈ Icc 0 S,
      (1 ≤ m → P.s m + δ ≤ σ) → (m < M → σ ≤ P.s (m + 1) - δ) →
      ‖θ α ((α ^ (k - 2))⁻¹ * σ) - P.θs m‖ < ε := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ m hmM
    exact tA_plateau_stage hF hk hH P θ D hθ hmM hpl hC hδ hε
  filter_upwards [(Filter.eventually_all_finset _).mpr hall] with α hα σ hσ
  obtain ⟨hσS, hσU⟩ := hσ
  obtain ⟨m, hmM, hsm, hsm1⟩ := tA_exists_stage P hσS.1
  rw [P.limitPath_eq hmM hsm hsm1, dist_comm, dist_eq_norm]
  refine hα m (Finset.mem_range.mpr (Nat.lt_succ_of_le hmM)) σ hσS ?_ ?_
  · intro h1
    by_contra hlt
    rw [not_le] at hlt
    exact hσU (mem_iUnion₂.mpr ⟨m, Finset.mem_Icc.mpr ⟨h1, hmM⟩, by linarith, hlt⟩)
  · intro h1
    by_contra hlt
    rw [not_le] at hlt
    exact hσU (mem_iUnion₂.mpr
      ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, h1⟩, hlt, by linarith [hsm1 h1]⟩)

/-- The loss converges, by (i) and the uniform continuity of `F` on a closed ball. -/
private lemma tA_part_loss {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun α σ => F (θ α ((α ^ (k - 2))⁻¹ * σ)))
      (fun σ => F (P.limitPath σ)) (𝓝[>] 0)
      (Icc 0 S \ ⋃ m ∈ Finset.Icc 1 M, Ioo (P.s m - δ) (P.s m + δ)) := by
  have hi := Metric.tendstoUniformlyOn_iff.mp (tA_part_i hF hk hH P θ D hθ hδ)
  set R : ℝ := ∑ m ∈ Finset.range (M + 1), ‖P.θs m‖ + 1 with hR
  have hlp : ∀ σ, ‖P.limitPath σ‖ ≤ R - 1 := by
    intro σ
    have hcard : ((Finset.Icc 1 M).filter (fun j => P.s j ≤ σ)).card ≤ M := by
      calc _ ≤ (Finset.Icc 1 M).card := Finset.card_filter_le _ _
        _ = M := by simp
    show ‖P.θs _‖ ≤ R - 1
    rw [hR, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun m => ‖P.θs m‖) (fun m _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have huc := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : Θ ι E) R).uniformContinuousOn_of_continuous
      hF.continuous.continuousOn)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηuc⟩ := huc ε hε
  filter_upwards [hi (min η 1) (lt_min hη one_pos)] with α hα σ hσ
  have h1 := hα σ hσ
  have h2 : P.limitPath σ ∈ closedBall (0 : Θ ι E) R := by
    rw [mem_closedBall_zero_iff]; linarith [hlp σ]
  have h3 : θ α ((α ^ (k - 2))⁻¹ * σ) ∈ closedBall (0 : Θ ι E) R := by
    rw [mem_closedBall_zero_iff]
    have h4 := dist_triangle (θ α ((α ^ (k - 2))⁻¹ * σ)) (P.limitPath σ) 0
    rw [dist_zero_right, dist_zero_right, dist_comm] at h4
    linarith [hlp σ, min_le_right η 1]
  exact hηuc _ h2 _ h3 (lt_of_lt_of_le h1 (min_le_left _ _))

/-- Existence of `θ^α` on `[0, α^{2-k} S]`. -/
private lemma tA_exists : ∀ᶠ α in 𝓝[>] 0, Icc 0 ((α ^ (k - 2))⁻¹ * S) ⊆ D α := by
  obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ M le_rfl
  have h1 := P.s_lt_S
  have h2 := P.S_lt_S'
  obtain ⟨hD, -, -, -⟩ := stage_plateau hF hk hH P θ D hθ le_rfl hpl hC
    (σ₁ := (S + P.S') / 2) (by linarith) ⟨fun h => absurd h (lt_irrefl _), fun _ => by linarith⟩
  filter_upwards [hD, tA_ev_le_shift hC.time (x := S) (y := (S + P.S') / 2 - P.s M)
    (by linarith)] with α h3 h4
  exact (Icc_subset_Icc le_rfl (h4 S le_rfl)).trans h3

/-- Part (ii) of Theorem A for the neurons that are still dormant at the last stage. -/
private lemma tA_part_ii_a {i : ι} (hi : i ∉ P.A M) :
    TendstoUniformlyOn (fun α σ => α⁻¹ • θ α ((α ^ (k - 2))⁻¹ * σ) i) (P.Ξ i) (𝓝[>] 0)
      (Icc 0 S) := by
  obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ M le_rfl
  have h1 := P.s_lt_S
  have h2 := P.S_lt_S'
  obtain ⟨-, hb, -, -⟩ := stage_plateau hF hk hH P θ D hθ le_rfl hpl hC
    (σ₁ := (S + P.S') / 2) (by linarith) ⟨fun h => absurd h (lt_irrefl _), fun _ => by linarith⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb i hi (ε / 2) (by positivity),
    tA_ev_le_shift hC.time (x := S) (y := (S + P.S') / 2 - P.s M) (by linarith),
    self_mem_nhdsWithin] with α h3 h4 hα σ hσ
  have hα0 : (0 : ℝ) < α := hα
  have h5 := h3 ((α ^ (k - 2))⁻¹ * σ)
    ⟨mul_nonneg (inv_nonneg.mpr (pow_pos hα0 _).le) hσ.1, h4 σ hσ.2⟩
  rw [tA_rescale_inv hα0] at h5
  rw [dist_comm, dist_eq_norm]
  linarith

/-- Part (ii) of Theorem A for the neuron `n_{j+1}`, up to its activation time `s_{j+1}`. -/
private lemma tA_part_ii_b {j : ℕ} (hj : j < M) {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun α σ => α⁻¹ • θ α ((α ^ (k - 2))⁻¹ * σ) (P.n (j + 1)))
      (P.Ξ (P.n (j + 1))) (𝓝[>] 0) (Icc 0 (P.s (j + 1) - δ)) := by
  obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ j hj.le
  have h1 : P.s j < P.s (j + 1) := P.s_lt j hj
  obtain ⟨σ₁, hσ, hσ₁, hσb⟩ : ∃ σ₁, P.s j < σ₁ ∧
      ((j < M → σ₁ < P.s (j + 1)) ∧ (j = M → σ₁ < P.S')) ∧ P.s (j + 1) - δ < σ₁ :=
    ⟨max (P.s (j + 1) - δ / 2) ((P.s j + P.s (j + 1)) / 2),
      lt_of_lt_of_le (by linarith) (le_max_right _ _),
      ⟨fun _ => max_lt (by linarith) (by linarith), fun h => absurd h hj.ne⟩,
      lt_of_lt_of_le (by linarith) (le_max_left _ _)⟩
  have hni : P.n (j + 1) ∉ P.A j := P.n_notMem_A (by omega) (by omega)
  obtain ⟨-, hb, -, -⟩ := stage_plateau hF hk hH P θ D hθ hj.le hpl hC hσ hσ₁
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb _ hni (ε / 2) (by positivity),
    tA_ev_le_shift hC.time (x := P.s (j + 1) - δ) (y := σ₁ - P.s j) (by linarith),
    self_mem_nhdsWithin] with α h3 h4 hα σ hσ
  have hα0 : (0 : ℝ) < α := hα
  have h5 := h3 ((α ^ (k - 2))⁻¹ * σ)
    ⟨mul_nonneg (inv_nonneg.mpr (pow_pos hα0 _).le) hσ.1, h4 σ hσ.2⟩
  rw [tA_rescale_inv hα0] at h5
  rw [dist_comm, dist_eq_norm]
  linarith

/-- Part (iii) of Theorem A: the jump times and the local uniform convergence. -/
private lemma tA_part_iii {j : ℕ} (hj : j < M) :
    ∃ tm : ℝ → ℝ, Tendsto (fun α => α ^ (k - 2) * tm α) (𝓝[>] 0) (𝓝 (P.s (j + 1))) ∧
      ∃ c : ℝ, ∀ T > 0, TendstoUniformlyOn (fun α t => θ α (tm α + t))
        (fun t => P.γ (j + 1) (t + c)) (𝓝[>] 0) (Icc (-T) T) := by
  obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ j hj.le
  obtain ⟨r₀', μ', hpl'⟩ := plateau hF hk hH (P.isMin (j + 1) hj)
  obtain ⟨t₁, c, h1, -, h3, -, -⟩ := stage_jump hF hk hH P θ D hθ hj hpl hC hpl'
  exact ⟨t₁, h1, c, h3⟩


/-- The Hausdorff convergence in part (iii) of Theorem A, at the jump `s_{j+1}`. -/
private lemma tA_part_hausdorff {j : ℕ} (hj : j < M) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ m < M, 2 * δ < P.s (m + 1) - P.s m) (hgapS : 2 * δ < S - P.s M) :
    Tendsto (fun α => hausdorffDist
      ((fun σ => θ α ((α ^ (k - 2))⁻¹ * σ)) '' Icc (P.s (j + 1) - δ) (P.s (j + 1) + δ))
      (closure (range (P.γ (j + 1))))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨r₀, μ, τ, hpl, hC⟩ := tA_claims hF hk hH P θ D hθ j hj.le
  obtain ⟨r₀', μ', hpl'⟩ := plateau hF hk hH (P.isMin (j + 1) hj)
  obtain ⟨t₁, c, hJ1, -, hJ3, ⟨T₀, hT₀⟩, ⟨δ₀, hδ₀, hJ5⟩⟩ :=
    stage_jump hF hk hH P θ D hθ hj hpl hC hpl'
  have hgj : 2 * δ < P.s (j + 1) - P.s j := hgap j hj
  have hσm₁ : (j + 1 < M → P.s (j + 1) + 3 * δ / 2 < P.s (j + 1 + 1)) ∧
      (j + 1 = M → P.s (j + 1) + 3 * δ / 2 < P.S') := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hgap (j + 1) h; linarith
    · have e : P.s M = P.s (j + 1) := by rw [h]
      linarith [P.S_lt_S']
  -- the endpoints `θ^{(j)}` and `θ^{(j+1)}` of the escape orbit
  have hθj : P.θs j ∈ closure (range (P.γ (j + 1))) :=
    mem_closure_of_tendsto (P.escape j hj).tendsto (Eventually.of_forall fun t => mem_range_self t)
  have hθm : P.θs (j + 1) ∈ closure (range (P.γ (j + 1))) :=
    mem_closure_of_tendsto (P.escape_lim j hj) (Eventually.of_forall fun t => mem_range_self t)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη0 : 0 < ε / 16 := by positivity
  -- the tails of the escape orbit
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    ((P.escape_lim j hj).eventually (Metric.ball_mem_nhds _ hη0))
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atBot.mp
    ((P.escape j hj).tendsto.eventually (Metric.ball_mem_nhds _ hη0))
  obtain ⟨T, hT1, hTT₀, hTtop⟩ : ∃ T : ℝ, 0 < T ∧ T₀ ≤ T ∧
      ∀ u ≥ T, dist (P.γ (j + 1) (u + c)) (P.θs (j + 1)) < ε / 16 := by
    refine ⟨max (max T₀ 1) (T₁ - c), ?_, ?_, fun u hu => hT₁ _ ?_⟩
    · exact lt_of_lt_of_le one_pos (le_trans (le_max_right T₀ 1) (le_max_left _ _))
    · exact le_trans (le_max_left T₀ 1) (le_max_left _ _)
    · linarith [le_max_right (max T₀ 1) (T₁ - c)]
  obtain ⟨T', hTbot⟩ : ∃ T' : ℝ, ∀ u ≤ -T', dist (P.γ (j + 1) (u + c)) (P.θs j) < ε / 16 :=
    ⟨c - T₂, fun u hu => hT₂ _ (by linarith)⟩
  have hT''0 : 0 < max T T' := lt_of_lt_of_le hT1 (le_max_left _ _)
  -- the claim `(C_{j+1})` at time `t₁ + T`
  have hC' := hT₀ T hTT₀
  obtain ⟨δ', hδ'0, hδ'δ₀, hδ'δ⟩ : ∃ δ', 0 < δ' ∧ δ' ≤ δ₀ ∧ δ' ≤ δ / 2 :=
    ⟨min δ₀ (δ / 2), lt_min hδ₀ (by linarith), min_le_left _ _, min_le_right _ _⟩
  -- before the escape: plateau of stage `j`
  have hE1 := tA_close_t hF hk hH P θ D hθ hj.le hpl hC (σ₁ := P.s (j + 1) - δ' / 2)
    (by linarith) ⟨fun _ => by linarith, fun h => absurd h hj.ne⟩ (a := P.s (j + 1) - δ)
    (by linarith) hη0
  have hE1' := tA_ev_le_shift hC.time (x := P.s (j + 1) - δ)
    (y := P.s (j + 1) - δ' / 2 - P.s j) (by linarith)
  -- during the escape: shadowing
  have hE2 := hJ5 δ' ⟨hδ'0, hδ'δ₀⟩ (ε / 16) hη0
  -- local uniform convergence
  have hE3 := Metric.tendstoUniformlyOn_iff.mp (hJ3 (max T T') hT''0) (ε / 16) hη0
  -- after the escape: plateau of stage `j + 1`
  obtain ⟨K, -, hE4⟩ := tA_close hF hk hH P θ D hθ (show j + 1 ≤ M by omega) hpl' hC'
    (σ₁ := P.s (j + 1) + 3 * δ / 2) (by linarith) hσm₁
  have hE4l := tA_ev_lin (K := K) hη0
  have hE4' := tA_ev_le_shift hC'.time (x := P.s (j + 1) + δ)
    (y := P.s (j + 1) + 3 * δ / 2 - P.s (j + 1)) (by linarith)
  have hE7 := tA_ev_shift_le hC'.time (x := P.s (j + 1) + δ) (y := 0) (by linarith)
  -- the jump times are `s_{j+1} + o(1)` in the slow time
  have hE5a : ∀ᶠ α in 𝓝[>] (0 : ℝ), |α ^ (k - 2) * t₁ α - P.s (j + 1)| < δ / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hJ1 (δ / 2) (by positivity)] with α hα
    rwa [Real.dist_eq] at hα
  have hE5b : ∀ᶠ α in 𝓝[>] (0 : ℝ), α ^ (k - 2) * max T T' < δ / 2 := by
    have h := (tA_tendsto_pow hk).mul_const (max T T')
    rw [zero_mul] at h
    exact h.eventually_lt_const (by positivity)
  have hμ' : 0 < μ' := hpl'.2.1
  have hmain : ∀ᶠ α in 𝓝[>] 0, hausdorffDist
      ((fun σ => θ α ((α ^ (k - 2))⁻¹ * σ)) '' Icc (P.s (j + 1) - δ) (P.s (j + 1) + δ))
      (closure (range (P.γ (j + 1)))) ≤ 5 * (ε / 16) := by
    filter_upwards [hE1, hE1', hE2, hE3, hE4, hE4l, hE4', hE7, hE5a, hE5b, self_mem_nhdsWithin]
      with α e1 e1' e2 e3 e4 e4l e4' e7 e5a e5b hα
    have hα0 : (0 : ℝ) < α := hα
    have hpk : 0 < α ^ (k - 2) := pow_pos hα0 _
    have hc : 0 < (α ^ (k - 2))⁻¹ := inv_pos.mpr hpk
    have hTmem : T ∈ Icc (-max T T') (max T T') :=
      ⟨by linarith [le_max_left T T'], le_max_left _ _⟩
    -- `θ^α(t₁ + T)` is close to `θ^{(j+1)}`
    have hnear : ‖proj (P.A (j + 1)) (θ α (t₁ α + T)) - P.θs (j + 1)‖ < 2 * (ε / 16) := by
      have h1 := e3 T hTmem
      have h2 := hTtop T le_rfl
      have hproj : proj (P.A (j + 1)) (P.θs (j + 1)) = P.θs (j + 1) :=
        proj_eq_self_of_mem_S (P.isMin (j + 1) hj).mem
      have h3 : ‖proj (P.A (j + 1)) (θ α (t₁ α + T)) - P.θs (j + 1)‖ ≤
          ‖θ α (t₁ α + T) - P.θs (j + 1)‖ := by
        calc ‖proj (P.A (j + 1)) (θ α (t₁ α + T)) - P.θs (j + 1)‖
            = ‖proj (P.A (j + 1)) (θ α (t₁ α + T) - P.θs (j + 1))‖ := by
              rw [map_sub, hproj]
          _ ≤ ‖θ α (t₁ α + T) - P.θs (j + 1)‖ := norm_zeroOut_le _ _
      have h4 := dist_triangle (θ α (t₁ α + T)) (P.γ (j + 1) (T + c)) (P.θs (j + 1))
      rw [dist_eq_norm (θ α (t₁ α + T)), dist_comm (θ α (t₁ α + T))] at h4
      linarith
    -- after `t₁ + T`, `θ^α` stays close to `θ^{(j+1)}`
    have hlate : ∀ t ∈ Icc (t₁ α + T) ((α ^ (k - 2))⁻¹ * (P.s (j + 1) + δ)),
        ‖θ α t - P.θs (j + 1)‖ < 3 * (ε / 16) := by
      intro t ht
      have h1 := e4 t ⟨ht.1, ht.2.trans (e4' _ le_rfl)⟩
      have h2 : Real.exp (-μ' * (t - (t₁ α + T))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ t - (t₁ α + T) := by linarith [ht.1]
        nlinarith
      have h3 : Real.exp (-μ' * (t - (t₁ α + T))) *
          ‖proj (P.A (j + 1)) (θ α (t₁ α + T)) - P.θs (j + 1)‖ ≤
          ‖proj (P.A (j + 1)) (θ α (t₁ α + T)) - P.θs (j + 1)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) h2
      linarith
    -- the curve reaches `[t₁ - T', t₁ + T]` in slow times `[s_{j+1} - δ, s_{j+1} + δ]`
    have h_in : ∀ u ∈ Icc (-max T T') (max T T'), ∃ σ ∈ Icc (P.s (j + 1) - δ) (P.s (j + 1) + δ),
        (α ^ (k - 2))⁻¹ * σ = t₁ α + u := by
      intro u hu
      refine ⟨α ^ (k - 2) * (t₁ α + u), ?_, tA_inv_rescale hα0 _⟩
      have h1 := abs_lt.mp e5a
      have h2 : α ^ (k - 2) * u ≤ α ^ (k - 2) * max T T' := mul_le_mul_of_nonneg_left hu.2 hpk.le
      have h3 : α ^ (k - 2) * (-max T T') ≤ α ^ (k - 2) * u :=
        mul_le_mul_of_nonneg_left hu.1 hpk.le
      rw [mul_add]
      constructor <;> nlinarith
    have h_b : t₁ α + T ≤ (α ^ (k - 2))⁻¹ * (P.s (j + 1) + δ) := by
      have := e7 _ le_rfl
      rwa [mul_zero, add_zero] at this
    have ht₀ : τ α + (α ^ (k - 2))⁻¹ * (P.s (j + 1) - δ' - P.s j) ≤
        τ α + (α ^ (k - 2))⁻¹ * (P.s (j + 1) - δ' / 2 - P.s j) := by
      have : P.s (j + 1) - δ' - P.s j ≤ P.s (j + 1) - δ' / 2 - P.s j := by linarith
      have := mul_le_mul_of_nonneg_left this hc.le
      linarith
    exact tA_hausdorff_core (φ := θ α) (γ := P.γ (j + 1)) hc hη0 hθj hθm
      (le_max_left _ _) (le_max_right _ _) hT1.le ht₀ e1
      (fun t ht => by obtain ⟨s, -, hs⟩ := e2 t ht; exact ⟨s, hs⟩) e3 hlate hTtop hTbot h_in
      (e1' _ le_rfl) h_b (by linarith)
  filter_upwards [hmain] with α hα
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  linarith

end Stages

/-- **Theorem A.** -/
theorem theoremA (F : Θ ι E → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) (hk : 3 ≤ k) (hH : Flat F k)
    (ξ : Θ ι E) (M : ℕ) (S : ℝ) (P : Process F k ξ M S)
    (θ : ℝ → ℝ → Θ ι E) (D : ℝ → Set ℝ)
    (hθ : ∀ α > 0, IsMaxFwd (gf F) (θ α) (D α) ∧ θ α 0 = α • ξ) :
    -- `θ^α` is defined on `[0, α^{2-k} S]` for small `α`
    (∀ᶠ α in 𝓝[>] 0, Icc 0 ((α ^ (k - 2))⁻¹ * S) ⊆ D α) ∧
    -- (i) plateaus
    (∀ δ > 0, TendstoUniformlyOn (fun α σ => θ α ((α ^ (k - 2))⁻¹ * σ)) P.limitPath (𝓝[>] 0)
        (Icc 0 S \ ⋃ m ∈ Finset.Icc 1 M, Ioo (P.s m - δ) (P.s m + δ))) ∧
    (∀ δ > 0, TendstoUniformlyOn (fun α σ => F (θ α ((α ^ (k - 2))⁻¹ * σ)))
        (fun σ => F (P.limitPath σ)) (𝓝[>] 0)
        (Icc 0 S \ ⋃ m ∈ Finset.Icc 1 M, Ioo (P.s m - δ) (P.s m + δ))) ∧
    (∀ m < M, F (P.θs (m + 1)) < F (P.θs m)) ∧
    -- (ii) dormant neurons
    (∀ i ∉ P.A M, TendstoUniformlyOn (fun α σ => α⁻¹ • θ α ((α ^ (k - 2))⁻¹ * σ) i) (P.Ξ i)
        (𝓝[>] 0) (Icc 0 S)) ∧
    (∀ m ∈ Finset.Icc 1 M, ∀ δ > 0, TendstoUniformlyOn
        (fun α σ => α⁻¹ • θ α ((α ^ (k - 2))⁻¹ * σ) (P.n m)) (P.Ξ (P.n m)) (𝓝[>] 0)
        (Icc 0 (P.s m - δ))) ∧
    -- (iii) jumps
    (∀ m ∈ Finset.Icc 1 M, ∃ tm : ℝ → ℝ,
        Tendsto (fun α => α ^ (k - 2) * tm α) (𝓝[>] 0) (𝓝 (P.s m)) ∧
        ∃ c : ℝ, ∀ T > 0, TendstoUniformlyOn (fun α t => θ α (tm α + t))
          (fun t => P.γ m (t + c)) (𝓝[>] 0) (Icc (-T) T)) ∧
    (∀ δ > 0, (∀ m < M, 2 * δ < P.s (m + 1) - P.s m) → 2 * δ < S - P.s M →
        ∀ m ∈ Finset.Icc 1 M, Tendsto
          (fun α => hausdorffDist
            ((fun σ => θ α ((α ^ (k - 2))⁻¹ * σ)) '' Icc (P.s m - δ) (P.s m + δ))
            (closure (range (P.γ m)))) (𝓝[>] 0) (𝓝 0)) ∧
    -- critical points and saddles
    (∀ m ≤ M, gradient F (P.θs m) = 0) ∧
    (∀ m < M, IsSaddle F (P.θs m)) := by
  refine ⟨tA_exists hF hk hH P θ D hθ,
    fun δ hδ => tA_part_i hF hk hH P θ D hθ hδ,
    fun δ hδ => tA_part_loss hF hk hH P θ D hθ hδ,
    fun m hm => P.F_lt hF hk hH hm,
    fun i hi => tA_part_ii_a hF hk hH P θ D hθ hi, ?_, ?_, ?_,
    fun m hm => P.gradient_θs_eq_zero hF hk hH hm,
    fun m hm => P.isSaddle hF hk hH hm⟩
  · intro m hm δ hδ
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact tA_part_ii_b hF hk hH P θ D hθ (by omega) hδ
  · intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact tA_part_iii hF hk hH P θ D hθ (by omega)
  · intro δ hδ hgap hgapS m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact tA_part_hausdorff hF hk hH P θ D hθ (by omega) hδ hgap hgapS

end S2S
