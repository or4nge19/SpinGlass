/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.WeightedInterpolation

/-!
# From a bound on the Guerra trace to the free-energy comparison

Guerra's interpolation schemes (Talagrand Vol. II, Lemma 14.4.1 in one dimension, Lemma 14.6.1 for
coupled copies) all end the same way: the weighted Guerra trace of the two kernels is bounded,
pointwise in the Hamiltonian, by an expression of the form

`(1/2) c₀ + (1/2) ∑_{x,y} g_x g_y θ(x, y)`   (`treeBoundIntegrand`),

a constant plus the Gibbs average of a bounded function of a pair of replicas, and the comparison
bound `wFreeEnergy_sub_le` then gives `𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ b(t) dt` with `b(t)` the
average of that expression along the interpolation. This file does that step once and for all
(`wFreeEnergy_sub_le_of_le_treeBoundIntegrand`): the integrability along the path and the
continuity of `b` in `t` (dominated convergence, `continuous_guerraBoundFn`) are discharged from
the boundedness of the Gibbs weights alone.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {A : Type*} [Fintype A]

/-! ### Continuity of the weighted Gibbs weights -/

lemma continuous_wZ (wt : A → ℝ) : Continuous fun H : FiniteGibbs.EnergySpace A => wZ wt H := by
  unfold wZ
  refine continuous_finsetSum _ fun x _ => continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((continuous_apply x).comp (PiLp.continuous_ofLp 2 (fun _ : A => ℝ))).neg

lemma continuous_wGibbs (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (x : A) :
    Continuous fun H : FiniteGibbs.EnergySpace A => wGibbs wt H x := by
  unfold wGibbs
  refine (continuous_const.mul (Real.continuous_exp.comp ?_)).div (continuous_wZ wt)
    fun H => (wZ_pos wt hwt hne H).ne'
  exact ((continuous_apply x).comp (PiLp.continuous_ofLp 2 (fun _ : A => ℝ))).neg

lemma continuous_wGuerraTrace (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (K₁ K₂ : A → A → ℝ) (n : ℕ) :
    Continuous fun H : FiniteGibbs.EnergySpace A => wGuerraTrace wt K₁ K₂ n H := by
  unfold wGuerraTrace
  refine continuous_const.mul ((continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_wGibbs wt hwt hne x)).sub
    (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      continuous_const.mul ((continuous_wGibbs wt hwt hne x).mul (continuous_wGibbs wt hwt hne y))))

/-- The integrand of the bound (14.79):
`(1/2)(ξ(1) - ξ'(q̄)) + (1/2) ∑_{x,y} g_x g_y θ(q_{x,y})`. -/
def treeBoundIntegrand (wt : A → ℝ) (c₀ : ℝ) (θq : A → A → ℝ) (H : FiniteGibbs.EnergySpace A) :
    ℝ :=
  (1 / 2) * c₀ + (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y * θq x y

lemma continuous_treeBoundIntegrand (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c₀ : ℝ) (θq : A → A → ℝ) :
    Continuous fun H : FiniteGibbs.EnergySpace A => treeBoundIntegrand wt c₀ θq H := by
  unfold treeBoundIntegrand
  refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_finsetSum _ fun y _ =>
      ((continuous_wGibbs wt hwt hne x).mul (continuous_wGibbs wt hwt hne y)).mul continuous_const))

lemma abs_treeBoundIntegrand_le (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c₀ : ℝ) (θq : A → A → ℝ) (H : FiniteGibbs.EnergySpace A) :
    |treeBoundIntegrand wt c₀ θq H| ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y| := by
  unfold treeBoundIntegrand
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)).trans (one_mul _).le
    rw [abs_of_nonneg (mul_nonneg (wGibbs_nonneg wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y))]
    exact mul_le_one₀ (wGibbs_le_one wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y)
      (wGibbs_le_one wt hwt hne H y)

/-! ### The integrated bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K₁ K₂ : A → A → ℝ}

/-- The bound `b(t) = ∫ [(1/2) c₀ + (1/2) ⟨θ⟩_{H_t}] dP` along the interpolation `H_t = Z_t + c`. -/
def guerraBoundFn (G₁ : GaussianField (α := A) P K₁) (G₂ : GaussianField (α := A) P K₂)
    (wt : A → ℝ) (c₀ : ℝ) (θq : A → A → ℝ) (c : FiniteGibbs.EnergySpace A) (t : ℝ) : ℝ :=
  ∫ p : PairSpace A, treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c) ∂pairLaw G₁ G₂

/-- The integrated bound is continuous in `t`, by dominated convergence: the integrand is
continuous in `t` and bounded by a constant. -/
lemma continuous_guerraBoundFn (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (c₀ : ℝ) (θq : A → A → ℝ)
    (c : FiniteGibbs.EnergySpace A) :
    Continuous (guerraBoundFn G₁ G₂ wt c₀ θq c) := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  unfold guerraBoundFn
  refine continuous_of_dominated (fun t => ?_)
    (bound := fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (fun t => Filter.Eventually.of_forall fun p => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun p => ?_)
  · exact ((continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _
  · exact (continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((continuous_gaussianInterp_apply p).add continuous_const)

/-- **From a pointwise bound on the Guerra trace to the free-energy comparison.** If for every
Hamiltonian `wGuerraTrace wt K₁ K₂ n H ≤ (1/2) c₀ + (1/2) ⟨θ⟩_H`, then

`𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ 𝔼 [(1/2) c₀ + (1/2) ⟨θ⟩_{H_t}] dt`.

This is the common final step of Guerra's one-dimensional scheme (Lemma 14.4.1) and of its
two-dimensional version for coupled copies (Lemma 14.6.1). -/
theorem wFreeEnergy_sub_le_of_le_treeBoundIntegrand (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (n : ℕ) (c : FiniteGibbs.EnergySpace A) (c₀ : ℝ)
    (θq : A → A → ℝ)
    (hle : ∀ H : FiniteGibbs.EnergySpace A,
      wGuerraTrace wt K₁ K₂ n H ≤ treeBoundIntegrand wt c₀ θq H) :
    (∫ ω, wFreeEnergy wt n (G₁.U ω + c) ∂P) - (∫ ω, wFreeEnergy wt n (G₂.U ω + c) ∂P)
      ≤ ∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq c t := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  have hcontb := continuous_guerraBoundFn G₁ G₂ hindep wt hwt hne c₀ θq c
  refine wFreeEnergy_sub_le G₁ G₂ hindep wt hwt hne c n (fun t _ => ?_)
    (hcontb.intervalIntegrable 0 1)
  have hcontT := continuous_wGuerraTrace wt hwt hne K₁ K₂ n
  have hint1 : Integrable (fun p : PairSpace A =>
      wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
    refine Integrable.of_bound ((hcontT.comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
      ((1 / (2 * (n : ℝ))) * ((∑ x, |K₁ x x - K₂ x x|) + ∑ x, ∑ y, |K₁ x y - K₂ x y|))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_wGuerraTrace_le wt hwt hne _ _ n _
  have hint2 : Integrable (fun p : PairSpace A =>
      treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
    refine Integrable.of_bound (((continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
      ((1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _
  exact integral_mono hint1 hint2 fun p => hle _

/-! ### An independent random external field -/

/-- The integrated bound is uniformly bounded. -/
lemma abs_guerraBoundFn_le (G₁ : GaussianField (α := A) P K₁) (G₂ : GaussianField (α := A) P K₂)
    (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c₀ : ℝ) (θq : A → A → ℝ) (c : FiniteGibbs.EnergySpace A) (t : ℝ) :
    |guerraBoundFn G₁ G₂ wt c₀ θq c t| ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y| := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  unfold guerraBoundFn
  have h := norm_integral_le_of_norm_le_const (μ := pairLaw G₁ G₂)
    (f := fun p : PairSpace A => treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c))
    (C := (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-- The integrated bound is jointly continuous in the external field and the time. -/
lemma continuous_guerraBoundFn_prod (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (c₀ : ℝ) (θq : A → A → ℝ) :
    Continuous fun q : FiniteGibbs.EnergySpace A × ℝ => guerraBoundFn G₁ G₂ wt c₀ θq q.1 q.2 := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  unfold guerraBoundFn
  refine continuous_of_dominated (fun q => ?_)
    (bound := fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (fun q => Filter.Eventually.of_forall fun p => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun p => ?_)
  · exact ((continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((gaussianInterp q.2).continuous.add continuous_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _
  · exact (continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      (((continuous_gaussianInterp_apply p).comp continuous_snd).add continuous_fst)

/-- `|log ∑_x w_x e^{-H x} - log ∑_x w_x| ≤ ‖H‖`. -/
lemma abs_log_wZ_sub_le (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : FiniteGibbs.EnergySpace A) :
    |Real.log (wZ wt H) - Real.log (∑ x, wt x)| ≤ ‖H‖ := by
  have hS : 0 < ∑ x, wt x := Finset.sum_pos' (fun x _ => hwt x)
    ⟨hne.choose, Finset.mem_univ _, lt_of_le_of_ne (hwt _) hne.choose_spec.symm⟩
  have hHx : ∀ x, |H x| ≤ ‖H‖ := fun x => by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le H x
  have hup : wZ wt H ≤ (∑ x, wt x) * Real.exp ‖H‖ := by
    unfold wZ
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hwt x)
    linarith [neg_abs_le (H x), hHx x]
  have hlow : (∑ x, wt x) * Real.exp (-‖H‖) ≤ wZ wt H := by
    unfold wZ
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hwt x)
    linarith [le_abs_self (H x), hHx x]
  have hZ : 0 < wZ wt H := wZ_pos wt hwt hne H
  rw [abs_sub_le_iff]
  constructor
  · have := Real.log_le_log hZ hup
    rw [Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    linarith
  · have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    linarith

lemma abs_wFreeEnergy_le (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (n : ℕ)
    (H : FiniteGibbs.EnergySpace A) :
    |wFreeEnergy wt n H| ≤ (1 / (n : ℝ)) * (|Real.log (∑ x, wt x)| + ‖H‖) := by
  unfold wFreeEnergy
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |Real.log (wZ wt H)|
      = |(Real.log (wZ wt H) - Real.log (∑ x, wt x)) + Real.log (∑ x, wt x)| := by ring_nf
    _ ≤ |Real.log (wZ wt H) - Real.log (∑ x, wt x)| + |Real.log (∑ x, wt x)| := abs_add_le _ _
    _ ≤ ‖H‖ + |Real.log (∑ x, wt x)| := add_le_add (abs_log_wZ_sub_le wt hwt hne H) le_rfl
    _ = _ := add_comm _ _

lemma continuous_wFreeEnergy (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (n : ℕ) :
    Continuous fun H : FiniteGibbs.EnergySpace A => wFreeEnergy wt n H :=
  continuous_const.mul ((continuous_wZ wt).log fun H => (wZ_pos wt hwt hne H).ne')

/-- The weighted free energy of an integrable random Hamiltonian is integrable. -/
lemma integrable_wFreeEnergy_of_integrable_norm [IsFiniteMeasure P] (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (n : ℕ) {g : Ω → FiniteGibbs.EnergySpace A}
    (hg : Measurable g) (hint : Integrable (fun ω => ‖g ω‖) P) :
    Integrable (fun ω => wFreeEnergy wt n (g ω)) P := by
  refine Integrable.mono' (((integrable_const |Real.log (∑ x, wt x)|).add hint).const_mul (1 / (n : ℝ)))
    ((continuous_wFreeEnergy wt hwt hne n).measurable.comp hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_wFreeEnergy_le wt hwt hne n (g ω)

/-- **The free-energy comparison with an independent random external field.** If `c` is an
integrable random Hamiltonian independent of the pair `(U, V)`, then

`𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ 𝔼_c b(c, t) dt`,

`b(c, t)` being the integrated bound `guerraBoundFn` for the constant `c`: conditionally on `c`
the comparison is the one of `wFreeEnergy_sub_le_of_le_treeBoundIntegrand`, and both sides are
integrated over the law of `c` (Fubini). This is how Talagrand's Lemma 14.6.1 handles the
Hamiltonian `H⁰` of (14.126), "independent of the randomness of `H_N`" and of `H`. -/
theorem wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep [IsProbabilityMeasure P]
    (G₁ : GaussianField (α := A) P K₁) (G₂ : GaussianField (α := A) P K₂)
    (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (n : ℕ) {c : Ω → FiniteGibbs.EnergySpace A} (hc : Measurable c) (hcint : Integrable c P)
    (hci : pair G₁ G₂ ⟂ᵢ[P] c) (c₀ : ℝ) (θq : A → A → ℝ)
    (hle : ∀ H : FiniteGibbs.EnergySpace A,
      wGuerraTrace wt K₁ K₂ n H ≤ treeBoundIntegrand wt c₀ θq H) :
    (∫ ω, wFreeEnergy wt n (G₁.U ω + c ω) ∂P) - (∫ ω, wFreeEnergy wt n (G₂.U ω + c ω) ∂P)
      ≤ ∫ t in (0 : ℝ)..1, ∫ ω, guerraBoundFn G₁ G₂ wt c₀ θq (c ω) t ∂P := by
  have hG := isGaussian_pairLaw G₁ G₂ hindep
  set ν : Measure (FiniteGibbs.EnergySpace A) := P.map c with hν
  have hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hc.aemeasurable
  have hΦ : Measurable fun ω => (pair G₁ G₂ ω, c ω) := (measurable_pair G₁ G₂).prodMk hc
  have hjoint : P.map (fun ω => (pair G₁ G₂ ω, c ω)) = (pairLaw G₁ G₂).prod ν :=
    hci.map_prod_eq_prod_map_map (measurable_pair G₁ G₂).aemeasurable hc.aemeasurable
  set B : ℝ := (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y| with hB
  set F₁ : PairSpace A × FiniteGibbs.EnergySpace A → ℝ :=
    fun q => wFreeEnergy wt n ((WithLp.ofLp q.1).1 + q.2) with hF₁
  set F₂ : PairSpace A × FiniteGibbs.EnergySpace A → ℝ :=
    fun q => wFreeEnergy wt n ((WithLp.ofLp q.1).2 + q.2) with hF₂
  have hcw := continuous_wFreeEnergy wt hwt hne n
  have hofLp : Continuous fun q : PairSpace A × FiniteGibbs.EnergySpace A => WithLp.ofLp q.1 :=
    (WithLp.prod_continuous_ofLp (p := (2 : ℝ≥0∞)) (α := FiniteGibbs.EnergySpace A)
      (β := FiniteGibbs.EnergySpace A)).comp continuous_fst
  have hF₁c : Continuous F₁ := hcw.comp ((continuous_fst.comp hofLp).add continuous_snd)
  have hF₂c : Continuous F₂ := hcw.comp ((continuous_snd.comp hofLp).add continuous_snd)
  have hint₁ : Integrable (fun ω => wFreeEnergy wt n (G₁.U ω + c ω)) P :=
    integrable_wFreeEnergy_of_integrable_norm wt hwt hne n (G₁.measU.add hc)
      (G₁.integrable.add hcint).norm
  have hint₂ : Integrable (fun ω => wFreeEnergy wt n (G₂.U ω + c ω)) P :=
    integrable_wFreeEnergy_of_integrable_norm wt hwt hne n (G₂.measU.add hc)
      (G₂.integrable.add hcint).norm
  have hF₁i : Integrable F₁ ((pairLaw G₁ G₂).prod ν) := by
    rw [← hjoint]
    exact (integrable_map_measure hF₁c.aestronglyMeasurable hΦ.aemeasurable).2 hint₁
  have hF₂i : Integrable F₂ ((pairLaw G₁ G₂).prod ν) := by
    rw [← hjoint]
    exact (integrable_map_measure hF₂c.aestronglyMeasurable hΦ.aemeasurable).2 hint₂
  have e₁ : (∫ ω, wFreeEnergy wt n (G₁.U ω + c ω) ∂P)
      = ∫ z, ∫ p, F₁ (p, z) ∂pairLaw G₁ G₂ ∂ν := by
    rw [← integral_prod_symm F₁ hF₁i, ← hjoint,
      integral_map hΦ.aemeasurable hF₁c.aestronglyMeasurable]
    rfl
  have e₂ : (∫ ω, wFreeEnergy wt n (G₂.U ω + c ω) ∂P)
      = ∫ z, ∫ p, F₂ (p, z) ∂pairLaw G₁ G₂ ∂ν := by
    rw [← integral_prod_symm F₂ hF₂i, ← hjoint,
      integral_map hΦ.aemeasurable hF₂c.aestronglyMeasurable]
    rfl
  -- the comparison at a fixed value of the external field
  have hfix : ∀ z, (∫ p, F₁ (p, z) ∂pairLaw G₁ G₂) - (∫ p, F₂ (p, z) ∂pairLaw G₁ G₂)
      ≤ ∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq z t := by
    intro z
    have h := wFreeEnergy_sub_le_of_le_treeBoundIntegrand G₁ G₂ hindep wt hwt hne n z c₀ θq hle
    have e1 : (∫ ω, wFreeEnergy wt n (G₁.U ω + z) ∂P) = ∫ p, F₁ (p, z) ∂pairLaw G₁ G₂ := by
      rw [integral_map (f := fun p : PairSpace A => F₁ (p, z))
        (measurable_pair G₁ G₂).aemeasurable
        (by exact (hF₁c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)]
      rfl
    have e2 : (∫ ω, wFreeEnergy wt n (G₂.U ω + z) ∂P) = ∫ p, F₂ (p, z) ∂pairLaw G₁ G₂ := by
      rw [integral_map (f := fun p : PairSpace A => F₂ (p, z))
        (measurable_pair G₁ G₂).aemeasurable
        (by exact (hF₂c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)]
      rfl
    rw [e1, e2] at h
    exact h
  have hA : Integrable (fun z => ∫ p, F₁ (p, z) ∂pairLaw G₁ G₂) ν := hF₁i.integral_prod_right
  have hB' : Integrable (fun z => ∫ p, F₂ (p, z) ∂pairLaw G₁ G₂) ν := hF₂i.integral_prod_right
  have hbcont := continuous_guerraBoundFn_prod G₁ G₂ hindep wt hwt hne c₀ θq
  have hbabs : ∀ z t, |guerraBoundFn G₁ G₂ wt c₀ θq z t| ≤ B := fun z t =>
    abs_guerraBoundFn_le G₁ G₂ hindep wt hwt hne c₀ θq z t
  have hC : Integrable (fun z => ∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq z t) ν := by
    refine Integrable.of_bound ?_ B (Filter.Eventually.of_forall fun z => ?_)
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun z t => guerraBoundFn G₁ G₂ wt c₀ θq z t) hbcont 0 1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B)
        (f := fun t => guerraBoundFn G₁ G₂ wt c₀ θq z t) (fun t _ => by
          rw [Real.norm_eq_abs]; exact hbabs z t)
      rwa [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at this
  have hmono : (∫ z, (∫ p, F₁ (p, z) ∂pairLaw G₁ G₂) - ∫ p, F₂ (p, z) ∂pairLaw G₁ G₂ ∂ν)
      ≤ ∫ z, (∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq z t) ∂ν :=
    integral_mono (hA.sub hB') hC hfix
  rw [integral_sub hA hB'] at hmono
  -- Fubini for the bound
  have hswap : (∫ z, (∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq z t) ∂ν)
      = ∫ t in (0 : ℝ)..1, ∫ z, guerraBoundFn G₁ G₂ wt c₀ θq z t ∂ν := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hint : Integrable (Function.uncurry fun z t => guerraBoundFn G₁ G₂ wt c₀ θq z t)
        (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.of_bound hbcont.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hbabs q.1 q.2)
    simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
    exact integral_integral_swap hint
  have hlast : ∀ t, (∫ z, guerraBoundFn G₁ G₂ wt c₀ θq z t ∂ν)
      = ∫ ω, guerraBoundFn G₁ G₂ wt c₀ θq (c ω) t ∂P := fun t => by
    rw [hν, integral_map (f := fun z => guerraBoundFn G₁ G₂ wt c₀ θq z t) hc.aemeasurable
      (by exact (hbcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)]
  simp_rw [hlast] at hswap
  rw [e₁, e₂]
  exact hmono.trans (le_of_eq hswap)

/-- The bound of `wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep`, as one expectation over the
joint sample: `𝔼 [(1/2) c₀ + (1/2) ⟨θ⟩_{√t U + √(1-t) V + c}]`. -/
lemma integral_guerraBoundFn_eq [IsProbabilityMeasure P] (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) {c : Ω → FiniteGibbs.EnergySpace A}
    (hc : Measurable c) (hci : pair G₁ G₂ ⟂ᵢ[P] c) (c₀ : ℝ) (θq : A → A → ℝ) (t : ℝ) :
    (∫ ω, guerraBoundFn G₁ G₂ wt c₀ θq (c ω) t ∂P)
      = ∫ ω, treeBoundIntegrand wt c₀ θq (gaussianInterp t (pair G₁ G₂ ω) + c ω) ∂P := by
  have hG := isGaussian_pairLaw G₁ G₂ hindep
  set ν : Measure (FiniteGibbs.EnergySpace A) := P.map c with hν
  have hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hc.aemeasurable
  have hΦ : Measurable fun ω => (pair G₁ G₂ ω, c ω) := (measurable_pair G₁ G₂).prodMk hc
  have hjoint : P.map (fun ω => (pair G₁ G₂ ω, c ω)) = (pairLaw G₁ G₂).prod ν :=
    hci.map_prod_eq_prod_map_map (measurable_pair G₁ G₂).aemeasurable hc.aemeasurable
  set F : PairSpace A × FiniteGibbs.EnergySpace A → ℝ :=
    fun q => treeBoundIntegrand wt c₀ θq (gaussianInterp t q.1 + q.2) with hF
  have hFc : Continuous F := (continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
    (((gaussianInterp t).continuous.comp continuous_fst).add continuous_snd)
  have hFi : Integrable F ((pairLaw G₁ G₂).prod ν) :=
    Integrable.of_bound hFc.aestronglyMeasurable
      ((1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|) (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _)
  have e1 : (∫ ω, guerraBoundFn G₁ G₂ wt c₀ θq (c ω) t ∂P)
      = ∫ z, ∫ p, F (p, z) ∂pairLaw G₁ G₂ ∂ν := by
    rw [hν, integral_map (f := fun z => ∫ p, F (p, z) ∂pairLaw G₁ G₂) hc.aemeasurable
      (by exact ((continuous_guerraBoundFn_prod G₁ G₂ hindep wt hwt hne c₀ θq).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable)]
    rfl
  rw [e1, ← integral_prod_symm F hFi, ← hjoint,
    integral_map hΦ.aemeasurable hFc.aestronglyMeasurable]

/-- `wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep` with the bound written as one
expectation over the joint sample of the fields and of the external field. -/
theorem wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep' [IsProbabilityMeasure P]
    (G₁ : GaussianField (α := A) P K₁) (G₂ : GaussianField (α := A) P K₂)
    (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (n : ℕ) {c : Ω → FiniteGibbs.EnergySpace A} (hc : Measurable c) (hcint : Integrable c P)
    (hci : pair G₁ G₂ ⟂ᵢ[P] c) (c₀ : ℝ) (θq : A → A → ℝ)
    (hle : ∀ H : FiniteGibbs.EnergySpace A,
      wGuerraTrace wt K₁ K₂ n H ≤ treeBoundIntegrand wt c₀ θq H) :
    (∫ ω, wFreeEnergy wt n (G₁.U ω + c ω) ∂P) - (∫ ω, wFreeEnergy wt n (G₂.U ω + c ω) ∂P)
      ≤ ∫ t in (0 : ℝ)..1,
          ∫ ω, treeBoundIntegrand wt c₀ θq (gaussianInterp t (pair G₁ G₂ ω) + c ω) ∂P := by
  refine (wFreeEnergy_sub_le_of_le_treeBoundIntegrand_indep G₁ G₂ hindep wt hwt hne n hc hcint
    hci c₀ θq hle).trans (le_of_eq ?_)
  exact intervalIntegral.integral_congr fun t _ =>
    integral_guerraBoundFn_eq G₁ G₂ hindep wt hwt hne hc hci c₀ θq t

end

end SpinGlass
