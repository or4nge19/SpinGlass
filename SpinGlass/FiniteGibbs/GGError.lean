/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GGDefect

/-!
# The Ghirlanda–Guerra error is the energy fluctuation

`FiniteGibbs.ghirlandaGuerra_defect` identifies the failure of the Ghirlanda–Guerra identity for a
test function `f` of `m` replicas with the energy–observable covariance
`𝔼⟨H_{σⁱ} f⟩ - 𝔼⟨f⟩ 𝔼⟨H⟩`. This file bounds that covariance by the **energy fluctuation**

`𝔼⟨(H - a)²⟩`,  `a = 𝔼⟨H⟩`,

giving a Ghirlanda–Guerra identity with an explicit error term at every finite volume:

`|GG-combination(f)| ≤ ‖f‖_∞ · √(𝔼⟨(H - 𝔼⟨H⟩)²⟩)`.

The proof is three elementary steps, each of independent use:

* the `i`-th coordinate of the `m`-replica product Gibbs measure has the Gibbs measure as its
  marginal (`gibbs_average_n_det_eval`), so a function of one replica may be averaged in one
  replica;
* Cauchy–Schwarz for the Gibbs bracket, `⟨|u|⟩² ≤ ⟨u²⟩` (`sq_sum_gibbs_pmf_mul_abs_le`);
* Cauchy–Schwarz for the disorder average, `(𝔼X)² ≤ 𝔼X²`.

Nothing here needs the Hamiltonian to be Gaussian, or centred: the bound holds for an arbitrary
law of `H` with enough moments and an arbitrary constant `a`. Gaussianity enters only when one
computes the right-hand side, which the cavity identity does exactly
(`integral_gibbs_average_sub_const_sq`).

## Main statements

- `FiniteGibbs.gibbs_average_n_det_eval`: the one-replica marginal.
- `FiniteGibbs.sq_sum_gibbs_pmf_mul_abs_le`: Cauchy–Schwarz for the Gibbs bracket.
- `FiniteGibbs.abs_integral_gibbs_average_energy_mul_sub_le`: **the error bound**.
- `FiniteGibbs.ghirlandaGuerra_error_le`: Ghirlanda–Guerra with an explicit error term.
-/

open MeasureTheory ProbabilityTheory BigOperators
open scoped InnerProductSpace ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-! ### The one-replica marginal of the product Gibbs measure -/

/-- **Every coordinate of the `m`-replica product Gibbs measure has the Gibbs measure as its
marginal**: `⟨u(σⁱ)⟩ = ⟨u⟩`. -/
lemma gibbs_average_n_det_eval (m : ℕ) (H : EnergySpace α) (u : α → ℝ) (i : Fin m) :
    gibbs_average_n_det (α := α) (n := m) H (fun σs => u (σs i))
      = ∑ σ : α, u σ * gibbs_pmf (α := α) H σ := by
  classical
  set p : α → ℝ := fun σ => gibbs_pmf (α := α) H σ with hp
  set g : Fin m → α → ℝ := fun l x => if l = i then u x * p x else p x with hg
  have hfac : (∑ σs : ReplicaSpace (α := α) m, ∏ l : Fin m, g l (σs l))
      = ∏ l : Fin m, ∑ x : α, g l x := by
    rw [← Finset.sum_prod_piFinset]
    exact Finset.sum_congr (by simp [Fintype.piFinset_univ]) (fun _ _ => rfl)
  have hprod : ∀ σs : ReplicaSpace (α := α) m,
      (∏ l : Fin m, g l (σs l)) = u (σs i) * ∏ l : Fin m, p (σs l) := by
    intro σs
    rw [← Finset.mul_prod_erase _ (fun l : Fin m => g l (σs l)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun l : Fin m => p (σs l)) (Finset.mem_univ i)]
    have hg_i : g i (σs i) = u (σs i) * p (σs i) := by simp [hg]
    have hg_ne : ∀ l ∈ (Finset.univ : Finset (Fin m)).erase i, g l (σs l) = p (σs l) := by
      intro l hl
      simp [hg, Finset.mem_erase.mp hl |>.1]
    rw [hg_i, Finset.prod_congr rfl hg_ne]
    ring
  have hsum : ∀ l : Fin m, (∑ x : α, g l x) = if l = i then ∑ x : α, u x * p x else 1 := by
    intro l
    by_cases hl : l = i
    · simp [hg, hl]
    · simp only [hg, hl, ite_false, hp]
      exact sum_gibbs_pmf (α := α) H
  calc gibbs_average_n_det (α := α) (n := m) H (fun σs => u (σs i))
      = ∑ σs : ReplicaSpace (α := α) m, ∏ l : Fin m, g l (σs l) := by
        rw [gibbs_average_n_det]
        exact (Finset.sum_congr rfl fun σs _ => (hprod σs)).symm
    _ = ∏ l : Fin m, ∑ x : α, g l x := hfac
    _ = ∑ σ : α, u σ * gibbs_pmf (α := α) H σ := by
        rw [Finset.prod_congr rfl fun l _ => hsum l,
          ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp [hp]

/-! ### Cauchy–Schwarz for the Gibbs bracket -/

/-- **Cauchy–Schwarz for the Gibbs bracket**: `⟨|u|⟩² ≤ ⟨u²⟩`. -/
lemma sq_sum_gibbs_pmf_mul_abs_le (H : EnergySpace α) (u : α → ℝ) :
    (∑ σ : α, gibbs_pmf (α := α) H σ * |u σ|) ^ 2
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * (u σ) ^ 2 := by
  classical
  have hnn : ∀ σ : α, 0 ≤ gibbs_pmf (α := α) H σ := fun σ => gibbs_pmf_nonneg (α := α) H σ
  have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun σ => Real.sqrt (gibbs_pmf (α := α) H σ))
    (fun σ => Real.sqrt (gibbs_pmf (α := α) H σ) * |u σ|)
  have e1 : ∀ σ : α, Real.sqrt (gibbs_pmf (α := α) H σ)
      * (Real.sqrt (gibbs_pmf (α := α) H σ) * |u σ|)
      = gibbs_pmf (α := α) H σ * |u σ| := by
    intro σ
    rw [← mul_assoc, Real.mul_self_sqrt (hnn σ)]
  have e2 : ∀ σ : α, Real.sqrt (gibbs_pmf (α := α) H σ) ^ 2 = gibbs_pmf (α := α) H σ :=
    fun σ => Real.sq_sqrt (hnn σ)
  have e3 : ∀ σ : α, (Real.sqrt (gibbs_pmf (α := α) H σ) * |u σ|) ^ 2
      = gibbs_pmf (α := α) H σ * (u σ) ^ 2 := by
    intro σ
    rw [mul_pow, e2 σ, sq_abs]
  calc (∑ σ : α, gibbs_pmf (α := α) H σ * |u σ|) ^ 2
      = (∑ σ : α, Real.sqrt (gibbs_pmf (α := α) H σ)
          * (Real.sqrt (gibbs_pmf (α := α) H σ) * |u σ|)) ^ 2 :=
        congrArg (· ^ 2) (Finset.sum_congr rfl fun σ _ => (e1 σ).symm)
    _ ≤ (∑ σ : α, Real.sqrt (gibbs_pmf (α := α) H σ) ^ 2)
          * ∑ σ : α, (Real.sqrt (gibbs_pmf (α := α) H σ) * |u σ|) ^ 2 := key
    _ = ∑ σ : α, gibbs_pmf (α := α) H σ * (u σ) ^ 2 := by
        rw [Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_congr rfl fun σ _ => e3 σ,
          sum_gibbs_pmf, one_mul]

/-! ### Elementary bounds on the energy fluctuation -/

/-- The Gibbs average of `|H - a|` is bounded by `‖H‖ + |a|`. -/
lemma sum_gibbs_pmf_mul_abs_sub_le (a : ℝ) (H : EnergySpace α) :
    (∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|) ≤ ‖H‖ + |a| := by
  classical
  calc (∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|)
      ≤ ∑ _σ : α, gibbs_pmf (α := α) H _σ * (‖H‖ + |a|) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (gibbs_pmf_nonneg (α := α) H σ)
        calc |H σ - a| ≤ |H σ| + |a| := abs_sub _ _
          _ ≤ ‖H‖ + |a| := by
              gcongr
              exact abs_apply_le_norm (α := α) H σ
    _ = ‖H‖ + |a| := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]

/-- Continuity of the Gibbs average of `|H - a|` in the Hamiltonian. -/
lemma continuous_sum_gibbs_pmf_mul_abs_sub (a : ℝ) :
    Continuous fun H : EnergySpace α => ∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a| :=
  continuous_finsetSum _ fun σ _ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous).mul
      (((evalCLM (α := α) σ).continuous.sub continuous_const).abs)

/-- Continuity of the Gibbs average of `(H - a)²` in the Hamiltonian. -/
lemma continuous_sum_gibbs_pmf_mul_sub_sq (a : ℝ) :
    Continuous fun H : EnergySpace α => ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2 :=
  continuous_finsetSum _ fun σ _ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous).mul
      (((evalCLM (α := α) σ).continuous.sub continuous_const).pow 2)

/-! ### Integrability of the energy fluctuation -/

variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

/-- The Gibbs average of `|H - a|` is square-integrable under a Gaussian law. -/
lemma memLp_two_sum_gibbs_pmf_mul_abs_sub (a : ℝ) :
    MemLp (fun H : EnergySpace α => ∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|) 2 μ := by
  classical
  have hcont := continuous_sum_gibbs_pmf_mul_abs_sub (α := α) a
  have hnn : ∀ H : EnergySpace α, 0 ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a| :=
    fun H => Finset.sum_nonneg fun σ _ =>
      mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (abs_nonneg _)
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    ((hcont.pow 2).measurable) (C := (1 + |a|) ^ 2) (m := 2) (by positivity) fun H => ?_
  have h1 : (∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|) ≤ (1 + |a|) * (1 + ‖H‖) := by
    refine le_trans (sum_gibbs_pmf_mul_abs_sub_le (α := α) a H) ?_
    nlinarith [norm_nonneg H, abs_nonneg a]
  have h2 : |(∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|) ^ 2|
      ≤ ((1 + |a|) * (1 + ‖H‖)) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (hnn H) h1 2
  calc |(∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a|) ^ 2|
      ≤ ((1 + |a|) * (1 + ‖H‖)) ^ 2 := h2
    _ = (1 + |a|) ^ 2 * (1 + ‖H‖) ^ 2 := by ring

/-- The Gibbs average of `(H - a)²` is integrable under a Gaussian law. -/
lemma integrable_sum_gibbs_pmf_mul_sub_sq (a : ℝ) :
    Integrable (fun H : EnergySpace α => ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2) μ := by
  classical
  have hcont := continuous_sum_gibbs_pmf_mul_sub_sq (α := α) a
  refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    hcont.measurable (C := (1 + |a|) ^ 2) (m := 2) (by positivity) fun H => ?_
  have hterm : ∀ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2
      ≤ gibbs_pmf (α := α) H σ * ((1 + |a|) * (1 + ‖H‖)) ^ 2 := by
    intro σ
    refine mul_le_mul_of_nonneg_left ?_ (gibbs_pmf_nonneg (α := α) H σ)
    have hb : |H σ - a| ≤ (1 + |a|) * (1 + ‖H‖) := by
      have h0 : |H σ - a| ≤ ‖H‖ + |a| := by
        calc |H σ - a| ≤ |H σ| + |a| := abs_sub _ _
          _ ≤ ‖H‖ + |a| := by
              gcongr
              exact abs_apply_le_norm (α := α) H σ
      nlinarith [norm_nonneg H, abs_nonneg a]
    calc (H σ - a) ^ 2 = |H σ - a| ^ 2 := (sq_abs _).symm
      _ ≤ ((1 + |a|) * (1 + ‖H‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hnn : 0 ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2 :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (sq_nonneg _)
  rw [abs_of_nonneg hnn]
  calc (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2)
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ((1 + |a|) * (1 + ‖H‖)) ^ 2 :=
        Finset.sum_le_sum fun σ _ => hterm σ
    _ = ((1 + |a|) * (1 + ‖H‖)) ^ 2 := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]
    _ = (1 + |a|) ^ 2 * (1 + ‖H‖) ^ 2 := by ring

/-! ### The error bound -/

/-- **The energy–observable covariance is controlled by the energy fluctuation.** For any constant
`a`, any `m`-replica test function `f` bounded by `B`, and any index `i`,

`|𝔼⟨H_{σⁱ} f⟩ - a 𝔼⟨f⟩| ≤ B √(𝔼⟨(H - a)²⟩)`.

Three Cauchy–Schwarz steps: the `i`-th coordinate is averaged out by
`gibbs_average_n_det_eval`, then `⟨|H - a|⟩² ≤ ⟨(H - a)²⟩` and `(𝔼X)² ≤ 𝔼X²`. -/
theorem abs_integral_gibbs_average_energy_mul_sub_le
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) {B : ℝ} (hB : ∀ σs, |f σs| ≤ B) (a : ℝ) :
    |(∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
        - a * ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ|
      ≤ B * Real.sqrt (∫ H : EnergySpace α,
          (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2) ∂μ) := by
  classical
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (fun _ => Classical.arbitrary α))
  set W : EnergySpace α → ℝ :=
    fun H => ∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - a| with hW
  set V : EnergySpace α → ℝ :=
    fun H => ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2 with hV
  have hWnn : ∀ H : EnergySpace α, 0 ≤ W H := fun H =>
    Finset.sum_nonneg fun σ _ => mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (abs_nonneg _)
  have hWLp : MemLp W 2 μ := memLp_two_sum_gibbs_pmf_mul_abs_sub (α := α) (μ := μ) a
  have hWint : Integrable W μ := hWLp.integrable one_le_two
  have hVint : Integrable V μ := integrable_sum_gibbs_pmf_mul_sub_sq (α := α) (μ := μ) a
  -- the two integrals on the left-hand side exist
  have hBf : ∀ σs : ReplicaSpace (α := α) m, ‖f σs‖ ≤ B := fun σs => by
    simpa [Real.norm_eq_abs] using hB σs
  have hI2 : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H f) μ :=
    integrable_gibbs_average_n_det_of_bounded (μ := μ) m (fun _ => f)
      ((contDiff_gibbs_average_n_det (α := α) m f).continuous) (B := B) (fun _ σs => hBf σs)
  have hI1 : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
        (fun σs => H (σs i) * f σs)) μ := by
    have hcont : Continuous fun H : EnergySpace α =>
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) := by
      simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun σs _ =>
        (((evalCLM (α := α) (σs i)).continuous.mul continuous_const).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
      hcont.measurable (C := B) (m := 1) hB0 fun H => ?_
    have hstep : |gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs)|
        ≤ ∑ σs : ReplicaSpace (α := α) m,
            |H (σs i) * f σs| * ∏ l, gibbs_pmf (α := α) H (σs l) := by
      rw [gibbs_average_n_det]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun σs _ => ?_))
      rw [abs_mul,
        abs_of_nonneg (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (α := α) H (σs l))]
    refine le_trans hstep ?_
    calc (∑ σs : ReplicaSpace (α := α) m,
            |H (σs i) * f σs| * ∏ l, gibbs_pmf (α := α) H (σs l))
        ≤ ∑ σs : ReplicaSpace (α := α) m,
            (‖H‖ * B) * ∏ l, gibbs_pmf (α := α) H (σs l) := by
          refine Finset.sum_le_sum fun σs _ => ?_
          refine mul_le_mul_of_nonneg_right ?_
            (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (α := α) H (σs l))
          rw [abs_mul]
          exact mul_le_mul (abs_apply_le_norm (α := α) H (σs i)) (hB σs) (abs_nonneg _)
            (norm_nonneg _)
      _ = ‖H‖ * B := by
          rw [← Finset.mul_sum, sum_prod_gibbs_pmf_eq_one, mul_one]
      _ ≤ B * (1 + ‖H‖) ^ 1 := by
          have := norm_nonneg H
          nlinarith
  -- (1) the left-hand side is a single integral
  have hdiff : (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
      - a * ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ
      = ∫ H : EnergySpace α, (gibbs_average_n_det (α := α) (n := m) H
          (fun σs => H (σs i) * f σs)
          - a * gibbs_average_n_det (α := α) (n := m) H f) ∂μ := by
    rw [MeasureTheory.integral_sub hI1 (hI2.const_mul a), MeasureTheory.integral_const_mul]
  -- (2) the pointwise bound, by averaging out the `i`-th replica
  have hptwise : ∀ H : EnergySpace α,
      |gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs)
        - a * gibbs_average_n_det (α := α) (n := m) H f| ≤ B * W H := by
    intro H
    have hEq : gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs)
        - a * gibbs_average_n_det (α := α) (n := m) H f
        = gibbs_average_n_det (α := α) (n := m) H (fun σs => (H (σs i) - a) * f σs) := by
      simp only [gibbs_average_n_det, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun σs _ => by ring
    rw [hEq]
    have hstep : |gibbs_average_n_det (α := α) (n := m) H (fun σs => (H (σs i) - a) * f σs)|
        ≤ ∑ σs : ReplicaSpace (α := α) m,
            |(H (σs i) - a) * f σs| * ∏ l, gibbs_pmf (α := α) H (σs l) := by
      rw [gibbs_average_n_det]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun σs _ => ?_))
      rw [abs_mul,
        abs_of_nonneg (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (α := α) H (σs l))]
    refine le_trans hstep ?_
    calc (∑ σs : ReplicaSpace (α := α) m,
            |(H (σs i) - a) * f σs| * ∏ l, gibbs_pmf (α := α) H (σs l))
        ≤ ∑ σs : ReplicaSpace (α := α) m,
            (B * |H (σs i) - a|) * ∏ l, gibbs_pmf (α := α) H (σs l) := by
          refine Finset.sum_le_sum fun σs _ => ?_
          refine mul_le_mul_of_nonneg_right ?_
            (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (α := α) H (σs l))
          rw [abs_mul, mul_comm B]
          exact mul_le_mul_of_nonneg_left (hB σs) (abs_nonneg _)
      _ = B * gibbs_average_n_det (α := α) (n := m) H (fun σs => |H (σs i) - a|) := by
          rw [gibbs_average_n_det, Finset.mul_sum]
          exact Finset.sum_congr rfl fun σs _ => by ring
      _ = B * W H := by
          rw [gibbs_average_n_det_eval (α := α) m H (fun σ => |H σ - a|) i, hW]
          exact congrArg (fun t => B * t) (Finset.sum_congr rfl fun σ _ => mul_comm _ _)
  -- (3) integrate the pointwise bound
  have hbound : |∫ H : EnergySpace α, (gibbs_average_n_det (α := α) (n := m) H
          (fun σs => H (σs i) * f σs)
        - a * gibbs_average_n_det (α := α) (n := m) H f) ∂μ|
      ≤ B * ∫ H : EnergySpace α, W H ∂μ := by
    calc |∫ H : EnergySpace α, (gibbs_average_n_det (α := α) (n := m) H
            (fun σs => H (σs i) * f σs)
          - a * gibbs_average_n_det (α := α) (n := m) H f) ∂μ|
        ≤ ∫ H : EnergySpace α, ‖gibbs_average_n_det (α := α) (n := m) H
            (fun σs => H (σs i) * f σs)
          - a * gibbs_average_n_det (α := α) (n := m) H f‖ ∂μ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ)
            (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
              (fun σs => H (σs i) * f σs)
              - a * gibbs_average_n_det (α := α) (n := m) H f)
      _ ≤ ∫ H : EnergySpace α, B * W H ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hWint.const_mul B)
            (Filter.Eventually.of_forall fun H => by
              simpa [Real.norm_eq_abs] using hptwise H)
      _ = B * ∫ H : EnergySpace α, W H ∂μ := MeasureTheory.integral_const_mul _ _
  -- (4) Cauchy–Schwarz twice
  have hWsq : ∀ H : EnergySpace α, (W H) ^ 2 ≤ V H := fun H => by
    simpa [hW, hV] using sq_sum_gibbs_pmf_mul_abs_le (α := α) H (fun σ => H σ - a)
  have hjensen : (∫ H : EnergySpace α, W H ∂μ) ^ 2 ≤ ∫ H : EnergySpace α, V H ∂μ := by
    have hvar := ProbabilityTheory.variance_nonneg W μ
    rw [ProbabilityTheory.variance_eq_sub hWLp] at hvar
    have h1 : (∫ H : EnergySpace α, W H ∂μ) ^ 2 ≤ ∫ H : EnergySpace α, (W H) ^ 2 ∂μ := by
      simpa using hvar
    have h2 : (∫ H : EnergySpace α, (W H) ^ 2 ∂μ) ≤ ∫ H : EnergySpace α, V H ∂μ :=
      integral_mono (hWLp.integrable_sq) hVint hWsq
    linarith
  have hWnn' : 0 ≤ ∫ H : EnergySpace α, W H ∂μ := integral_nonneg fun H => hWnn H
  have hsqrt : (∫ H : EnergySpace α, W H ∂μ)
      ≤ Real.sqrt (∫ H : EnergySpace α, V H ∂μ) := by
    calc (∫ H : EnergySpace α, W H ∂μ)
        = Real.sqrt ((∫ H : EnergySpace α, W H ∂μ) ^ 2) := (Real.sqrt_sq hWnn').symm
      _ ≤ Real.sqrt (∫ H : EnergySpace α, V H ∂μ) := Real.sqrt_le_sqrt hjensen
  rw [hdiff]
  exact le_trans hbound (mul_le_mul_of_nonneg_left hsqrt hB0)

/-- **Ghirlanda–Guerra with an explicit error term.** For a centered Gaussian Hamiltonian whose
covariance kernel has constant diagonal `c σ σ = d` — the case of every mixed `p`-spin model — the
Ghirlanda–Guerra combination of a test function `f` of `m` replicas bounded by `B` obeys

`|m 𝔼⟨f c(σⁱ, σ^{m+1})⟩ - 𝔼⟨f⟩ 𝔼⟨c₁₂⟩ - ∑_{l ≠ i} 𝔼⟨f c(σⁱ, σˡ)⟩| ≤ B √(𝔼⟨(H - 𝔼⟨H⟩)²⟩)`.

This is an exact finite-volume statement: `FiniteGibbs.ghirlandaGuerra_defect` identifies the
left-hand side with the energy–observable covariance, and
`FiniteGibbs.abs_integral_gibbs_average_energy_mul_sub_le` bounds that covariance by the energy
fluctuation. The identities hold in the limit exactly when the energy self-averages, and the rate
is the rate at which the fluctuation is `o(N²)`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §12.2. -/
theorem ghirlandaGuerra_error_le
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) {B : ℝ} (hB : ∀ σs, |f σs| ≤ B) :
    |(m : ℝ) * (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs * freshCov μ H (σs i)) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
        - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs
                * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) ∂μ|
      ≤ B * Real.sqrt (∫ H : EnergySpace α,
          (∑ σ : α, gibbs_pmf (α := α) H σ
            * (H σ - ∫ H' : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H' (fun τs => H' (τs 0)) ∂μ) ^ 2) ∂μ) := by
  rw [ghirlandaGuerra_defect (μ := μ) hmean0 hdiag m f i]
  have h := abs_integral_gibbs_average_energy_mul_sub_le (μ := μ) m f i hB
    (∫ H' : EnergySpace α,
      gibbs_average_n_det (α := α) (n := 1) H' (fun τs => H' (τs 0)) ∂μ)
  rw [mul_comm (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)]
  exact h

end

end FiniteGibbs

end SpinGlass
