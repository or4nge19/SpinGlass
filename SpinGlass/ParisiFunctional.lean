/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ReplicaSymmetricBound
import Common.Mathlib.Probability.PointProcess.CascadeIdentities
import Common.Mathlib.Probability.PointProcess.CascadeProduct
import Common.Mathlib.Algebra.BigOperators.SummationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Parisi functional

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.4, Eqs. (14.69)–(14.88). For a
covariance profile `ξ` (a mixed `p`-spin model, `N⁻¹ 𝔼 H(σ¹)H(σ²) = ξ(R₁₂)`), an external
field `h`, and the **functional order parameter** given by the sequences
`0 = m₀ < m₁ < ⋯ < m_k < 1 = m_{k+1}` (14.69) and `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`
(14.70), the Parisi functional is

`𝒫(m, q) = log 2 + X₀ - (1/2) ∑_{1 ≤ p ≤ k+1} m_p (θ(q_{p+1}) - θ(q_p))`, (14.88)

where `θ(x) = x ξ'(x) - ξ(x)` (14.60) and `X₀ = 𝔼 X₁` is computed by the recursion (14.83):
`X_{k+2} = log cosh (h + z₀ + ⋯ + z_{k+1})`, `X_p = (1/m_p) log 𝔼_p exp (m_p X_{p+1})`, with
independent Gaussians `𝔼 z_p² = ξ'(q_{p+1}) - ξ'(q_p)` (14.72). The recursion is
`ProbabilityTheory.parisiRec` — the same recursion that computes averages over Poisson–Dirichlet
cascades (Theorem 14.2.1) — applied to Gaussian marks. The functional is therefore not a new
object but a specialization of the cascade theory; this is what makes Guerra's broken
replica-symmetry bound (Theorem 14.4.3) a statement about cascades.

## Main definitions

- `SpinGlass.parisiTheta`, `SpinGlass.qExt`, `SpinGlass.parisiVar`, `SpinGlass.parisiMarks`:
  `θ`, the extended sequence `(q_r)`, the variances (14.72), and the Gaussian marks.
- `SpinGlass.parisiRecGauss`, `SpinGlass.parisiX₀`: `X₁(z₀)` and `X₀ = 𝔼 X₁`, for a general
  one-site function in place of `log cosh (h + ·)`.
- `SpinGlass.parisiFunctional`: (14.88).

## Main statements

- `SpinGlass.integral_cosh_add_gaussianReal`: `𝔼 cosh (a + z) = cosh a · exp (v/2)`.
- `SpinGlass.parisiRecGauss_logCosh`: **(14.84)** — the last level, which has `m_{k+1} = 1`,
  contributes exactly `(ξ'(1) - ξ'(q_{k+1}))/2`, so `X₁ = (ξ'(1) - ξ'(q_{k+1}))/2 + X'₁`. This is
  `ProbabilityTheory.cascadeRec_snoc_one` for Gaussian marks.
- `SpinGlass.parisiFunctional_zero`: the functional at `k = 0` in closed form.
- `SpinGlass.parisiFunctional_skCovXi_zero`: **for the SK model, the `k = 0` Parisi functional is
  the replica-symmetric expression** `𝔼 log (2 cosh (β√q z + h)) + (β²/4)(1 - q)²`; hence
  `SpinGlass.skFreeEnergyLimit_le_parisiFunctional_zero`: Guerra's replica-symmetric bound
  (Vol. I, Theorem 1.3.7) is the case `k = 0` of the Parisi bound.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

/-! ### The functional order parameter -/

/-- Talagrand's `θ(x) = x ξ'(x) - ξ(x)`, (14.60). -/
def parisiTheta (ξ : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv ξ x - ξ x

/-- The extended sequence `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1` of (14.70), indexed by `ℕ`
(`q_r = 1` for `r ≥ k + 2`), from the free parameters `q₁, …, q_{k+1}`. -/
def qExt {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else if h : r - 1 < k + 1 then qs ⟨r - 1, h⟩ else 1

@[simp] lemma qExt_zero {k : ℕ} (qs : Fin (k + 1) → ℝ) : qExt qs 0 = 0 := by simp [qExt]

lemma qExt_succ_of_lt {k : ℕ} (qs : Fin (k + 1) → ℝ) {r : ℕ} (h : r < k + 1) :
    qExt qs (r + 1) = qs ⟨r, h⟩ := by simp [qExt, h]

lemma qExt_of_le {k : ℕ} (qs : Fin (k + 1) → ℝ) {r : ℕ} (h : k + 2 ≤ r) : qExt qs r = 1 := by
  have h0 : r ≠ 0 := by omega
  have h1 : ¬ r - 1 < k + 1 := by omega
  simp [qExt, h0, h1]

/-- **The extended sequence is nondecreasing** on `0 ≤ r ≤ k + 2` when `q` is nondecreasing
in `[0, 1]`: this is Talagrand's (14.70). -/
lemma qExt_le_succ {k : ℕ} {qs : Fin (k + 1) → ℝ} (hmono : Monotone qs) (hq0 : 0 ≤ qs 0)
    (hq1 : qs (Fin.last k) ≤ 1) {r : ℕ} (hr : r ≤ k + 1) : qExt qs r ≤ qExt qs (r + 1) := by
  rcases r with _ | j
  · rw [qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)]
    exact hq0
  · rw [qExt_succ_of_lt qs (by omega : j < k + 1)]
    rcases Nat.lt_or_ge (j + 1) (k + 1) with hj | hj
    · rw [qExt_succ_of_lt qs hj]
      exact hmono (Fin.mk_le_mk.2 (by omega))
    · rw [qExt_of_le qs (by omega : k + 2 ≤ j + 1 + 1)]
      exact (hmono (Fin.le_last _)).trans hq1

/-- The extended sequence takes its values in `[0, 1]`. -/
lemma qExt_mem_Icc {k : ℕ} {qs : Fin (k + 1) → ℝ} (hmono : Monotone qs) (hq0 : 0 ≤ qs 0)
    (hq1 : qs (Fin.last k) ≤ 1) (r : ℕ) : qExt qs r ∈ Set.Icc (0 : ℝ) 1 := by
  rcases r with _ | j
  · simp
  · rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · rw [qExt_succ_of_lt qs hj]
      exact ⟨hq0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hq1⟩
    · rw [qExt_of_le qs (by omega : k + 2 ≤ j + 1)]
      exact ⟨zero_le_one, le_refl 1⟩

/-- The variance `𝔼 z_p² = ξ'(q_{p+1}) - ξ'(q_p)` of the Gaussian `z_p`, `0 ≤ p ≤ k + 1`,
(14.72) and (14.83), clamped at `0` so that it is a variance for every profile (it is exact when
`ξ'` is nondecreasing on `[0, 1]`, e.g. for every mixed `p`-spin profile). -/
def parisiVar (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : ℕ) : ℝ≥0 :=
  Real.toNNReal (deriv ξ (qExt qs (p + 1)) - deriv ξ (qExt qs p))

/-- The Gaussian marks `z₁, …, z_{k+1}` of the recursion, `z_p ∼ N(0, ξ'(q_{p+1}) - ξ'(q_p))`. -/
def parisiMarks (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) : Measure ℝ :=
  gaussianReal 0 (parisiVar ξ qs (p.val + 1))

instance (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    IsProbabilityMeasure (parisiMarks ξ qs p) := by
  unfold parisiMarks; infer_instance

/-- The marks split as `(z₁, …, z_k)` and the last one `z_{k+1}`. -/
lemma parisiMarks_eq_snoc (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    parisiMarks ξ qs = Fin.snoc (α := fun _ => Measure ℝ)
      (fun p : Fin k => parisiMarks ξ qs p.castSucc) (gaussianReal 0 (parisiVar ξ qs (k + 1))) := by
  funext p
  refine Fin.lastCases ?_ (fun q => ?_) p
  · rw [Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc]

/-! ### The recursion -/

/-- **`X₁` as a function of `z₀`**: the recursion (14.83), `X_p = (1/m_p) log 𝔼_p exp (m_p X_{p+1})`
for `1 ≤ p ≤ k+1` with `m_{k+1} = 1`, started from `X_{k+2} = F (z₀ + z₁ + ⋯ + z_{k+1})`, for a
general one-site function `F`; Talagrand's case is `F = log cosh (h + ·)`. -/
def parisiRecGauss (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (F : ℝ → ℝ)
    (z₀ : ℝ) : ℝ :=
  parisiRec (k + 1) (Fin.snoc ms 1) (parisiMarks ξ qs) (fun x => F (z₀ + ∑ p, x p))

/-- **`X₀ = 𝔼 X₁`**, (14.84): the expectation over `z₀ ∼ N(0, ξ'(q₁) - ξ'(0))`. -/
def parisiX₀ (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ z₀, parisiRecGauss ξ ms qs F z₀ ∂gaussianReal 0 (parisiVar ξ qs 0)

/-- **The Parisi functional** (14.88),
`𝒫(m, q) = log 2 + X₀ - (1/2) ∑_{1 ≤ p ≤ k+1} m_p (θ(q_{p+1}) - θ(q_p))`, with `m_{k+1} = 1`
and `q_{k+2} = 1` (`ProbabilityTheory.mExt`, `SpinGlass.qExt`), for the Ising one-site function
`log cosh (h + ·)`. -/
def parisiFunctional (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ :=
  Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
    - (1 / 2) * ∑ p ∈ Finset.range (k + 1),
        mExt ms (p + 1) * (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))

/-! ### Talagrand's second form (14.403) -/

/-- **The Parisi functional in Talagrand's form (14.403)**:
`𝒫_k(m, q) = log 2 + X₀ + (1/2) ∑_{1 ≤ p ≤ k+1} θ(q_p)(m_p − m_{p−1}) − θ(1)/2`.
This is the form in which `𝒫_k` visibly depends only on the measure
`μ = ∑_{1 ≤ p ≤ k+1} (m_p − m_{p−1}) δ_{q_p}` of §14.11; it is equivalent to the definition
(14.89) by summation by parts, using `m₀ = 0`, `m_{k+1} = 1` and `q_{k+2} = 1`. -/
theorem parisiFunctional_eq_theta_sum (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) :
    parisiFunctional ξ h ms qs
      = Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
        + (1 / 2) * ∑ p ∈ Finset.range (k + 1),
            parisiTheta ξ (qExt qs (p + 1)) * (mExt ms (p + 1) - mExt ms p)
        - (1 / 2) * parisiTheta ξ 1 := by
  set A : ℕ → ℝ := fun j => parisiTheta ξ (qExt qs j) with hA
  set B : ℕ → ℝ := fun j => mExt ms j with hB
  have hleib := Finset.sum_range_mul_sub_add_sub_mul B (fun j => A (j + 1)) (k + 1)
  have hB0 : B 0 = 0 := mExt_zero ms
  have hBk : B (k + 1) = 1 := mExt_eq_one_of_le ms (le_refl (k + 1))
  have hAk : A (k + 1 + 1) = parisiTheta ξ 1 := by
    rw [hA]
    simp only
    rw [qExt_of_le qs (by omega : k + 2 ≤ k + 1 + 1)]
  rw [hBk, hAk, hB0, one_mul, zero_mul, sub_zero, Finset.sum_add_distrib] at hleib
  have h1 : ∑ p ∈ Finset.range (k + 1), mExt ms (p + 1)
      * (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))
      = ∑ i ∈ Finset.range (k + 1), B (i + 1) * (A (i + 1 + 1) - A (i + 1)) := rfl
  have h2 : ∑ p ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (p + 1))
      * (mExt ms (p + 1) - mExt ms p)
      = ∑ i ∈ Finset.range (k + 1), (B (i + 1) - B i) * A (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA, hB]
    ring
  unfold parisiFunctional
  rw [h1, h2]
  linarith

/-! ### Gaussian averages of `cosh` and `log cosh` -/

/-- `∫ exp (t z) dN(0,v)(z) = exp (v t²/2)`. -/
lemma integral_exp_mul_gaussianReal_zero (v : ℝ≥0) (t : ℝ) :
    ∫ z, Real.exp (t * z) ∂gaussianReal 0 v = Real.exp (v * t ^ 2 / 2) := by
  have := mgf_gaussianReal (p := gaussianReal 0 v) (X := id) (μ := 0) (v := v) Measure.map_id t
  simpa [mgf] using this

lemma cosh_add_eq_exp (a z : ℝ) :
    Real.cosh (a + z) = (Real.exp a * Real.exp (1 * z) + Real.exp (-a) * Real.exp (-1 * z)) / 2 := by
  rw [Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
  ring_nf

lemma integrable_cosh_add_gaussianReal (a : ℝ) (v : ℝ≥0) :
    Integrable (fun z => Real.cosh (a + z)) (gaussianReal 0 v) := by
  simp_rw [cosh_add_eq_exp]
  exact (((integrable_exp_mul_gaussianReal 1).const_mul _).add
    ((integrable_exp_mul_gaussianReal (-1)).const_mul _)).div_const 2

/-- **`𝔼 cosh (a + z) = cosh a · exp (v/2)`** for `z ∼ N(0, v)`. -/
theorem integral_cosh_add_gaussianReal (a : ℝ) (v : ℝ≥0) :
    ∫ z, Real.cosh (a + z) ∂gaussianReal 0 v = Real.cosh a * Real.exp (v / 2) := by
  simp_rw [cosh_add_eq_exp]
  rw [integral_div, integral_add ((integrable_exp_mul_gaussianReal 1).const_mul _)
    ((integrable_exp_mul_gaussianReal (-1)).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_mul_gaussianReal_zero, integral_exp_mul_gaussianReal_zero, Real.cosh_eq]
  simp only [one_pow, neg_one_sq, mul_one]
  ring

/-- The `ℝ≥0∞` form of `integral_cosh_add_gaussianReal`. -/
theorem lintegral_ofReal_cosh_add_gaussianReal (a : ℝ) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal (Real.cosh (a + z)) ∂gaussianReal 0 v
      = ENNReal.ofReal (Real.exp (v / 2)) * ENNReal.ofReal (Real.cosh a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cosh_add_gaussianReal a v)
    (Filter.Eventually.of_forall fun z => (Real.cosh_pos _).le), integral_cosh_add_gaussianReal,
    ENNReal.ofReal_mul (Real.cosh_pos _).le, mul_comm]

/-- `0 ≤ log cosh y ≤ |y|`. -/
lemma log_cosh_nonneg (y : ℝ) : 0 ≤ Real.log (Real.cosh y) :=
  Real.log_nonneg (Real.one_le_cosh y)

lemma log_cosh_le_abs (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
  have hc : Real.cosh y ≤ Real.exp |y| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
    have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.2 (neg_le_abs y)
    linarith
  calc Real.log (Real.cosh y) ≤ Real.log (Real.exp |y|) :=
        Real.log_le_log (Real.cosh_pos y) hc
    _ = |y| := Real.log_exp _

lemma continuous_log_cosh : Continuous fun y : ℝ => Real.log (Real.cosh y) :=
  Real.continuousOn_log.comp_continuous Real.continuous_cosh fun y => (Real.cosh_pos y).ne'

/-- `log cosh ∘ g` is integrable as soon as `g` is. -/
lemma integrable_log_cosh_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg : Integrable g μ) : Integrable (fun ω => Real.log (Real.cosh (g ω))) μ := by
  refine hg.norm.mono' (continuous_log_cosh.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg _), Real.norm_eq_abs]
  exact log_cosh_le_abs _

lemma integrable_id_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun z => z) (gaussianReal μ v) := by
  have := memLp_id_gaussianReal (μ := μ) (v := v) 1
  rw [ENNReal.coe_one] at this
  exact memLp_one_iff_integrable.1 this

lemma integrable_log_cosh_add_gaussianReal (a : ℝ) (v : ℝ≥0) :
    Integrable (fun z => Real.log (Real.cosh (a + z))) (gaussianReal 0 v) :=
  integrable_log_cosh_comp ((integrable_const a).add (integrable_id_gaussianReal 0 v))

/-! ### Absorbing the last level, (14.84) -/

/-- **(14.84)**: with `m_{k+1} = 1`, the last level of the recursion contributes exactly
`(ξ'(1) - ξ'(q_{k+1}))/2`:
`X₁(z₀) = (ξ'(1) - ξ'(q_{k+1}))/2 + X'₁(z₀)`, where `X'₁` is the recursion over the levels
`1, …, k` only, started from `log cosh (h + z₀ + z₁ + ⋯ + z_k)`. -/
theorem parisiRecGauss_logCosh (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (z₀ : ℝ) :
    parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) z₀
      = (parisiVar ξ qs (k + 1) : ℝ) / 2
        + parisiRec k ms (fun p => parisiMarks ξ qs p.castSucc)
            (fun x => Real.log (Real.cosh (h + z₀ + ∑ p, x p))) := by
  set G : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.cosh (h + z₀ + a)) with hGdef
  have hG : Measurable G :=
    ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp (measurable_const_add _))
  have hC : ∀ a, ∫⁻ z, G (a + z) ∂gaussianReal 0 (parisiVar ξ qs (k + 1))
      = ENNReal.ofReal (Real.exp ((parisiVar ξ qs (k + 1) : ℝ) / 2)) * G a := by
    intro a
    simp only [hGdef, ← add_assoc]
    exact lintegral_ofReal_cosh_add_gaussianReal _ _
  have hCle : ∀ (p : Fin k) a, ∫⁻ z, G (a + z) ∂parisiMarks ξ qs p.castSucc
      ≤ ENNReal.ofReal (Real.exp ((parisiVar ξ qs (p.val + 1) : ℝ) / 2)) * G a := by
    intro p a
    simp only [hGdef, ← add_assoc, parisiMarks, Fin.val_castSucc]
    exact (lintegral_ofReal_cosh_add_gaussianReal _ _).le
  have hfin : cascadeRec k ms (fun p => parisiMarks ξ qs p.castSucc) (fun x => G (∑ p, x p)) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) (cascadeRec_sum_le k ms _ hG hpos hle hCle)
  have hRpos : 0 < cascadeRec k ms (fun p => parisiMarks ξ qs p.castSucc) (fun x => G (∑ p, x p)) :=
    cascadeRec_pos k _ _ (hG.comp (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
      (fun _ => ENNReal.ofReal_pos.2 (Real.cosh_pos _)) hpos
  have hkey := cascadeRec_snoc_one k ms (fun p => parisiMarks ξ qs p.castSucc) hG hpos hC
  have hfun : (fun x : Fin (k + 1) → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h + (z₀ + ∑ p, x p))))))
      = fun x => G (∑ p, x p) := by
    funext x
    simp only [hGdef, Real.exp_log (Real.cosh_pos _), add_assoc]
  have hfun' : (fun x : Fin k → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h + z₀ + ∑ p, x p)))))
      = fun x => G (∑ p, x p) := by
    funext x
    simp only [hGdef, Real.exp_log (Real.cosh_pos _)]
  rw [← parisiMarks_eq_snoc ξ qs] at hkey
  have hC0 : (ENNReal.ofReal (Real.exp ((parisiVar ξ qs (k + 1) : ℝ) / 2))).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    exact (Real.exp_pos _).ne'
  simp only [parisiRecGauss, parisiRec]
  rw [hfun, hfun', hkey, ENNReal.toReal_mul, Real.log_mul hC0 (ENNReal.toReal_pos hRpos.ne' hfin).ne',
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

/-! ### The replica-symmetric case `k = 0` -/

/-- **`X₀` at `k = 0`**: `X₀ = 𝔼 log cosh (h + z₀) + (ξ'(1) - ξ'(q₁))/2`. -/
theorem parisiX₀_logCosh_zero (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin 0 → ℝ) (qs : Fin 1 → ℝ) :
    parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
      = (∫ z, Real.log (Real.cosh (h + z)) ∂gaussianReal 0 (parisiVar ξ qs 0))
        + (parisiVar ξ qs 1 : ℝ) / 2 := by
  unfold parisiX₀
  have hfun : ∀ z₀, parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) z₀
      = (parisiVar ξ qs 1 : ℝ) / 2 + Real.log (Real.cosh (h + z₀)) := by
    intro z₀
    rw [parisiRecGauss_logCosh ξ h ms qs (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) z₀]
    simp
  simp_rw [hfun]
  rw [integral_add (integrable_const _) (integrable_log_cosh_add_gaussianReal h _), integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- **The Parisi functional at `k = 0`**, in closed form:
`𝒫 = log 2 + 𝔼 log cosh (h + z₀) + (ξ'(1) - ξ'(q₁))/2 - (θ(1) - θ(q₁))/2`,
`z₀ ∼ N(0, ξ'(q₁) - ξ'(0))`. -/
theorem parisiFunctional_zero (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin 0 → ℝ) (qs : Fin 1 → ℝ) :
    parisiFunctional ξ h ms qs
      = Real.log 2 + (∫ z, Real.log (Real.cosh (h + z)) ∂gaussianReal 0 (parisiVar ξ qs 0))
        + (parisiVar ξ qs 1 : ℝ) / 2 - (1 / 2) * (parisiTheta ξ 1 - parisiTheta ξ (qs 0)) := by
  unfold parisiFunctional
  rw [parisiX₀_logCosh_zero, Finset.sum_range_one, mExt_of_zero_lt (by norm_num),
    qExt_of_le qs (by norm_num), qExt_succ_of_lt qs zero_lt_one, one_mul, Fin.zero_eta]
  ring

/-! ### The Sherrington–Kirkpatrick model: `k = 0` is the replica-symmetric bound -/

lemma deriv_skCovXi (β x : ℝ) : deriv (skCovXi β) x = β ^ 2 * x := by
  have : HasDerivAt (skCovXi β) (β ^ 2 * ((2 : ℕ) * x ^ (2 - 1)) / 2) x := by
    show HasDerivAt (fun x => β ^ 2 * x ^ 2 / 2) _ x
    exact ((hasDerivAt_pow 2 x).const_mul _).div_const 2
  rw [this.deriv]
  norm_num
  ring

lemma differentiable_skCovXi (β : ℝ) : Differentiable ℝ (skCovXi β) := by
  unfold skCovXi
  fun_prop

/-- The SK profile is convex on all of `ℝ`. -/
lemma convexOn_univ_skCovXi (β : ℝ) : ConvexOn ℝ Set.univ (skCovXi β) := by
  refine Monotone.convexOn_univ_of_deriv (differentiable_skCovXi β) ?_
  rw [funext (deriv_skCovXi β)]
  exact fun a b hab => by nlinarith [sq_nonneg β]

@[simp] lemma deriv_skCovXi_zero (β : ℝ) : deriv (skCovXi β) 0 = 0 := by
  rw [deriv_skCovXi]
  ring

lemma parisiTheta_skCovXi (β x : ℝ) : parisiTheta (skCovXi β) x = β ^ 2 * x ^ 2 / 2 := by
  simp only [parisiTheta, deriv_skCovXi, skCovXi]
  ring

lemma parisiVar_skCovXi_zero (β q : ℝ) (hq0 : 0 ≤ q) :
    (parisiVar (skCovXi β) ![q] 0 : ℝ) = β ^ 2 * q := by
  simp only [parisiVar, qExt_succ_of_lt _ zero_lt_one, qExt_zero, deriv_skCovXi, mul_zero,
    sub_zero, Fin.zero_eta, Matrix.cons_val_zero]
  exact Real.coe_toNNReal _ (by positivity)

lemma parisiVar_skCovXi_one (β q : ℝ) (hq1 : q ≤ 1) :
    (parisiVar (skCovXi β) ![q] 1 : ℝ) = β ^ 2 * (1 - q) := by
  simp only [parisiVar, qExt_of_le _ le_rfl, qExt_succ_of_lt _ zero_lt_one, deriv_skCovXi,
    mul_one, Fin.zero_eta, Matrix.cons_val_zero]
  have : β ^ 2 * q ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hq1 (sq_nonneg β)
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

/-- The Gaussian `N(0, β² q)` is the image of `N(0, 1)` under `z ↦ β √q z`. -/
lemma integral_gaussianReal_sq_eq (β q : ℝ) (hq0 : 0 ≤ q) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ z, f z ∂gaussianReal 0 (Real.toNNReal (β ^ 2 * q))
      = ∫ z, f (β * Real.sqrt q * z) ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (· * (β * Real.sqrt q))
      = gaussianReal 0 (Real.toNNReal (β ^ 2 * q)) := by
    rw [gaussianReal_map_mul_const, mul_zero]
    congr 1
    ext
    simp [mul_pow, Real.sq_sqrt hq0, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq0)]
  rw [← hmap, integral_map (measurable_mul_const _).aemeasurable hf.aestronglyMeasurable]
  simp_rw [mul_comm _ (β * Real.sqrt q)]

/-- **For the SK model, the Parisi functional at `k = 0` is the replica-symmetric expression**
`𝔼 log (2 cosh (β√q z + h)) + (β²/4)(1 - q)²` of Guerra's bound, Vol. I, Theorem 1.3.7. -/
theorem parisiFunctional_skCovXi_zero (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    parisiFunctional (skCovXi β) h ![] ![q]
      = (∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂gaussianReal 0 1)
        + β ^ 2 / 4 * (1 - q) ^ 2 := by
  rw [parisiFunctional_zero, parisiVar_skCovXi_one β q hq1, parisiTheta_skCovXi,
    parisiTheta_skCovXi, Matrix.cons_val_zero]
  have hv : parisiVar (skCovXi β) ![q] 0 = Real.toNNReal (β ^ 2 * q) := by
    ext
    rw [parisiVar_skCovXi_zero β q hq0, Real.coe_toNNReal _ (by positivity)]
  rw [hv, integral_gaussianReal_sq_eq β q hq0 (fun z => Real.log (Real.cosh (h + z)))
    (Real.measurable_log.comp (Real.continuous_cosh.measurable.comp (measurable_const_add h)))]
  have hlog : ∀ z, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h))
      = Real.log 2 + Real.log (Real.cosh (h + β * Real.sqrt q * z)) := by
    intro z
    rw [Real.log_mul two_ne_zero (Real.cosh_pos _).ne', add_comm (β * Real.sqrt q * z) h]
  simp_rw [hlog]
  have hint : Integrable (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z)))
      (gaussianReal 0 1) :=
    integrable_log_cosh_comp (g := fun z => h + β * Real.sqrt q * z)
      ((integrable_const h).add ((integrable_id_gaussianReal 0 1).const_mul _))
  rw [integral_add (integrable_const _) hint, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- **Guerra's replica-symmetric bound is the case `k = 0` of the Parisi bound**:
`p(β, h) ≤ 𝒫(∅, (q))` for every `0 ≤ q ≤ 1`. -/
theorem skFreeEnergyLimit_le_parisiFunctional_zero (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    skFreeEnergyLimit β h ≤ parisiFunctional (skCovXi β) h ![] ![q] := by
  rw [parisiFunctional_skCovXi_zero β h q hq0 hq1]
  exact skFreeEnergyLimit_le_rs β q h hq0

end

end SpinGlass
