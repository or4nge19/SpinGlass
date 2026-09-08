/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Cauchy–Schwarz against the constant function

Mathlib proves Hölder's inequality for `lintegral` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) and has
the Cauchy–Schwarz inequality inside the Hilbert space `L²`, but it does not record the elementary
consequence one actually reaches for:

`(∫ f dμ)² ≤ μ(univ) · ∫ f² dμ`

for a finite measure — Cauchy–Schwarz against the constant function `1`. For a probability measure
this is `(𝔼X)² ≤ 𝔼X²`; on an interval of length `b - a` it is `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`, the
step that converts an `L²` bound on a fluctuation into an `L¹` bound.

The proof is the discriminant argument: `0 ≤ ∫ (f - t)² dμ` for every real `t`, evaluated at
`t = (∫ f)/μ(univ)`.

## Main statements

- `MeasureTheory.sq_integral_le_measureReal_univ_mul_integral_sq`.
- `MeasureTheory.integral_le_sqrt_measureReal_univ_mul_integral_sq` — the square-root form.
- `MeasureTheory.integral_abs_le_sqrt_measureReal_univ_mul_integral_sq`.
- `intervalIntegral.sq_integral_le_mul_integral_sq`,
  `intervalIntegral.integral_le_sqrt_mul_integral_sq` — the interval forms.
-/

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}

/-- **Cauchy–Schwarz against the constant function.** For a finite measure,
`(∫ f)² ≤ μ(univ) · ∫ f²`. -/
theorem sq_integral_le_measureReal_univ_mul_integral_sq (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  have hI : Integrable f μ := hf.integrable (by norm_num)
  have hQ : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  -- For every `t`, expanding `0 ≤ ∫ (f - t)²` gives a quadratic in `t` with nonnegative values.
  have hquad : ∀ t : ℝ, 0 ≤ ((∫ x, f x ^ 2 ∂μ) - 2 * t * (∫ x, f x ∂μ))
      + (μ.real Set.univ) * t ^ 2 := by
    intro t
    have hpt : ∀ x, (f x - t) ^ 2 = (f x ^ 2 - 2 * t * f x) + t ^ 2 := fun x => by ring
    have hI1 : Integrable (fun x => f x ^ 2 - 2 * t * f x) μ := hQ.sub (hI.const_mul (2 * t))
    have hcalc : (∫ x, (f x - t) ^ 2 ∂μ)
        = ((∫ x, f x ^ 2 ∂μ) - 2 * t * (∫ x, f x ∂μ)) + (μ.real Set.univ) * t ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_add hI1 (integrable_const (t ^ 2)),
        integral_sub hQ (hI.const_mul (2 * t)), integral_const_mul, integral_const, smul_eq_mul]
    have hnn := integral_nonneg (μ := μ) (f := fun x => (f x - t) ^ 2) fun x => sq_nonneg _
    rwa [hcalc] at hnn
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := Set.univ)) with hm0 | hmpos
  · -- A finite measure of total mass `0` is the zero measure.
    have hzero : μ = 0 := by
      refine Measure.measure_univ_eq_zero.1 ?_
      have h0 : μ.real Set.univ = 0 := hm0.symm
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff,
        or_iff_left (measure_ne_top μ Set.univ)] at h0
    simp [hzero]
  · set m : ℝ := μ.real Set.univ with hm
    set I : ℝ := ∫ x, f x ∂μ with hIdef
    set Q : ℝ := ∫ x, f x ^ 2 ∂μ with hQdef
    have h := hquad (I / m)
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hkey : (Q - 2 * (I / m) * I) + m * (I / m) ^ 2 = Q - I ^ 2 / m := by
      field_simp
      ring
    rw [hkey] at h
    have hdiv : I ^ 2 / m ≤ Q := by linarith
    rw [div_le_iff₀ hmpos] at hdiv
    calc I ^ 2 ≤ Q * m := hdiv
      _ = m * Q := mul_comm _ _

/-- The square-root form of Cauchy–Schwarz against the constant function, for a nonnegative
integrand. -/
theorem integral_le_sqrt_measureReal_univ_mul_integral_sq (hf : MemLp f 2 μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ Real.sqrt (μ.real Set.univ * ∫ x, f x ^ 2 ∂μ) := by
  have hnn : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hf0
  calc (∫ x, f x ∂μ) = Real.sqrt ((∫ x, f x ∂μ) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (μ.real Set.univ * ∫ x, f x ^ 2 ∂μ) :=
        Real.sqrt_le_sqrt (sq_integral_le_measureReal_univ_mul_integral_sq hf)

/-- Cauchy–Schwarz against the constant function, for `|f|`. -/
theorem integral_abs_le_sqrt_measureReal_univ_mul_integral_sq (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (μ.real Set.univ * ∫ x, f x ^ 2 ∂μ) := by
  have habs : MemLp (fun x => |f x|) 2 μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hsq : ∀ x, |f x| ^ 2 = f x ^ 2 := fun x => sq_abs (f x)
  have h := integral_le_sqrt_measureReal_univ_mul_integral_sq habs
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
  rwa [integral_congr_ae (Filter.Eventually.of_forall hsq)] at h

end MeasureTheory

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Cauchy–Schwarz on an interval**: `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
theorem sq_integral_le_mul_integral_sq (hab : a ≤ b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hres : ((volume.restrict (Set.Ioc a b)).real Set.univ) = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
  have h := MeasureTheory.sq_integral_le_measureReal_univ_mul_integral_sq
    (μ := volume.restrict (Set.Ioc a b)) hf
  rw [hres] at h
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact h

/-- The square-root form of Cauchy–Schwarz on an interval, for a nonnegative integrand. -/
theorem integral_le_sqrt_mul_integral_sq (hab : a ≤ b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hf0 : ∀ x ∈ Set.Ioc a b, 0 ≤ f x) :
    (∫ x in a..b, f x) ≤ Real.sqrt ((b - a) * ∫ x in a..b, f x ^ 2) := by
  have hnn : 0 ≤ ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hf0 x hx
  calc (∫ x in a..b, f x) = Real.sqrt ((∫ x in a..b, f x) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((b - a) * ∫ x in a..b, f x ^ 2) :=
        Real.sqrt_le_sqrt (sq_integral_le_mul_integral_sq hab hf)

end intervalIntegral
