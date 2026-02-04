import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Talagrand Vol. II: Parisi recursive operator `T_{m,v}`

This file introduces the basic “Gaussian log-mgf smoothing” operator
\[
T_{m,v}(A)(x) = \frac{1}{m}\log \int \exp(m A(x+z)) \, d\gamma_{0,v}(z),
\]
where `γ_{0,v}` is `gaussianReal 0 v`.

The key structural lemma for the Parisi recursion is the semigroup property:
\[
T_{m,v₁}(T_{m,v₂}(A)) = T_{m,v₁+v₂}(A),
\]
which is a direct consequence of Gaussian convolution and Fubini.

This is intentionally stated under **minimal** hypotheses (measurability + uniform boundedness)
so it can be used as a core building block in later Vol. II developments.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal MeasureTheory NNReal

namespace SpinGlass

namespace Parisi

/-! ### Basic boundedness hypothesis -/

/-- A convenient “uniform bound” hypothesis for real functions. -/
def HasUniformBound (A : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x, |A x| ≤ C

lemma hasUniformBound_comp_add {A : ℝ → ℝ} (hA : HasUniformBound A) (x : ℝ) :
    HasUniformBound (fun z => A (x + z)) := by
  rcases hA with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro z
  simpa using hC (x + z)

/-! ### The operator -/

/-- The Parisi recursive operator `T_{m,v}`. -/
noncomputable def T (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / m) * Real.log (∫ z : ℝ, Real.exp (m * A (x + z)) ∂(ProbabilityTheory.gaussianReal (0 : ℝ) v))

lemma integrable_exp_mul_of_measurable_of_hasUniformBound
    {m : ℝ} {v : ℝ≥0} {A : ℝ → ℝ} (hA_meas : Measurable A)
    (hA : HasUniformBound A) (x : ℝ) :
    Integrable (fun z : ℝ => Real.exp (m * A (x + z)))
      (ProbabilityTheory.gaussianReal (0 : ℝ) v) := by
  rcases hA with ⟨C, hC⟩
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (m * A (x + z)))
      (ProbabilityTheory.gaussianReal (0 : ℝ) v) := by
    have : Measurable fun z : ℝ => Real.exp (m * A (x + z)) := by
      have hadd : Measurable fun z : ℝ => x + z := by fun_prop
      have : Measurable fun z : ℝ => A (x + z) := hA_meas.comp hadd
      fun_prop
    exact this.aestronglyMeasurable
  have hbound :
      ∀ z : ℝ, ‖Real.exp (m * A (x + z))‖ ≤ Real.exp (|m| * C) := by
    intro z
    have hAz : |A (x + z)| ≤ C := hC (x + z)
    have hmul : |m * A (x + z)| ≤ |m| * C := by
      -- `|m * a| ≤ |m| * C` from `|a| ≤ C`.
      simpa [abs_mul] using (mul_le_mul_of_nonneg_left hAz (abs_nonneg m))
    have : Real.exp (m * A (x + z)) ≤ Real.exp (|m| * C) := by
      have hle : m * A (x + z) ≤ |m| * C :=
        le_trans (le_abs_self _) hmul
      exact Real.exp_le_exp.mpr hle
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using this
  refine (integrable_const (Real.exp (|m| * C))).mono' hmeas ?_
  refine ae_of_all _ (fun z => ?_)
  simpa using hbound z

/-! ### Semigroup property -/

theorem T_add (m : ℝ) (hm : m ≠ 0) (v₁ v₂ : ℝ≥0) {A : ℝ → ℝ}
    (hA_meas : Measurable A) (hA : HasUniformBound A) :
    T m (v₁ + v₂) A = fun x => T m v₁ (fun y => T m v₂ A y) x := by
  funext x
  let μ₁ : Measure ℝ := ProbabilityTheory.gaussianReal (0 : ℝ) v₁
  let μ₂ : Measure ℝ := ProbabilityTheory.gaussianReal (0 : ℝ) v₂
  have hμ₁ : IsProbabilityMeasure μ₁ := by infer_instance
  have hμ₂ : IsProbabilityMeasure μ₂ := by infer_instance
  let I : ℝ → ℝ := fun t => ∫ z : ℝ, Real.exp (m * A (t + z)) ∂μ₂
  have hI_pos : ∀ t, 0 < I t := by
    intro t
    have hint : Integrable (fun z : ℝ => Real.exp (m * A (t + z))) μ₂ := by
      simpa [μ₂] using
        (integrable_exp_mul_of_measurable_of_hasUniformBound (m := m) (v := v₂) hA_meas hA t)
    haveI : NeZero μ₂ := by
      have hu : μ₂ Set.univ = 1 := by
        simp [μ₂]
      refine ⟨?_⟩
      intro h0
      have h0univ : (μ₂ Set.univ) = 0 := by simp [h0]
      have : (1 : ℝ≥0∞) = 0 := by simp [hu] at h0univ
      exact one_ne_zero this
    simpa [I, μ₂] using (MeasureTheory.integral_exp_pos (μ := μ₂) (f := fun z => m * A (t + z)) hint)
  have hstep :
      (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁)
        = ∫ z : ℝ, I (x + z) ∂μ₁ := by
    have hpoint : ∀ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) = I (x + z) := by
      intro z
      have hpos : 0 < I (x + z) := hI_pos (x + z)
      simp [T, I, μ₂, hm, div_eq_mul_inv, Real.exp_log hpos]
    refine integral_congr_ae ?_
    exact ae_of_all _ hpoint
  have hFubini :
      (∫ z₁ : ℝ, I (x + z₁) ∂μ₁)
        = ∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂) := by
    have hconv : μ₁ ∗ μ₂ = Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ₁.prod μ₂) := by
      rfl
    let F : ℝ × ℝ → ℝ := fun p => Real.exp (m * A (x + (p.1 + p.2)))
    have hF_meas : Measurable F := by
      have : Measurable fun p : ℝ × ℝ => x + (p.1 + p.2) := by fun_prop
      have : Measurable fun p : ℝ × ℝ => A (x + (p.1 + p.2)) := hA_meas.comp this
      fun_prop
    have hF_int : Integrable F (μ₁.prod μ₂) := by
      rcases hA with ⟨C, hC⟩
      have hmeas : AEStronglyMeasurable F (μ₁.prod μ₂) := hF_meas.aestronglyMeasurable
      have hbound :
          ∀ p : ℝ × ℝ, ‖F p‖ ≤ Real.exp (|m| * C) := by
        intro p
        have hAp : |A (x + (p.1 + p.2))| ≤ C := hC (x + (p.1 + p.2))
        have hmul : |m * A (x + (p.1 + p.2))| ≤ |m| * C := by
          simpa [abs_mul] using (mul_le_mul_of_nonneg_left hAp (abs_nonneg m))
        have : Real.exp (m * A (x + (p.1 + p.2))) ≤ Real.exp (|m| * C) := by
          have hle : m * A (x + (p.1 + p.2)) ≤ |m| * C :=
            le_trans (le_abs_self _) hmul
          exact Real.exp_le_exp.mpr hle
        simpa [F, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using this
      refine (integrable_const (Real.exp (|m| * C))).mono' hmeas ?_
      exact ae_of_all _ (fun p => hbound p)
    have hleft :
        (∫ z₁ : ℝ, I (x + z₁) ∂μ₁)
          = ∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂) := by
      have hleft1 :
          (∫ z₁ : ℝ, I (x + z₁) ∂μ₁)
            = ∫ z₁ : ℝ, ∫ z₂ : ℝ, Real.exp (m * A (x + z₁ + z₂)) ∂μ₂ ∂μ₁ := by
        simp [I, add_left_comm, add_comm]
      have hleft2 :
          (∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂))
            = ∫ z₁ : ℝ, ∫ z₂ : ℝ, Real.exp (m * A (x + z₁ + z₂)) ∂μ₂ ∂μ₁ := by
        simpa [F, add_assoc, add_left_comm, add_comm] using
          (MeasureTheory.integral_prod F hF_int)
      exact hleft1.trans (by simpa using hleft2.symm)
    have hright :
        (∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂))
          = ∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂) := by
      have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
      have haemeas : AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2) (μ₁.prod μ₂) :=
        hadd.aemeasurable
      have hfm :
          AEStronglyMeasurable (fun z : ℝ => Real.exp (m * A (x + z)))
            (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ₁.prod μ₂)) := by
        have : Measurable (fun z : ℝ => Real.exp (m * A (x + z))) := by
          have : Measurable fun z : ℝ => x + z := by fun_prop
          have : Measurable fun z : ℝ => A (x + z) := hA_meas.comp this
          fun_prop
        exact this.aestronglyMeasurable
      simpa [MeasureTheory.Measure.conv, F, add_assoc, add_left_comm, add_comm] using
        (MeasureTheory.integral_map (μ := (μ₁.prod μ₂))
          (φ := fun p : ℝ × ℝ => p.1 + p.2) haemeas
          (f := fun z : ℝ => Real.exp (m * A (x + z))) hfm)
    exact by
      simpa [hleft] using hright.symm
  have hGauss :
      (ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂) : Measure ℝ) = μ₁ ∗ μ₂ := by
    simpa [μ₁, μ₂, add_assoc, add_left_comm, add_comm] using
      (ProbabilityTheory.gaussianReal_conv_gaussianReal (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ))
        (v₁ := v₁) (v₂ := v₂)).symm
  have hInside :
      (∫ z : ℝ, Real.exp (m * A (x + z))
        ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂)))
        = (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁) := by
    calc
      (∫ z : ℝ, Real.exp (m * A (x + z))
        ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂)))
          = ∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂) := by simp [hGauss]
      _ = ∫ z₁ : ℝ, I (x + z₁) ∂μ₁ := by simp [hFubini]
      _ = (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁) := by simp [hstep]
  simp [T, hInside, μ₁, hm, div_eq_mul_inv, mul_comm]

end Parisi

end SpinGlass
