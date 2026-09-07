/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The `L²`-joint law of an independent pair, and its block-diagonal covariance

Given random variables `X` (valued in a Hilbert space `E`) and `Y` (valued in a Hilbert space
`F`) on `Ω`, the pair repackages as a single random variable `ω ↦ (X ω, Y ω)` valued in the
Hilbert space `WithLp 2 (E × F)`. The two spaces need not agree: a Guerra-style interpolation
compares two Hamiltonians on the same configuration space, but a splitting argument compares a
system with a pair of subsystems, and there the two blocks live in different spaces. This file
records the three facts about the joint law that every Gaussian comparison or interpolation
argument needs:

* it is Gaussian when `X` and `Y` are Gaussian and independent
  (`ProbabilityTheory.isGaussian_map_toLp_prodMk`);
* it is centered when `X` and `Y` are (`ProbabilityTheory.integral_id_map_toLp_prodMk_eq_zero`);
* its covariance operator is **block diagonal**, with the covariance operators of `X` and `Y` as
  its blocks (`ProbabilityTheory.covarianceOperator_map_toLp_prodMk`).

The last is the substantive one: it is what turns the hypotheses of the Gaussian interpolation
trace identity, of Slepian's inequality and of the Sudakov–Fernique inequality into statements
about the two marginals, and it is exactly where independence enters (the off-diagonal blocks are
the cross-covariances, which vanish).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω E F : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {X : Ω → E}

/-! ### Second moments of a single Gaussian variable -/

section SingleVariable

variable [IsGaussian (P.map X)]

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Second moments of a coordinate functional are finite, for a Gaussian variable. -/
lemma memLp_two_inner (hX : Measurable X) (x : E) :
    MemLp (fun ω => ⟪x, X ω⟫_ℝ) 2 P := by
  have h : MemLp (innerSL ℝ x) 2 (P.map X) :=
    IsGaussian.memLp_dual (μ := P.map X) (L := innerSL ℝ x) 2 (by norm_num)
  simpa [Function.comp_def] using h.comp_of_map (f := X) (μ := P) hX.aemeasurable

/-- The covariance operator of a pushforward law, read as a second moment on the base space. -/
lemma inner_covarianceOperator_map (hX : Measurable X) (x y : E) :
    ⟪covarianceOperator (P.map X) x, y⟫_ℝ = ∫ ω, ⟪x, X ω⟫_ℝ * ⟪y, X ω⟫_ℝ ∂P := by
  have hLp : MemLp (fun u : E => u) 2 (P.map X) :=
    IsGaussian.memLp_two_id (μ := P.map X)
  have hcov := covarianceOperator_inner (μ := P.map X) hLp x y
  have hmeas : Measurable fun u : E => ⟪x, u⟫_ℝ * ⟪y, u⟫_ℝ := by
    exact ((innerSL ℝ x).measurable).mul ((innerSL ℝ y).measurable)
  have hmap : (∫ u : E, ⟪x, u⟫_ℝ * ⟪y, u⟫_ℝ ∂(P.map X))
      = ∫ ω, ⟪x, X ω⟫_ℝ * ⟪y, X ω⟫_ℝ ∂P :=
    MeasureTheory.integral_map hX.aemeasurable hmeas.aestronglyMeasurable
  rw [hcov, hmap]

end SingleVariable

/-! ### The `L²`-joint law of a pair -/

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {Y : Ω → F}

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [InnerProductSpace ℝ F] [CompleteSpace F] in
/-- The pair `ω ↦ (X ω, Y ω)`, valued in the Hilbert space `WithLp 2 (E × F)`, is measurable. -/
lemma measurable_toLp_prodMk (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => WithLp.toLp 2 (X ω, Y ω)) := by
  have hpair : Measurable fun ω : Ω => (X ω, Y ω) := hX.prodMk hY
  exact (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞)) (α := E) (β := F)).measurable.comp hpair

/-- **The `L²`-joint law of an independent Gaussian pair is Gaussian.** -/
lemma isGaussian_map_toLp_prodMk (hXg : HasGaussianLaw X P) (hYg : HasGaussianLaw Y P)
    (hindep : X ⟂ᵢ[P] Y) :
    IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) := by
  have hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P :=
    IndepFun.hasGaussianLaw (P := P) hXg hYg hindep
  have : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact (HasGaussianLaw.toLp_prodMk (X := X) (Y := Y) (P := P) (p := (2 : ℝ≥0∞)) hXY).isGaussian_map

omit [MeasurableSpace Ω] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] in
/-- Coordinates of the `L²`-joint variable, in inner-product form. -/
lemma inner_toLp_prodMk (x : WithLp 2 (E × F)) (ω : Ω) :
    ⟪x, WithLp.toLp 2 (X ω, Y ω)⟫_ℝ
      = ⟪(WithLp.ofLp x).1, X ω⟫_ℝ + ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ := by
  simp [WithLp.prod_inner_apply]

/-- **The `L²`-joint law of a centered pair is centered.** -/
lemma integral_id_map_toLp_prodMk_eq_zero (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X P) (hYi : Integrable Y P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    [IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω))] :
    (∫ p : WithLp 2 (E × F), p ∂(P.map fun ω => WithLp.toLp 2 (X ω, Y ω))) = 0 := by
  set μ : Measure (WithLp 2 (E × F)) := P.map fun ω => WithLp.toLp 2 (X ω, Y ω) with hμdef
  have hpair : Measurable (fun ω => WithLp.toLp 2 (X ω, Y ω)) := measurable_toLp_prodMk hX hY
  have hint : Integrable (fun p : WithLp 2 (E × F) => p) μ := IsGaussian.integrable_id (μ := μ)
  refine ext_inner_right ℝ fun y => ?_
  rw [inner_zero_left, real_inner_comm, ← integral_inner hint y]
  have hmap : (∫ p : WithLp 2 (E × F), ⟪y, p⟫_ℝ ∂μ)
      = ∫ ω, ⟪y, WithLp.toLp 2 (X ω, Y ω)⟫_ℝ ∂P := by
    rw [hμdef]
    exact MeasureTheory.integral_map hpair.aemeasurable
      (innerSL ℝ y).continuous.aestronglyMeasurable
  rw [hmap, MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω => inner_toLp_prodMk (X := X) (Y := Y) y ω)]
  have hI1 : Integrable (fun ω => ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) P :=
    (innerSL ℝ (WithLp.ofLp y).1).integrable_comp hXi
  have hI2 : Integrable (fun ω => ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ) P :=
    (innerSL ℝ (WithLp.ofLp y).2).integrable_comp hYi
  have h1 : (∫ ω, ⟪(WithLp.ofLp y).1, X ω⟫_ℝ ∂P) = 0 := by
    have := (innerSL ℝ (WithLp.ofLp y).1).integral_comp_comm (μ := P) hXi
    simpa [hX0] using this
  have h2 : (∫ ω, ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ ∂P) = 0 := by
    have := (innerSL ℝ (WithLp.ofLp y).2).integral_comp_comm (μ := P) hYi
    simpa [hY0] using this
  rw [MeasureTheory.integral_add hI1 hI2, h1, h2, add_zero]

section Covariance

variable [IsGaussian (P.map X)] [IsGaussian (P.map Y)]

/-- **The covariance operator of the `L²`-joint law of an independent pair is block diagonal.**
Its blocks are the covariance operators of the two marginals; the off-diagonal blocks are the
cross-covariances, and they vanish precisely because `X` and `Y` are independent and centered.

This is the fact that makes the hypotheses of the Gaussian interpolation trace identity, of
Slepian's inequality and of the Sudakov–Fernique inequality checkable: they ask for exactly this
block structure. -/
theorem covarianceOperator_map_toLp_prodMk (hX : Measurable X) (hY : Measurable Y)
    (hindep : X ⟂ᵢ[P] Y)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    [IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω))]
    (x : WithLp 2 (E × F)) :
    covarianceOperator (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) x
      = WithLp.toLp 2 (covarianceOperator (P.map X) (WithLp.ofLp x).1,
          covarianceOperator (P.map Y) (WithLp.ofLp x).2) := by
  classical
  have hpair : Measurable (fun ω => WithLp.toLp 2 (X ω, Y ω)) := measurable_toLp_prodMk hX hY
  have hXi : Integrable X P := (IsGaussian.hasGaussianLaw (X := X) (P := P)).integrable
  have hYi : Integrable Y P := (IsGaussian.hasGaussianLaw (X := Y) (P := P)).integrable
  -- The two cross terms vanish, by independence and centering.
  have hcrossXY : ∀ (u : E) (v : F), (∫ ω, ⟪u, X ω⟫_ℝ * ⟪v, Y ω⟫_ℝ ∂P) = 0 := by
    intro u v
    have hind : (fun ω => ⟪u, X ω⟫_ℝ) ⟂ᵢ[P] (fun ω => ⟪v, Y ω⟫_ℝ) :=
      hindep.comp (hφ := (innerSL ℝ u).measurable) (hψ := (innerSL ℝ v).measurable)
    have hsplit := IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind
      ((innerSL ℝ u).measurable.aestronglyMeasurable.comp_measurable hX)
      ((innerSL ℝ v).measurable.aestronglyMeasurable.comp_measurable hY)
    have hu : (∫ ω, ⟪u, X ω⟫_ℝ ∂P) = 0 := by
      have := (innerSL ℝ u).integral_comp_comm (μ := P) hXi
      simpa [hX0] using this
    rw [hsplit, hu, zero_mul]
  have hcrossYX : ∀ (u : F) (v : E), (∫ ω, ⟪u, Y ω⟫_ℝ * ⟪v, X ω⟫_ℝ ∂P) = 0 := by
    intro u v
    have hind : (fun ω => ⟪v, X ω⟫_ℝ) ⟂ᵢ[P] (fun ω => ⟪u, Y ω⟫_ℝ) :=
      hindep.comp (hφ := (innerSL ℝ v).measurable) (hψ := (innerSL ℝ u).measurable)
    have hsplit := IndepFun.integral_fun_mul_eq_mul_integral (μ := P) hind
      ((innerSL ℝ v).measurable.aestronglyMeasurable.comp_measurable hX)
      ((innerSL ℝ u).measurable.aestronglyMeasurable.comp_measurable hY)
    have hu : (∫ ω, ⟪u, Y ω⟫_ℝ ∂P) = 0 := by
      have := (innerSL ℝ u).integral_comp_comm (μ := P) hYi
      simpa [hY0] using this
    calc (∫ ω, ⟪u, Y ω⟫_ℝ * ⟪v, X ω⟫_ℝ ∂P)
        = ∫ ω, ⟪v, X ω⟫_ℝ * ⟪u, Y ω⟫_ℝ ∂P :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      _ = 0 := by rw [hsplit, hu, mul_zero]
  refine ext_inner_right ℝ fun y => ?_
  -- Square-integrability of each coordinate functional.
  have hAx1 : MemLp (fun ω => ⟪(WithLp.ofLp x).1, X ω⟫_ℝ) 2 P := memLp_two_inner hX _
  have hAy1 : MemLp (fun ω => ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) 2 P := memLp_two_inner hX _
  have hAx2 : MemLp (fun ω => ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ) 2 P :=
    memLp_two_inner (X := Y) hY _
  have hAy2 : MemLp (fun ω => ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ) 2 P :=
    memLp_two_inner (X := Y) hY _
  have hI11 : Integrable
      (fun ω => ⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) P :=
    hAx1.integrable_mul hAy1
  have hI22 : Integrable
      (fun ω => ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ) P :=
    hAx2.integrable_mul hAy2
  have hI12 : Integrable
      (fun ω => ⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ) P :=
    hAx1.integrable_mul hAy2
  have hI21 : Integrable
      (fun ω => ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) P :=
    hAx2.integrable_mul hAy1
  have hIdiag : Integrable
      (fun ω => ⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ
        + ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ) P := hI11.add hI22
  have hIoff : Integrable
      (fun ω => ⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ
        + ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) P := hI12.add hI21
  -- The left-hand side, transported to `Ω` and expanded.
  have hLHS : ⟪covarianceOperator (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) x, y⟫_ℝ
      = ∫ ω, (⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ
            + ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ)
          + (⟪(WithLp.ofLp x).1, X ω⟫_ℝ * ⟪(WithLp.ofLp y).2, Y ω⟫_ℝ
            + ⟪(WithLp.ofLp x).2, Y ω⟫_ℝ * ⟪(WithLp.ofLp y).1, X ω⟫_ℝ) ∂P := by
    have hLp : MemLp (fun p : WithLp 2 (E × F) => p) 2
        (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) :=
      IsGaussian.memLp_two_id (μ := P.map fun ω => WithLp.toLp 2 (X ω, Y ω))
    have hcov := covarianceOperator_inner
      (μ := P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) hLp x y
    have hmeas : Measurable fun p : WithLp 2 (E × F) => ⟪x, p⟫_ℝ * ⟪y, p⟫_ℝ :=
      ((innerSL ℝ x).measurable).mul ((innerSL ℝ y).measurable)
    have hmap : (∫ p : WithLp 2 (E × F), ⟪x, p⟫_ℝ * ⟪y, p⟫_ℝ
          ∂(P.map fun ω => WithLp.toLp 2 (X ω, Y ω)))
        = ∫ ω, ⟪x, WithLp.toLp 2 (X ω, Y ω)⟫_ℝ * ⟪y, WithLp.toLp 2 (X ω, Y ω)⟫_ℝ ∂P :=
      MeasureTheory.integral_map hpair.aemeasurable hmeas.aestronglyMeasurable
    rw [hcov, hmap]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [inner_toLp_prodMk]
    ring
  rw [hLHS, MeasureTheory.integral_add hIdiag hIoff,
    MeasureTheory.integral_add hI11 hI22, MeasureTheory.integral_add hI12 hI21,
    hcrossXY (WithLp.ofLp x).1 (WithLp.ofLp y).2,
    hcrossYX (WithLp.ofLp x).2 (WithLp.ofLp y).1,
    ← inner_covarianceOperator_map hX (WithLp.ofLp x).1 (WithLp.ofLp y).1,
    ← inner_covarianceOperator_map (X := Y) hY (WithLp.ofLp x).2 (WithLp.ofLp y).2,
    WithLp.prod_inner_apply]
  ring

/-- The left block: `C (x, 0) = (C_X x, 0)`. -/
theorem covarianceOperator_map_toLp_prodMk_left (hX : Measurable X) (hY : Measurable Y)
    (hindep : X ⟂ᵢ[P] Y)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    [IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω))]
    (x : E) :
    covarianceOperator (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) (WithLp.toLp 2 (x, 0))
      = WithLp.toLp 2 (covarianceOperator (P.map X) x, 0) := by
  rw [covarianceOperator_map_toLp_prodMk hX hY hindep hX0 hY0]
  simp

/-- The right block: `C (0, y) = (0, C_Y y)`. -/
theorem covarianceOperator_map_toLp_prodMk_right (hX : Measurable X) (hY : Measurable Y)
    (hindep : X ⟂ᵢ[P] Y)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    [IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω))]
    (y : F) :
    covarianceOperator (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) (WithLp.toLp 2 (0, y))
      = WithLp.toLp 2 (0, covarianceOperator (P.map Y) y) := by
  rw [covarianceOperator_map_toLp_prodMk hX hY hindep hX0 hY0]
  simp

end Covariance

end ProbabilityTheory
