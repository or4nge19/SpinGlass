import SpinGlass.ComplexIBP
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Arguin–Tai (2018): the test function `F_p`

This file starts the formalization of the function `F_p(z, z̄)` from Arguin–Tai (2018),
used to apply the approximate complex IBP lemma (`SpinGlass.approx_integral_by_parts_complex`).

In the paper, for a fixed prime `p`, one defines (schematically)

`F_p(z, z̄) = (∫ ω_p(h) * exp(β(ω_p(h) z + \bar ω_p(h) \bar z) + Y_p(h)) dh)
             / (∫ exp(β(ω_p(h) z + \bar ω_p(h) \bar z) + Y_p(h)) dh)`.

We implement the same object as a genuine function `ℂ → ℂ`, interpreting `z̄ = conj z`.

The next step (in this file) will be to prove that `F_p` satisfies `FDerivLipschitz` with a
constant `M = O(p^{-3/2})` (uniformly in `z`), matching the heuristic bound in the paper.
-/

open scoped Real Topology BigOperators ComplexConjugate NNReal
open MeasureTheory Set Filter Complex

namespace SpinGlass

noncomputable section

/-!
### Measurability/continuity instances for scalar multiplication on higher-order CLM spaces

For spaces like `ℂ →L[ℝ] ℂ →L[ℝ] ℂ`, typeclass inference does not automatically provide
`IsBoundedSMul`/`ContinuousSMul`/`MeasurableSMul₂` for the `ℂ`-action, even though the normed-space
structure is available. We register the missing boundedness instance so that `Measurable.smul` can
be used below.
-/

-- We use the Borel σ-algebra coming from the norm topology on these CLM spaces.
instance : MeasurableSpace (ℂ →L[ℝ] ℂ) := borel _
instance : MeasurableSpace (ℂ →L[ℝ] ℝ) := borel _
instance : MeasurableSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := borel _
instance : MeasurableSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := borel _

instance : BorelSpace (ℂ →L[ℝ] ℂ) := ⟨rfl⟩
instance : BorelSpace (ℂ →L[ℝ] ℝ) := ⟨rfl⟩
instance : BorelSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ⟨rfl⟩
instance : BorelSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := ⟨rfl⟩

instance : IsScalarTower ℝ ℂ (ℂ →L[ℝ] ℂ) where
  smul_assoc r c T := by
    ext z
    exact smul_assoc r c (T z)

instance : IsScalarTower ℝ ℂ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) where
  smul_assoc r c T := by
    ext z w
    exact smul_assoc r c (T z w)

-- `PseudoMetrizableSpace` does not always infer for higher-order CLM spaces, so we register it
-- explicitly via the induced (pseudo)metric structure coming from the operator norm.
instance : TopologicalSpace.PseudoMetrizableSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := by
  classical
  letI : PseudoMetricSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := by infer_instance
  infer_instance

instance : TopologicalSpace.PseudoMetrizableSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := by
  classical
  letI : PseudoMetricSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := by infer_instance
  infer_instance

instance : IsBoundedSMul ℂ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := by
  classical
  letI : NormedSpace ℂ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := by infer_instance
  refine IsBoundedSMul.of_norm_smul_le (α := ℂ) (β := (ℂ →L[ℝ] ℂ →L[ℝ] ℂ)) ?_
  intro c T
  simpa using
    (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℂ)
      (E := ℂ) (F := (ℂ →L[ℝ] ℂ)) c T)

-- With the boundedness instance in place, we can register continuity/measurability of the action.
instance : ContinuousSMul ℂ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) :=
  (IsBoundedSMul.continuousSMul (α := ℂ) (β := (ℂ →L[ℝ] ℂ →L[ℝ] ℂ)))

instance : MeasurableSMul₂ ℂ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := by
  refine ⟨(continuous_smul : Continuous fun p : ℂ × (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) => p.1 • p.2).measurable⟩

/-! ## The base measure on `[0,1]` -/

def I01 : Set ℝ := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to `[0,1]`. This is a probability measure since `vol(I01)=1`. -/
noncomputable def μ01 : Measure ℝ :=
  (volume.restrict I01)

lemma μ01_isProbabilityMeasure : IsProbabilityMeasure (μ01) := by
  classical
  refine ⟨?_⟩
  simp [μ01, I01, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]

instance : IsProbabilityMeasure μ01 := μ01_isProbabilityMeasure

instance : IsFiniteMeasure μ01 := by
  dsimp [μ01, I01]
  infer_instance

instance : NeZero μ01 := by
  refine ⟨?_⟩
  intro h0
  have hmass : μ01 Set.univ = (1 : ENNReal) := by
    simp [μ01, I01, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  have hmass0 : μ01 Set.univ = 0 := by
    simp [h0]
  simp [hmass] at hmass0

/-! ## The coefficient `ω_p(h)` -/

/--
The paper’s coefficient
`ω_p(h) = (2 * √p)⁻¹ * p^{-i h} = (2 * √p)⁻¹ * exp(-i h log p)`.
-/
noncomputable def omega_p (p : ℕ) (h : ℝ) : ℂ :=
  (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) *
    Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))

lemma omega_p_norm (p : ℕ) (h : ℝ) :
    ‖omega_p p h‖ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
  have hexp :
      ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖ = 1 := by
    have hre : ((-Complex.I) * (h : ℂ) * (Real.log (p : ℝ) : ℂ)).re = 0 := by
      simp [-Complex.natCast_log, -Complex.ofNat_log]
    simp [Complex.norm_exp, -Complex.natCast_log, -Complex.ofNat_log]
  have hsc : 0 ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by positivity
  have hnsc :
      ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
    simp
  calc
    ‖omega_p p h‖
        = ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖
            * ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖ := by
              simp [omega_p, mul_assoc, -Complex.natCast_log, -Complex.ofNat_log]
    _ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
          calc
            ‖((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) : ℂ)‖
                * ‖Complex.exp (-Complex.I * (h : ℂ) * (Real.log (p : ℝ) : ℂ))‖
                = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * 1 := by
                    rw [hnsc, hexp]
            _ = (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by ring

lemma omega_p_norm_le (p : ℕ) (h : ℝ) :
    ‖omega_p p h‖ ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
  simp [omega_p_norm]

lemma measurable_omega_p (p : ℕ) : Measurable (omega_p p) := by
  unfold omega_p
  fun_prop

/-! ## The Arguin–Tai weight and the function `F_p` -/

/--
The real weight in the Gibbs-like average:

`w(z,h) = exp( 2*β*Re(omega_p(h) * z) + Y(h) )`.

This matches `exp(β(ω z + conj ω conj z) + Y)` since `ω z + conj ω conj z = 2 Re(ω z)`.
-/
noncomputable def arguinTaiWeight (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) (h : ℝ) : ℝ :=
  Real.exp (2 * β * ((omega_p p h * z).re) + Y h)

lemma arguinTaiWeight_pos (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) (h : ℝ) :
    0 < arguinTaiWeight β p Y z h := by
  simp [arguinTaiWeight, Real.exp_pos]

lemma measurable_arguinTaiWeight (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y) (z : ℂ) :
    Measurable (fun h => arguinTaiWeight β p Y z h) := by
  have hω : Measurable (omega_p p) := measurable_omega_p p
  have hre : Measurable (fun h => (omega_p p h * z).re) := by
    simpa using (Complex.continuous_re.measurable.comp (hω.mul measurable_const))
  have hlin : Measurable (fun h => (2 * β) * (omega_p p h * z).re + Y h) :=
    (measurable_const.mul hre).add hY
  simpa [arguinTaiWeight] using (Real.continuous_exp.measurable.comp hlin)

lemma integrable_arguinTaiWeight_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    Integrable (fun h => arguinTaiWeight β p Y z h) μ01 := by
  have hmeas :
      AEStronglyMeasurable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)).aestronglyMeasurable
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  have hbound :
      ∀ᵐ h ∂μ01, ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω := by
      simpa [Cω] using omega_p_norm_le p h
    have hlin :
        2 * β * (omega_p p h * z).re + Y h
          ≤ 2 * |β| * Cω * ‖z‖ + CY := by
      have h1 :
          2 * β * (omega_p p h * z).re ≤ |2 * β * (omega_p p h * z).re| :=
        le_abs_self _
      have h2 :
          |2 * β * (omega_p p h * z).re|
            = 2 * |β| * |(omega_p p h * z).re| := by
        simp [abs_mul, mul_assoc, mul_comm]
      have h3 : |(omega_p p h * z).re| ≤ ‖omega_p p h‖ * ‖z‖ := by
        calc
          |(omega_p p h * z).re| ≤ ‖omega_p p h * z‖ := Complex.abs_re_le_norm _
          _ = ‖omega_p p h‖ * ‖z‖ := by simp
      have h4 :
          2 * |β| * |(omega_p p h * z).re| ≤ 2 * |β| * (‖omega_p p h‖ * ‖z‖) := by
        gcongr
      have h5 :
          2 * |β| * (‖omega_p p h‖ * ‖z‖) ≤ 2 * |β| * (Cω * ‖z‖) := by
        gcongr
      have hlin' : 2 * β * (omega_p p h * z).re ≤ 2 * |β| * (Cω * ‖z‖) := by
        have : |2 * β * (omega_p p h * z).re| ≤ 2 * |β| * (Cω * ‖z‖) := by
          have : 2 * |β| * |(omega_p p h * z).re| ≤ 2 * |β| * (Cω * ‖z‖) := by
            exact (h4.trans (h5.trans_eq (by ring)))
          simpa [h2] using this
        exact h1.trans this
      have hYle : Y h ≤ CY := (le_trans (le_abs_self _) (hYb h))
      linarith
    have hexp :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
      simpa [arguinTaiWeight] using (Real.exp_le_exp.mpr hlin)
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hexp
  exact MeasureTheory.Integrable.of_bound (μ := μ01) hmeas _ hbound

/-! ## Real Fréchet derivatives in `z` -/

/-- The real-linear map `z ↦ Re(ω*z)` as a continuous linear map over `ℝ`. -/
noncomputable def reMulCLM (ω : ℂ) : ℂ →L[ℝ] ℝ :=
  (ω.re) • Complex.reCLM - (ω.im) • Complex.imCLM

@[simp] lemma reMulCLM_apply (ω z : ℂ) : reMulCLM ω z = (ω * z).re := by
  simp [reMulCLM, Complex.mul_re]

lemma norm_reMulCLM_le (ω : ℂ) : ‖reMulCLM ω‖ ≤ ‖ω‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (reMulCLM ω) (by positivity) ?_
  intro z
  simpa [reMulCLM_apply, Real.norm_eq_abs] using
    (calc
      |(ω * z).re| ≤ ‖ω * z‖ := Complex.abs_re_le_norm (ω * z)
      _ = ‖ω‖ * ‖z‖ := by simp)

/-- The `z`-linear part of the exponent: `(2β) * Re(ω_p(h) * z)` packaged as `ℂ →L[ℝ] ℝ`. -/
noncomputable def L_p (β : ℝ) (p : ℕ) (h : ℝ) : ℂ →L[ℝ] ℝ :=
  (2 * β) • reMulCLM (omega_p p h)

@[simp] lemma L_p_apply (β : ℝ) (p : ℕ) (h : ℝ) (z : ℂ) :
    L_p β p h z = (2 * β) * (omega_p p h * z).re := by
  simp [L_p, mul_assoc]

lemma norm_L_p_le (β : ℝ) (p : ℕ) (h : ℝ) :
    ‖L_p β p h‖ ≤ ‖(2 * β)‖ * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := by
  have hω : ‖omega_p p h‖ ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := omega_p_norm_le p h
  have hre : ‖reMulCLM (omega_p p h)‖ ≤ ‖omega_p p h‖ := norm_reMulCLM_le (omega_p p h)
  have : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * ‖omega_p p h‖ := by
    have : ‖L_p β p h‖ = ‖(2 * β)‖ * ‖reMulCLM (omega_p p h)‖ := by
      simpa [L_p] using (norm_smul (2 * β) (reMulCLM (omega_p p h)))
    calc
      ‖L_p β p h‖ = ‖(2 * β)‖ * ‖reMulCLM (omega_p p h)‖ := this
      _ ≤ ‖(2 * β)‖ * ‖omega_p p h‖ := by gcongr
  exact this.trans (by gcongr)

lemma measurable_L_p (β : ℝ) (p : ℕ) : Measurable (fun h : ℝ => L_p β p h) := by
  have hω : Measurable (omega_p p) := measurable_omega_p p
  have hre : Measurable (fun h : ℝ => (omega_p p h).re) :=
    Complex.continuous_re.measurable.comp hω
  have him : Measurable (fun h : ℝ => (omega_p p h).im) :=
    Complex.continuous_im.measurable.comp hω
  have h1 : Measurable (fun h : ℝ => (omega_p p h).re • (Complex.reCLM : ℂ →L[ℝ] ℝ)) :=
    hre.smul_const _
  have h2 : Measurable (fun h : ℝ => (omega_p p h).im • (Complex.imCLM : ℂ →L[ℝ] ℝ)) :=
    him.smul_const _
  have hres : Measurable (fun h : ℝ => reMulCLM (omega_p p h)) := by
    simpa [reMulCLM, sub_eq_add_neg] using h1.sub h2
  simpa [L_p] using (hres.const_smul (2 * β))

lemma hasFDerivAt_arguinTaiWeight (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (h : ℝ) (z : ℂ) :
    HasFDerivAt (fun z => arguinTaiWeight β p Y z h)
      ((arguinTaiWeight β p Y z h) • (L_p β p h)) z := by
  have hw : arguinTaiWeight β p Y z h = Real.exp ((L_p β p h) z + Y h) := by
    simp [arguinTaiWeight, L_p_apply, mul_assoc]
  have h_aff : HasFDerivAt (fun z : ℂ => (L_p β p h) z + Y h) (L_p β p h) z := by
    simpa using ((L_p β p h).hasFDerivAt.add_const (Y h))
  have h_exp :
      HasFDerivAt Real.exp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp ((L_p β p h) z + Y h)))
        ((L_p β p h) z + Y h) :=
    (Real.hasDerivAt_exp ((L_p β p h) z + Y h)).hasFDerivAt
  have hcomp := h_exp.comp z h_aff
  have hderiv :
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp ((L_p β p h) z + Y h))).comp
          (L_p β p h)
        = (Real.exp ((L_p β p h) z + Y h)) • (L_p β p h) := by
    ext u
    simp [ContinuousLinearMap.smulRight_apply, mul_assoc, mul_comm]
  have hcomp' := hcomp.congr_fderiv hderiv
  simpa [hw] using hcomp'

lemma hasFDerivAt_arguinTaiWeight_smul_L_p
    (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (h : ℝ) (z : ℂ) :
    HasFDerivAt (fun z => (arguinTaiWeight β p Y z h) • (L_p β p h))
      ((arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))) z := by
  have hw : HasFDerivAt (fun z => arguinTaiWeight β p Y z h)
      ((arguinTaiWeight β p Y z h) • (L_p β p h)) z :=
    hasFDerivAt_arguinTaiWeight (β := β) (p := p) (Y := Y) (h := h) (z := z)
  let S : ℝ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L_p β p h)
  have hS : HasFDerivAt (fun r : ℝ => r • (L_p β p h)) S (arguinTaiWeight β p Y z h) := by
    simpa [S] using S.hasFDerivAt
  have hcomp := hS.comp z hw
  have hderiv : (S.comp ((arguinTaiWeight β p Y z h) • (L_p β p h)))
      = (arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) := by
    ext u
    simp [S, ContinuousLinearMap.smulRight_apply, mul_assoc, mul_comm]
  exact hcomp.congr_fderiv hderiv

lemma norm_smulRight_le (L : ℂ →L[ℝ] ℝ) :
    ‖(ContinuousLinearMap.smulRight L L)‖ ≤ ‖L‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (ContinuousLinearMap.smulRight L L) (by positivity) ?_
  intro u
  -- `‖(L u) • L‖ = ‖L u‖ * ‖L‖ ≤ (‖L‖*‖u‖)*‖L‖`
  calc
    ‖(ContinuousLinearMap.smulRight L L) u‖ = ‖L u‖ * ‖L‖ := by
      simp [ContinuousLinearMap.smulRight_apply, norm_smul]
    _ ≤ (‖L‖ * ‖u‖) * ‖L‖ := by
      gcongr
      exact L.le_opNorm u
    _ = (‖L‖ * ‖L‖) * ‖u‖ := by
      ring_nf

noncomputable def Z_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ h, arguinTaiWeight β p Y z h ∂μ01

noncomputable def DZ_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  ∫ h, (arguinTaiWeight β p Y z h) • (L_p β p h) ∂μ01

noncomputable def DDZ_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  ∫ h, (arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) ∂μ01

lemma arguinTaiWeight_le_exp_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) (h : ℝ) :
    arguinTaiWeight β p Y z h ≤ Real.exp
        (2 * |β| * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖ + CY) := by
  have hre : |(omega_p p h * z).re| ≤ ‖omega_p p h‖ * ‖z‖ := by
    calc
      |(omega_p p h * z).re| ≤ ‖omega_p p h * z‖ := Complex.abs_re_le_norm _
      _ = ‖omega_p p h‖ * ‖z‖ := by simp
  have hω : ‖omega_p p h‖ ≤ (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) := omega_p_norm_le p h
  have hlin : 2 * β * (omega_p p h * z).re
      ≤ 2 * |β| * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖ := by
    have h1 : 2 * β * (omega_p p h * z).re ≤ |2 * β * (omega_p p h * z).re| := le_abs_self _
    have h2 :
        |2 * β * (omega_p p h * z).re|
          ≤ 2 * |β| * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖ := by
      calc
        |2 * β * (omega_p p h * z).re|
            = 2 * |β| * |(omega_p p h * z).re| := by
                simp [abs_mul, mul_assoc, mul_comm]
        _ ≤ 2 * |β| * (‖omega_p p h‖ * ‖z‖) := by gcongr
        _ ≤ 2 * |β| * ((1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖) := by gcongr
        _ = 2 * |β| * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖ := by ring
    exact h1.trans h2
  have hYle : Y h ≤ CY := (le_trans (le_abs_self _) (hYb h))
  have hexp :
      2 * β * (omega_p p h * z).re + Y h
        ≤ 2 * |β| * (1 / (2 * Real.sqrt (p : ℝ)) : ℝ) * ‖z‖ + CY := by
    linarith
  simpa [arguinTaiWeight] using (Real.exp_le_exp.mpr hexp)

lemma hasFDerivAt_Z_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (Z_p β p Y)
      (DZ_p β p Y z0) z0 := by
  have ε_pos : (0 : ℝ) < 1 := by norm_num
  let F : ℂ → ℝ → ℝ := fun z h => arguinTaiWeight β p Y z h
  let F' : ℂ → ℝ → ℂ →L[ℝ] ℝ := fun z h => (arguinTaiWeight β p Y z h) • (L_p β p h)
  have hF_meas : ∀ᶠ z in nhds z0, AEStronglyMeasurable (F z) μ01 :=
    Filter.Eventually.of_forall (fun z => (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)).aestronglyMeasurable)
  have hF_int : Integrable (F z0) μ01 := by
    simpa [F] using
      (integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0))
  have hF'_meas : AEStronglyMeasurable (F' z0) μ01 := by
    have hF'_meas' : Measurable (F' z0) :=
      (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z0)).smul
        (measurable_L_p (β := β) (p := p))
    exact hF'_meas'.aestronglyMeasurable
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  let B : ℝ := Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * Cω)
  have h_bound : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, ‖F' z h‖ ≤ (fun _h : ℝ => B) h := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hz' : ‖z‖ ≤ ‖z0‖ + 1 := le_of_lt (norm_lt_of_mem_ball hz)
    have hw0 :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      have hw := arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z) (h := h)
      have hmono :
          Real.exp (2 * |β| * Cω * ‖z‖ + CY)
            ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
        have hCω : 0 ≤ Cω := by positivity
        have hβ : 0 ≤ (2 * |β| * Cω : ℝ) := by positivity
        have : 2 * |β| * Cω * ‖z‖ + CY ≤ 2 * |β| * Cω * (‖z0‖ + 1) + CY := by
          have : (2 * |β| * Cω : ℝ) * ‖z‖ ≤ (2 * |β| * Cω : ℝ) * (‖z0‖ + 1) := by
            exact mul_le_mul_of_nonneg_left hz' hβ
          linarith
        exact (Real.exp_le_exp.mpr this)
      exact hw.trans hmono
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hnw : ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hw0
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * Cω := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have : ‖F' z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * Cω) := by
      calc
        ‖F' z h‖ = ‖arguinTaiWeight β p Y z h‖ * ‖L_p β p h‖ := by
          simp [F', norm_smul, mul_comm]
        _ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * Cω) := by
          gcongr
    simpa [B] using this
  have bound_integrable : Integrable (fun _h : ℝ => B) μ01 :=
    MeasureTheory.integrable_const (μ := μ01) B
  have h_diff : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, HasFDerivAt (fun z => F z h) (F' z h) z := by
    refine ae_of_all _ (fun h z hz => ?_)
    simpa [F, F'] using (hasFDerivAt_arguinTaiWeight (β := β) (p := p) (Y := Y) (h := h) (z := z))
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := μ01) (F := F) (F' := fun z h => F' z h)
      (x₀ := z0) (s := Metric.ball z0 1) (hs := Metric.ball_mem_nhds z0 ε_pos)
      (bound := fun _h : ℝ => B)
      hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa [Z_p, DZ_p, F, F'] using hmain

lemma hasFDerivAt_DZ_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (DZ_p β p Y) (DDZ_p β p Y z0) z0 := by
  have ε_pos : (0 : ℝ) < 1 := by norm_num
  let F : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun z h => (arguinTaiWeight β p Y z h) • (L_p β p h)
  let F' : ℂ → ℝ → (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := fun z h =>
    (arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))
  have hF_meas : ∀ᶠ z in nhds z0, AEStronglyMeasurable (F z) μ01 :=
    Filter.Eventually.of_forall (fun z =>
      ((measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)).aestronglyMeasurable).smul
        ((measurable_L_p (β := β) (p := p)).aestronglyMeasurable))
  have hF_int : Integrable (F z0) μ01 := by
    have hw_int :
        Integrable (fun h => arguinTaiWeight β p Y z0 h) μ01 :=
      integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0)
    let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
    let K : ℝ := ‖(2 * β)‖ * Cω
    have hLp : ∀ h, ‖L_p β p h‖ ≤ K := by
      intro h
      simpa [K, Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hmeas :
        AEStronglyMeasurable (F z0) μ01 :=
      (((measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z0)).aestronglyMeasurable).smul
        ((measurable_L_p (β := β) (p := p)).aestronglyMeasurable))
    have hbound : ∀ᵐ h ∂μ01, ‖F z0 h‖ ≤ (fun h => arguinTaiWeight β p Y z0 h * K) h := by
      refine ae_of_all _ (fun h => ?_)
      have hpos : 0 < arguinTaiWeight β p Y z0 h := arguinTaiWeight_pos β p Y z0 h
      calc
        ‖F z0 h‖ = ‖arguinTaiWeight β p Y z0 h‖ * ‖L_p β p h‖ := by
          simp [F, norm_smul, mul_comm]
        _ ≤ (arguinTaiWeight β p Y z0 h) * K := by
          gcongr
          · simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
          · exact hLp h
    have hg : Integrable (fun h => arguinTaiWeight β p Y z0 h * K) μ01 :=
      (hw_int.mul_const K)
    exact MeasureTheory.Integrable.mono' hg hmeas hbound
  have hF'_meas : AEStronglyMeasurable (F' z0) μ01 := by
    have hw : Measurable (fun h => arguinTaiWeight β p Y z0 h) :=
      measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z0)
    have hL : Measurable (fun h : ℝ => ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) := by
      have hcontL : Continuous (fun h : ℝ => L_p β p h) := by
        unfold L_p reMulCLM omega_p
        fun_prop
      have hcont : Continuous (fun h : ℝ => ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) := by
        rw [continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := (ℂ →L[ℝ] ℝ))]
        intro y
        rw [continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)]
        intro u
        have hLy : Continuous fun h : ℝ => (L_p β p h) y :=
          (continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ) (f := fun h => L_p β p h)).1 hcontL y
        have hLu : Continuous fun h : ℝ => (L_p β p h) u :=
          (continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ) (f := fun h => L_p β p h)).1 hcontL u
        simpa [ContinuousLinearMap.smulRight_apply] using hLy.mul hLu
      exact hcont.measurable
    have hF' : Measurable (F' z0) := hw.smul hL
    exact hF'.aestronglyMeasurable
  -- uniform bound for `F'` on the ball `Metric.ball z0 1`
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  let K : ℝ := ‖(2 * β)‖ * Cω
  let B : ℝ := Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (K * K)
  have h_bound : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, ‖F' z h‖ ≤ (fun _h : ℝ => B) h := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hz' : ‖z‖ ≤ ‖z0‖ + 1 := le_of_lt (norm_lt_of_mem_ball hz)
    have hw0 :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      have hw := arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z) (h := h)
      have hmono :
          Real.exp (2 * |β| * Cω * ‖z‖ + CY)
            ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
        have hβ : 0 ≤ (2 * |β| * Cω : ℝ) := by positivity
        have : 2 * |β| * Cω * ‖z‖ + CY ≤ 2 * |β| * Cω * (‖z0‖ + 1) + CY := by
          have : (2 * |β| * Cω : ℝ) * ‖z‖ ≤ (2 * |β| * Cω : ℝ) * (‖z0‖ + 1) :=
            mul_le_mul_of_nonneg_left hz' hβ
          linarith
        exact (Real.exp_le_exp.mpr this)
      have hw' : arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
        simpa [Cω, mul_assoc] using hw
      exact hw'.trans hmono
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hnw : ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hw0
    have hLp : ∀ h, ‖L_p β p h‖ ≤ K := by
      intro h
      simpa [K, Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hsmul : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ ≤ K * K := by
      have hK : 0 ≤ K := by positivity [K, Cω]
      have h0 : 0 ≤ ‖L_p β p h‖ := norm_nonneg _
      have hLp' : ‖L_p β p h‖ ≤ K := hLp h
      have : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
          ≤ ‖L_p β p h‖ * ‖L_p β p h‖ := norm_smulRight_le (L_p β p h)
      refine this.trans ?_
      exact mul_le_mul hLp' hLp' h0 hK
    have : ‖F' z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (K * K) := by
      calc
        ‖F' z h‖ = ‖arguinTaiWeight β p Y z h • (L_p β p h).smulRight (L_p β p h)‖ := by
          simp only [F']
        _ ≤ ‖arguinTaiWeight β p Y z h‖ * ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ := by
          simpa using
            (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℝ)
              (E := ℂ) (F := (ℂ →L[ℝ] ℝ))
              (arguinTaiWeight β p Y z h)
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))
        _ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (K * K) := by
          gcongr
    simpa [B] using this
  have bound_integrable : Integrable (fun _h : ℝ => B) μ01 :=
    MeasureTheory.integrable_const (μ := μ01) B
  have h_diff : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, HasFDerivAt (fun z => F z h) (F' z h) z := by
    refine ae_of_all _ (fun h z hz => ?_)
    simpa [F, F'] using (hasFDerivAt_arguinTaiWeight_smul_L_p (β := β) (p := p) (Y := Y) (h := h) (z := z))
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := μ01) (F := F) (F' := fun z h => F' z h)
      (x₀ := z0) (s := Metric.ball z0 1) (hs := Metric.ball_mem_nhds z0 ε_pos)
      (bound := fun _h : ℝ => B)
      hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa [DZ_p, DDZ_p, F, F'] using hmain

lemma norm_ofRealCLM_comp_le (T : ℂ →L[ℝ] ℝ) : ‖Complex.ofRealCLM.comp T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (Complex.ofRealCLM.comp T) (by positivity) ?_
  intro z
  simpa [Complex.norm_real, Real.norm_eq_abs] using (T.le_opNorm z)

lemma ofRealCLM_comp_smul (c : ℝ) (T : ℂ →L[ℝ] ℝ) :
    Complex.ofRealCLM.comp (c • T) = c • (Complex.ofRealCLM.comp T) := by
  ext z
  simp [ContinuousLinearMap.smul_apply]

lemma norm_post_ofRealCLM_comp_le (S : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) :
    ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp S‖ ≤ ‖S‖ := by
  let post1 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM
  have hpost1 : ‖post1‖ ≤ (1 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound post1 (by positivity) ?_
    intro T
    have : ‖post1 T‖ ≤ ‖T‖ := by
      simpa [post1] using (norm_ofRealCLM_comp_le T)
    simpa [one_mul] using this
  have hcomp : ‖post1.comp S‖ ≤ ‖post1‖ * ‖S‖ :=
    (ContinuousLinearMap.opNorm_comp_le (h := post1) (f := S))
  have : ‖post1.comp S‖ ≤ (1 : ℝ) * ‖S‖ :=
    hcomp.trans (mul_le_mul_of_nonneg_right hpost1 (by positivity))
  simpa [post1] using this

lemma Z_p_pos_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    0 < Z_p β p Y z := by
  have hint : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  simpa [Z_p, arguinTaiWeight] using
    (MeasureTheory.integral_exp_pos (μ := μ01) (f := fun h => (2 * β) * (omega_p p h * z).re + Y h)
      (by
        simpa [arguinTaiWeight] using hint))

lemma Z_p_ne_zero_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    Z_p β p Y z ≠ 0 :=
  (ne_of_gt (Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)))

noncomputable def N_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ h, (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ) ∂μ01

noncomputable def DN_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ∫ h,
      (omega_p p h) •
        (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))) ∂μ01

noncomputable def DDN_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  ∫ h,
      (omega_p p h) •
        (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
              ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
          ((arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))) ∂μ01

lemma integrable_N_p_integrand_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    Integrable (fun h => (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)) μ01 := by
  have hω_meas : Measurable (omega_p p) := measurable_omega_p p
  have hw_meas : Measurable (fun h => (arguinTaiWeight β p Y z h : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)))
  have hmeas :
      AEStronglyMeasurable (fun h => (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)) μ01 :=
    (hω_meas.mul hw_meas).aestronglyMeasurable
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  let B : ℝ := Cω * Real.exp (2 * |β| * Cω * ‖z‖ + CY)
  have hbound :
      ∀ᵐ h ∂μ01, ‖(omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)‖ ≤ B := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω := by simpa [Cω] using omega_p_norm_le p h
    have hw :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
      have hw' :=
        arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z) (h := h)
      simpa [Cω, mul_assoc] using hw'
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hw_norm : ‖(arguinTaiWeight β p Y z h : ℂ)‖ ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
      have habs : |arguinTaiWeight β p Y z h| ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
        simpa [abs_of_nonneg (le_of_lt hpos)] using hw
      simpa [Complex.norm_real, Real.norm_eq_abs] using habs
    calc
      ‖(omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)‖
          = ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h : ℂ)‖ := by
              simp
      _ ≤ Cω * Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
            gcongr
      _ = B := by simp [B, mul_assoc]
  exact MeasureTheory.Integrable.of_bound (μ := μ01) hmeas B hbound

lemma hasFDerivAt_N_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (N_p β p Y)
      (DN_p β p Y z0) z0 := by
  have ε_pos : (0 : ℝ) < 1 := by norm_num
  let F : ℂ → ℝ → ℂ := fun z h => (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)
  let F' : ℂ → ℝ → ℂ →L[ℝ] ℂ := fun z h =>
    (omega_p p h) • (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h)))
  have hF_meas : ∀ᶠ z in nhds z0, AEStronglyMeasurable (F z) μ01 :=
    Filter.Eventually.of_forall (fun z => by
      have hω : Measurable (omega_p p) := measurable_omega_p p
      have hw : Measurable (fun h => (arguinTaiWeight β p Y z h : ℂ)) :=
        (Complex.continuous_ofReal.measurable.comp
          (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)))
      exact (hω.mul hw).aestronglyMeasurable)
  have hF_int : Integrable (F z0) μ01 := by
    simpa [F] using
      (integrable_N_p_integrand_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0))
  have hF'_meas : AEStronglyMeasurable (F' z0) μ01 := by
    have hω : Measurable (omega_p p) := measurable_omega_p p
    have hT : Measurable (fun h => (arguinTaiWeight β p Y z0 h) • (L_p β p h)) :=
      (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z0)).smul
        (measurable_L_p (β := β) (p := p))
    have hcomp : Measurable (fun T : (ℂ →L[ℝ] ℝ) => Complex.ofRealCLM.comp T) := by
      fun_prop
    have hU : Measurable (fun h => Complex.ofRealCLM.comp ((fun h => (arguinTaiWeight β p Y z0 h) • (L_p β p h)) h)) :=
      hcomp.comp hT
    have hF' : Measurable (F' z0) := hω.smul hU
    exact hF'.aestronglyMeasurable
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  let B : ℝ := Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * (Cω * Cω))
  have h_bound : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, ‖F' z h‖ ≤ (fun _h : ℝ => B) h := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hz' : ‖z‖ ≤ ‖z0‖ + 1 := le_of_lt (norm_lt_of_mem_ball hz)
    have hw0 :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      have hw := arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z) (h := h)
      have hmono :
          Real.exp (2 * |β| * Cω * ‖z‖ + CY)
            ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
        have hβ : 0 ≤ (2 * |β| * Cω : ℝ) := by positivity
        have : 2 * |β| * Cω * ‖z‖ + CY ≤ 2 * |β| * Cω * (‖z0‖ + 1) + CY := by
          have : (2 * |β| * Cω : ℝ) * ‖z‖ ≤ (2 * |β| * Cω : ℝ) * (‖z0‖ + 1) :=
            mul_le_mul_of_nonneg_left hz' hβ
          linarith
        exact (Real.exp_le_exp.mpr this)
      have hw' : arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
        simpa [Cω, mul_assoc] using hw
      exact hw'.trans hmono
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hnw : ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hw0
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * Cω := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hω : ‖omega_p p h‖ ≤ Cω := by simpa [Cω] using omega_p_norm_le p h
    have hcomp_le :
        ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))‖
          ≤ ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖ :=
      norm_ofRealCLM_comp_le _
    have : ‖F' z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * (Cω * Cω)) := by
      calc
        ‖F' z h‖
            = ‖omega_p p h‖ *
                ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))‖ := by
                  simp [F', norm_smul, mul_comm]
        _ ≤ ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖ := by
              gcongr
        _ = ‖omega_p p h‖ * (‖arguinTaiWeight β p Y z h‖ * ‖L_p β p h‖) := by
              simp [norm_smul]
        _ ≤ Cω * (Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * Cω)) := by
              gcongr
        _ = Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (‖(2 * β)‖ * (Cω * Cω)) := by
              ring_nf
    simpa [B] using this
  have bound_integrable : Integrable (fun _h : ℝ => B) μ01 :=
    MeasureTheory.integrable_const (μ := μ01) B
  have h_diff : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, HasFDerivAt (fun z => F z h) (F' z h) z := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hw : HasFDerivAt (fun z => arguinTaiWeight β p Y z h)
        ((arguinTaiWeight β p Y z h) • (L_p β p h)) z :=
      hasFDerivAt_arguinTaiWeight (β := β) (p := p) (Y := Y) (h := h) (z := z)
    have hwc : HasFDerivAt (fun z => (arguinTaiWeight β p Y z h : ℂ))
        (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))) z := by
      simpa [Function.comp] using (Complex.ofRealCLM.hasFDerivAt.comp z hw)
    simpa [F, F'] using (hwc.const_mul (omega_p p h))
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := μ01) (F := F) (F' := fun z h => F' z h)
      (x₀ := z0) (s := Metric.ball z0 1) (hs := Metric.ball_mem_nhds z0 ε_pos)
      (bound := fun _h : ℝ => B)
      hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa [N_p, DN_p, F, F'] using hmain

set_option maxHeartbeats 800000 in
lemma hasFDerivAt_DN_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (DN_p β p Y) (DDN_p β p Y z0) z0 := by
  have ε_pos : (0 : ℝ) < 1 := by norm_num
  let F : ℂ → ℝ → (ℂ →L[ℝ] ℂ) := fun z h =>
    (omega_p p h) • (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h)))
  let F' : ℂ → ℝ → (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) := fun z h =>
    (omega_p p h) •
      (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
            ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
        ((arguinTaiWeight β p Y z h) •
          (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))
  have hF_meas : ∀ᶠ z in nhds z0, AEStronglyMeasurable (F z) μ01 :=
    Filter.Eventually.of_forall (fun z => by
      have hω : Measurable (omega_p p) := measurable_omega_p p
      have hT : Measurable (fun h => (arguinTaiWeight β p Y z h) • (L_p β p h)) :=
        (measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z)).smul
          (measurable_L_p (β := β) (p := p))
      have hcomp : Measurable (fun T : (ℂ →L[ℝ] ℝ) => Complex.ofRealCLM.comp T) := by
        fun_prop
      have hU :
          Measurable (fun h =>
            Complex.ofRealCLM.comp ((fun h => (arguinTaiWeight β p Y z h) • (L_p β p h)) h)) :=
        hcomp.comp hT
      have hF : Measurable (F z) := hω.smul hU
      exact hF.aestronglyMeasurable)
  have hF_int : Integrable (F z0) μ01 := by
    have hw_int :
        Integrable (fun h => arguinTaiWeight β p Y z0 h) μ01 :=
      integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0)
    let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
    let B : ℝ := (Real.exp (2 * |β| * Cω * ‖z0‖ + CY)) * (‖(2 * β)‖ * (Cω * Cω))
    have hmeas : AEStronglyMeasurable (F z0) μ01 := (hF_meas.self_of_nhds)
    have hbound : ∀ᵐ h ∂μ01, ‖F z0 h‖ ≤ (fun h => B) h := by
      refine ae_of_all _ (fun h => ?_)
      have hω : ‖omega_p p h‖ ≤ Cω := by simpa [Cω] using omega_p_norm_le p h
      have hw :
          arguinTaiWeight β p Y z0 h ≤ Real.exp (2 * |β| * Cω * ‖z0‖ + CY) := by
        have hw' :=
          arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z0) (h := h)
        simpa [Cω, mul_assoc] using hw'
      have hpos : 0 < arguinTaiWeight β p Y z0 h := arguinTaiWeight_pos β p Y z0 h
      have hnw : ‖arguinTaiWeight β p Y z0 h‖ ≤ Real.exp (2 * |β| * Cω * ‖z0‖ + CY) := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hw
      have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * Cω := by
        simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
      have hcomp_le :
          ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z0 h) • (L_p β p h))‖
            ≤ ‖(arguinTaiWeight β p Y z0 h) • (L_p β p h)‖ :=
        norm_ofRealCLM_comp_le _
      calc
        ‖F z0 h‖
            = ‖(omega_p p h) • (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z0 h) • (L_p β p h)))‖ := by
                simp [F]
        _ ≤ ‖omega_p p h‖ *
              ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z0 h) • (L_p β p h))‖ := by
              simpa using
                (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℂ)
                  (E := ℂ) (F := ℂ)
                  (omega_p p h)
                  (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z0 h) • (L_p β p h))))
        _ ≤ ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z0 h) • (L_p β p h)‖ := by
              gcongr
        _ = ‖omega_p p h‖ * (‖arguinTaiWeight β p Y z0 h‖ * ‖L_p β p h‖) := by
              simp [norm_smul]
        _ ≤ Cω * (Real.exp (2 * |β| * Cω * ‖z0‖ + CY) * (‖(2 * β)‖ * Cω)) := by
              gcongr
        _ = B := by
              simp [B, mul_assoc, mul_left_comm, mul_comm]
    have hB_int : Integrable (fun _h : ℝ => B) μ01 :=
      MeasureTheory.integrable_const (μ := μ01) B
    exact MeasureTheory.Integrable.of_bound (μ := μ01) hmeas B hbound
  have hF'_meas : AEStronglyMeasurable (F' z0) μ01 := by
    have hω : Measurable (omega_p p) := measurable_omega_p p
    have hw : Measurable (fun h => arguinTaiWeight β p Y z0 h) :=
      measurable_arguinTaiWeight (β := β) (p := p) (hY := hY) (z := z0)
    have hsmul :
        Measurable (fun h : ℝ => ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) := by
      have hcontL : Continuous (fun h : ℝ => L_p β p h) := by
        unfold L_p reMulCLM omega_p
        fun_prop
      have hcont : Continuous (fun h : ℝ =>
          ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) := by
        rw [continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := (ℂ →L[ℝ] ℝ))]
        intro y
        rw [continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)]
        intro u
        have hLy : Continuous fun h : ℝ => (L_p β p h) y :=
          (continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ) (f := fun h => L_p β p h)).1 hcontL y
        have hLu : Continuous fun h : ℝ => (L_p β p h) u :=
          (continuous_clm_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ) (f := fun h => L_p β p h)).1 hcontL u
        simpa [ContinuousLinearMap.smulRight_apply] using hLy.mul hLu
      exact hcont.measurable
    have hT :
        Measurable (fun h : ℝ =>
          (arguinTaiWeight β p Y z0 h) •
            (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))) :=
      hw.smul hsmul
    let post2 :
        (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) :=
      (ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
        ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM)
    have hpost2 : Measurable (fun T : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) => post2 T) := by
      fun_prop
    have hU :
        Measurable (fun h : ℝ =>
          post2 ((arguinTaiWeight β p Y z0 h) •
            (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))) :=
      hpost2.comp hT
    have hF' : Measurable (F' z0) := by
      have hcont :
          Continuous (fun q : ℂ × (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) => q.1 • q.2) := by
        simpa using
          (continuous_smul :
            Continuous (fun q : ℂ × (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) => q.1 • q.2))
      have hm :
          Measurable (fun h : ℝ =>
            (fun c x => c • x) (omega_p p h)
              (post2 ((arguinTaiWeight β p Y z0 h) •
                (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))) :=
        Continuous.measurable2 (α := ℂ) (β := (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ))) (γ := (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)))
          (δ := ℝ) (c := fun c x => c • x) hcont hω hU
      simpa [F'] using hm
    exact hF'.aestronglyMeasurable
  let Cω : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)
  let K : ℝ := ‖(2 * β)‖ * Cω
  let B : ℝ := Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (Cω * (K * K))
  have h_bound : ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, ‖F' z h‖ ≤ (fun _h : ℝ => B) h := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hz' : ‖z‖ ≤ ‖z0‖ + 1 := le_of_lt (norm_lt_of_mem_ball hz)
    have hw0 :
        arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      have hw := arguinTaiWeight_le_exp_of_bounded (β := β) (p := p) (CY := CY) hYb (z := z) (h := h)
      have hmono :
          Real.exp (2 * |β| * Cω * ‖z‖ + CY)
            ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
        have hβ : 0 ≤ (2 * |β| * Cω : ℝ) := by positivity
        have : 2 * |β| * Cω * ‖z‖ + CY ≤ 2 * |β| * Cω * (‖z0‖ + 1) + CY := by
          have : (2 * |β| * Cω : ℝ) * ‖z‖ ≤ (2 * |β| * Cω : ℝ) * (‖z0‖ + 1) :=
            mul_le_mul_of_nonneg_left hz' hβ
          linarith
        exact (Real.exp_le_exp.mpr this)
      have hw' : arguinTaiWeight β p Y z h ≤ Real.exp (2 * |β| * Cω * ‖z‖ + CY) := by
        simpa [Cω, mul_assoc] using hw
      exact hw'.trans hmono
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hnw : ‖arguinTaiWeight β p Y z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)] using hw0
    have hLp : ‖L_p β p h‖ ≤ K := by
      simpa [K, Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hω : ‖omega_p p h‖ ≤ Cω := by simpa [Cω] using omega_p_norm_le p h
    have hsmul : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ ≤ K * K := by
      have hK : 0 ≤ K := by positivity [K, Cω]
      have h0 : 0 ≤ ‖L_p β p h‖ := norm_nonneg _
      have : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
          ≤ ‖L_p β p h‖ * ‖L_p β p h‖ := norm_smulRight_le (L_p β p h)
      refine this.trans ?_
      exact mul_le_mul hLp hLp h0 hK
    have : ‖F' z h‖ ≤ Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (Cω * (K * K)) := by
      calc
        ‖F' z h‖
            = ‖omega_p p h •
                (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                      ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
                  ((arguinTaiWeight β p Y z h) •
                    (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))‖ := by
                simp [F']
        _ ≤ ‖omega_p p h‖ *
              ‖(((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                      ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
                  ((arguinTaiWeight β p Y z h) •
                    (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))‖ := by
              simpa using
                (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℂ)
                  (E := ℂ) (F := (ℂ →L[ℝ] ℂ))
                  (omega_p p h)
                  (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                        ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
                    ((arguinTaiWeight β p Y z h) •
                      (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))))
        _ ≤ ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖ := by
              gcongr
              simpa [ContinuousLinearMap.comp_assoc] using
                (norm_post_ofRealCLM_comp_le
                  (S :=
                    (arguinTaiWeight β p Y z h) •
                      (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))
        _ ≤ ‖omega_p p h‖ * (‖arguinTaiWeight β p Y z h‖ * ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖) := by
              have hscal :
                  ‖(arguinTaiWeight β p Y z h) •
                      (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖
                    ≤ ‖arguinTaiWeight β p Y z h‖ *
                        ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ := by
                simpa using
                  (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℝ)
                    (E := ℂ) (F := (ℂ →L[ℝ] ℝ))
                    (arguinTaiWeight β p Y z h)
                    (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))
              have := mul_le_mul_of_nonneg_left hscal (by positivity : 0 ≤ ‖omega_p p h‖)
              simpa [mul_assoc, mul_comm, mul_left_comm] using this
        _ ≤ Cω * (Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (K * K)) := by
              gcongr
        _ = Real.exp (2 * |β| * Cω * (‖z0‖ + 1) + CY) * (Cω * (K * K)) := by
              ring_nf
    simpa [B] using this
  have bound_integrable : Integrable (fun _h : ℝ => B) μ01 :=
    MeasureTheory.integrable_const (μ := μ01) B
  have h_diff :
      ∀ᵐ h ∂μ01, ∀ z ∈ Metric.ball z0 1, HasFDerivAt (fun z => F z h) (F' z h) z := by
    refine ae_of_all _ (fun h z hz => ?_)
    have hw :
        HasFDerivAt (fun z => (arguinTaiWeight β p Y z h) • (L_p β p h))
          ((arguinTaiWeight β p Y z h) •
            (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))) z :=
      hasFDerivAt_arguinTaiWeight_smul_L_p (β := β) (p := p) (Y := Y) (h := h) (z := z)
    let post1 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
      (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM
    let post2 : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) :=
      (ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ)) post1
    have hwc :
        HasFDerivAt
            (fun z =>
              post1 ((arguinTaiWeight β p Y z h) • (L_p β p h)))
            (post2 ((arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))) z := by
      change
          HasFDerivAt
            (fun z => post1 ((arguinTaiWeight β p Y z h) • (L_p β p h)))
            (post1.comp
              ((arguinTaiWeight β p Y z h) •
                (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))) z
      exact (post1.hasFDerivAt.comp z hw)
    simpa [F, F', post1, post2] using (hwc.const_smul (omega_p p h))
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := μ01) (F := F) (F' := fun z h => F' z h)
      (x₀ := z0) (s := Metric.ball z0 1) (hs := Metric.ball_mem_nhds z0 ε_pos)
      (bound := fun _h : ℝ => B)
      hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  have hDN :
      (fun x =>
        ∫ h,
          (omega_p p h) • (arguinTaiWeight β p Y x h) • (Complex.ofRealCLM.comp (L_p β p h)) ∂μ01)
        = DN_p β p Y := by
    funext x
    simp [DN_p]
  have hDDN :
      (∫ h,
          (omega_p p h) • (arguinTaiWeight β p Y z0 h) •
            ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp
              ((L_p β p h).smulRight (L_p β p h)) ∂μ01)
        = DDN_p β p Y z0 := by
    simp [DDN_p, ContinuousLinearMap.compL_apply]
  simpa [hDN, hDDN] using hmain

/-- The Arguin–Tai function `F_p : ℂ → ℂ`. -/
noncomputable def F_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ :=
  (N_p β p Y z) / (Z_p β p Y z)

lemma hasFDerivAt_F_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (F_p β p Y) (by
      let DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z0
      let DN : ℂ →L[ℝ] ℂ := DN_p β p Y z0
      let Z0 : ℂ := (Z_p β p Y z0 : ℂ)
      let inv' : ℂ →L[ℝ] ℂ := -((ContinuousLinearMap.mulLeftRight ℝ ℂ) Z0⁻¹) Z0⁻¹
      exact (N_p β p Y z0) • (inv'.comp (Complex.ofRealCLM.comp DZ))
        + (Z0⁻¹) • DN) z0 := by
  let DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z0
  let DN : ℂ →L[ℝ] ℂ := DN_p β p Y z0
  have hZ : HasFDerivAt (Z_p β p Y) DZ z0 :=
    hasFDerivAt_Z_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
  have hN : HasFDerivAt (N_p β p Y) DN z0 :=
    hasFDerivAt_N_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
  have hZC : HasFDerivAt (fun z => (Z_p β p Y z : ℂ)) (Complex.ofRealCLM.comp DZ) z0 := by
    simpa [Function.comp] using (Complex.ofRealCLM.hasFDerivAt.comp z0 hZ)
  have hZ0_ne : (Z_p β p Y z0 : ℂ) ≠ 0 := by
    exact_mod_cast (Z_p_ne_zero_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0))
  have hinv_base :
      HasFDerivAt Inv.inv
        (-((ContinuousLinearMap.mulLeftRight ℝ ℂ) (Z_p β p Y z0 : ℂ)⁻¹) (Z_p β p Y z0 : ℂ)⁻¹)
        (Z_p β p Y z0 : ℂ) :=
    hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) hZ0_ne
  have hinv :
      HasFDerivAt (fun z => ((Z_p β p Y z : ℂ)⁻¹))
        ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ) (Z_p β p Y z0 : ℂ)⁻¹) (Z_p β p Y z0 : ℂ)⁻¹).comp
          (Complex.ofRealCLM.comp DZ))
        z0 := by
    simpa [Function.comp] using (hinv_base.comp z0 hZC)
  have hprod :
      HasFDerivAt (fun z => (N_p β p Y z) * ((Z_p β p Y z : ℂ)⁻¹))
        ((N_p β p Y z0) •
            ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ) (Z_p β p Y z0 : ℂ)⁻¹) (Z_p β p Y z0 : ℂ)⁻¹).comp
              (Complex.ofRealCLM.comp DZ))
          + ((Z_p β p Y z0 : ℂ)⁻¹) • DN)
        z0 := by
    simpa only [Pi.mul_apply] using (hN.mul hinv)
  simpa [F_p, div_eq_mul_inv, DZ, DN, DZ_p, DN_p] using hprod

/-! ## Uniform derivative bounds (crucial for `FDerivLipschitz`) -/

private noncomputable def Cω (p : ℕ) : ℝ := (1 / (2 * Real.sqrt (p : ℝ)) : ℝ)

private lemma Cω_nonneg (p : ℕ) : 0 ≤ Cω p := by
  dsimp [Cω]
  positivity

lemma norm_N_p_le_Cω_mul_Z_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖N_p β p Y z‖ ≤ (Cω p) * (Z_p β p Y z) := by
  classical
  have hintW : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hbound :
      ∀ᵐ h ∂μ01, ‖(omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)‖
        ≤ (Cω p) * (arguinTaiWeight β p Y z h) := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω p := by
      simpa [Cω] using omega_p_norm_le p h
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hw_norm : ‖(arguinTaiWeight β p Y z h : ℂ)‖ = arguinTaiWeight β p Y z h := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
    calc
      ‖(omega_p p h) * (arguinTaiWeight β p Y z h : ℂ)‖
          = ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h : ℂ)‖ := by simp
      _ ≤ (Cω p) * (arguinTaiWeight β p Y z h) := by
        have hn : 0 ≤ arguinTaiWeight β p Y z h := le_of_lt hpos
        calc
          ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h : ℂ)‖
            = ‖omega_p p h‖ * (arguinTaiWeight β p Y z h) := by rw [hw_norm]
          _ ≤ (Cω p) * (arguinTaiWeight β p Y z h) := mul_le_mul_of_nonneg_right hω hn
  have hg : Integrable (fun h => (Cω p) * (arguinTaiWeight β p Y z h)) μ01 :=
    hintW.const_mul (Cω p)
  have hnorm :
      ‖∫ h, (omega_p p h) * (arguinTaiWeight β p Y z h : ℂ) ∂μ01‖
        ≤ ∫ h, (Cω p) * (arguinTaiWeight β p Y z h) ∂μ01 :=
    MeasureTheory.norm_integral_le_of_norm_le hg hbound
  have hR :
      (∫ h, (Cω p) * (arguinTaiWeight β p Y z h) ∂μ01) = (Cω p) * (Z_p β p Y z) := by
    simp [Z_p, MeasureTheory.integral_const_mul]
  simpa [N_p, hR] using hnorm

lemma norm_DZ_p_le_norm_two_mul_beta_mul_Cω_mul_Z_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DZ_p β p Y z‖ ≤ (‖(2 * β)‖ * (Cω p)) * (Z_p β p Y z) := by
  classical
  have hintW : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hbound :
      ∀ᵐ h ∂μ01, ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖
        ≤ (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h) := by
    refine ae_of_all _ (fun h => ?_)
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * (Cω p) := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hw_norm : ‖arguinTaiWeight β p Y z h‖ = arguinTaiWeight β p Y z h := by
      simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
    calc
      ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖
          = ‖arguinTaiWeight β p Y z h‖ * ‖L_p β p h‖ := by simp [norm_smul, mul_comm]
      _ = (arguinTaiWeight β p Y z h) * ‖L_p β p h‖ := by simp [hw_norm]
      _ ≤ (arguinTaiWeight β p Y z h) * (‖(2 * β)‖ * (Cω p)) := by
        exact mul_le_mul_of_nonneg_left hLp (le_of_lt hpos)
      _ = (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
  have hg : Integrable (fun h => (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h)) μ01 :=
    hintW.const_mul (‖(2 * β)‖ * (Cω p))
  have hnorm :
      ‖∫ h, (arguinTaiWeight β p Y z h) • (L_p β p h) ∂μ01‖
        ≤ ∫ h, (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h) ∂μ01 :=
    MeasureTheory.norm_integral_le_of_norm_le hg hbound
  have hR :
      (∫ h, (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h) ∂μ01)
        = (‖(2 * β)‖ * (Cω p)) * (Z_p β p Y z) := by
    simp [Z_p, MeasureTheory.integral_const_mul]
  calc ‖DZ_p β p Y z‖
      = ‖∫ h, (arguinTaiWeight β p Y z h) • (L_p β p h) ∂μ01‖ := by simp [DZ_p]
    _ ≤ ∫ h, (‖(2 * β)‖ * (Cω p)) * (arguinTaiWeight β p Y z h) ∂μ01 := hnorm
    _ = (‖(2 * β)‖ * (Cω p)) * (Z_p β p Y z) := hR

lemma norm_DN_p_le_norm_two_mul_beta_mul_Cω_sq_mul_Z_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DN_p β p Y z‖ ≤ (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (Z_p β p Y z) := by
  classical
  have hintW : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hbound :
      ∀ᵐ h ∂μ01, ‖(omega_p p h) •
          (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h)))‖
        ≤ (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h) := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω p := by
      simpa [Cω] using omega_p_norm_le p h
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * (Cω p) := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hcomp_le :
        ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))‖
          ≤ ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖ :=
      norm_ofRealCLM_comp_le _
    calc
      ‖(omega_p p h) •
          (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h)))‖
          ≤ ‖omega_p p h‖ *
              ‖Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))‖ := by
                simpa using
                  (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℂ)
                    (E := ℂ) (F := ℂ)
                    (omega_p p h)
                    (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))))
      _ ≤ ‖omega_p p h‖ * ‖(arguinTaiWeight β p Y z h) • (L_p β p h)‖ := by gcongr
      _ = ‖omega_p p h‖ * (‖arguinTaiWeight β p Y z h‖ * ‖L_p β p h‖) := by
            simp [norm_smul, mul_assoc, mul_comm]
      _ ≤ (Cω p) * ((arguinTaiWeight β p Y z h) * (‖(2 * β)‖ * (Cω p))) := by
            gcongr
            · exact Cω_nonneg p
            · rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
      _ = (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h) := by
            ring_nf
  have hg : Integrable (fun h => (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h)) μ01 :=
    hintW.const_mul (‖(2 * β)‖ * ((Cω p) * (Cω p)))
  have hnorm :
      ‖∫ h,
          (omega_p p h) • (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))) ∂μ01‖
        ≤ ∫ h, (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01 :=
    MeasureTheory.norm_integral_le_of_norm_le hg hbound
  have hR : ∫ h, (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01
      = (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (Z_p β p Y z) := by
    simp only [Z_p]
    rw [MeasureTheory.integral_const_mul]
  calc
    ‖DN_p β p Y z‖
      = ‖∫ h, (omega_p p h) • (Complex.ofRealCLM.comp ((arguinTaiWeight β p Y z h) • (L_p β p h))) ∂μ01‖ := by simp [DN_p]
    _ ≤ ∫ h, (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01 := hnorm
    _ = (‖(2 * β)‖ * ((Cω p) * (Cω p))) * (Z_p β p Y z) := hR

lemma norm_DDZ_p_le_norm_two_mul_beta_sq_mul_Cω_sq_mul_Z_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DDZ_p β p Y z‖ ≤ (‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p)) * (Z_p β p Y z) := by
  classical
  have hintW : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hbound :
      ∀ᵐ h ∂μ01,
        ‖(arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖
          ≤ ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) := by
    refine ae_of_all _ (fun h => ?_)
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * (Cω p) := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hsmul : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
        ≤ (‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p)) := by
      have h0 : 0 ≤ ‖L_p β p h‖ := norm_nonneg _
      have hK : 0 ≤ (‖(2 * β)‖ * (Cω p) : ℝ) := by positivity [Cω_nonneg p]
      have : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
          ≤ ‖L_p β p h‖ * ‖L_p β p h‖ := norm_smulRight_le (L_p β p h)
      refine this.trans ?_
      exact mul_le_mul hLp hLp h0 hK
    calc
      ‖(arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖
          ≤ ‖arguinTaiWeight β p Y z h‖ *
              ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ := by
                simpa using
                  (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℝ)
                    (E := ℂ) (F := (ℂ →L[ℝ] ℝ))
                    (arguinTaiWeight β p Y z h)
                    (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))
      _ ≤ ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) := by
            rw [Real.norm_eq_abs, abs_of_pos hpos]
            calc
              arguinTaiWeight β p Y z h *
                  ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
                ≤ arguinTaiWeight β p Y z h *
                    ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) := by
                  gcongr
              _ = ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) *
                    arguinTaiWeight β p Y z h := by ring

  have hg :
      Integrable (fun h =>
        ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h)) μ01 :=
    hintW.const_mul ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p)))
  have hnorm :
      ‖∫ h, (arguinTaiWeight β p Y z h) •
            (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)) ∂μ01‖
        ≤ ∫ h, ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01 :=
    MeasureTheory.norm_integral_le_of_norm_le hg hbound
  have hint_eq : ∫ h, ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01
      = ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * ∫ h, arguinTaiWeight β p Y z h ∂μ01 :=
    MeasureTheory.integral_const_mul _ _
  simp only [DDZ_p, Z_p, hint_eq] at hnorm ⊢
  linarith

lemma norm_DDN_p_le_norm_two_mul_beta_sq_mul_Cω_cube_mul_Z_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DDN_p β p Y z‖ ≤ (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (Z_p β p Y z) := by
  classical
  have hintW : Integrable (fun h => arguinTaiWeight β p Y z h) μ01 :=
    integrable_arguinTaiWeight_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hbound :
      ∀ᵐ h ∂μ01,
        ‖(omega_p p h) •
          (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
            ((arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))‖
          ≤ (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) := by
    refine ae_of_all _ (fun h => ?_)
    have hω : ‖omega_p p h‖ ≤ Cω p := by
      simpa [Cω] using omega_p_norm_le p h
    have hpos : 0 < arguinTaiWeight β p Y z h := arguinTaiWeight_pos β p Y z h
    have hLp : ‖L_p β p h‖ ≤ ‖(2 * β)‖ * (Cω p) := by
      simpa [Cω] using (norm_L_p_le (β := β) (p := p) (h := h))
    have hsmul : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
        ≤ (‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p)) := by
      have h0 : 0 ≤ ‖L_p β p h‖ := norm_nonneg _
      have hK : 0 ≤ (‖(2 * β)‖ * (Cω p) : ℝ) := by positivity [Cω_nonneg p]
      have : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖
          ≤ ‖L_p β p h‖ * ‖L_p β p h‖ := norm_smulRight_le (L_p β p h)
      refine this.trans ?_
      exact mul_le_mul hLp hLp h0 hK
    have hpost :
        ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp
            ((arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))‖
          ≤ ‖(arguinTaiWeight β p Y z h) • (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖ := by
      simpa [ContinuousLinearMap.comp_assoc] using
        (norm_post_ofRealCLM_comp_le
          (S :=
            (arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))
    have hscal :
        ‖(arguinTaiWeight β p Y z h) •
            (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖
          ≤ ‖arguinTaiWeight β p Y z h‖ *
              ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ := by
      simpa using
        (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℝ)
          (E := ℂ) (F := (ℂ →L[ℝ] ℝ))
          (arguinTaiWeight β p Y z h)
          (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))
    calc
      ‖(omega_p p h) •
          (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
            ((arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))))‖
          ≤ ‖omega_p p h‖ *
              ‖((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                    ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
                ((arguinTaiWeight β p Y z h) •
                  (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))‖ := by
                simpa using
                  (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ) (𝕜' := ℂ)
                    (E := ℂ) (F := (ℂ →L[ℝ] ℂ))
                    (omega_p p h)
                    (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                          ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
                      ((arguinTaiWeight β p Y z h) •
                        (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))))
      _ ≤ ‖omega_p p h‖ *
            ‖(arguinTaiWeight β p Y z h) •
              (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h))‖ := by
            gcongr; aesop
      _ ≤ ‖omega_p p h‖ * (‖arguinTaiWeight β p Y z h‖ * ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖) := by
            have := mul_le_mul_of_nonneg_left hscal (by positivity : 0 ≤ ‖omega_p p h‖)
            simpa [mul_assoc] using this
      _ ≤ (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) := by
            have hw' : ‖arguinTaiWeight β p Y z h‖ = arguinTaiWeight β p Y z h := by
              simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
            rw [hw']
            have hLp' : ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖ ≤ ‖L_p β p h‖ * ‖L_p β p h‖ :=
              norm_smulRight_le (L_p β p h)
            calc ‖omega_p p h‖ * (arguinTaiWeight β p Y z h * ‖ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)‖)
                ≤ ‖omega_p p h‖ * (arguinTaiWeight β p Y z h * (‖L_p β p h‖ * ‖L_p β p h‖)) := by
                  gcongr
              _ ≤ (Cω p) * (arguinTaiWeight β p Y z h * (‖2 * β‖ * Cω p * (‖2 * β‖ * Cω p))) := by
                  have hLp2 :
                      ‖L_p β p h‖ * ‖L_p β p h‖ ≤ (‖2 * β‖ * Cω p) * (‖2 * β‖ * Cω p) := by
                    refine mul_le_mul hLp hLp (norm_nonneg _) ?_
                    positivity [Cω_nonneg p]
                  have hwLp2 :
                      arguinTaiWeight β p Y z h * (‖L_p β p h‖ * ‖L_p β p h‖)
                        ≤ arguinTaiWeight β p Y z h * ((‖2 * β‖ * Cω p) * (‖2 * β‖ * Cω p)) := by
                    exact mul_le_mul_of_nonneg_left hLp2 (le_of_lt hpos)
                  have hn : 0 ≤ arguinTaiWeight β p Y z h * (‖L_p β p h‖ * ‖L_p β p h‖) := by
                    positivity [le_of_lt hpos]
                  calc
                    ‖omega_p p h‖ * (arguinTaiWeight β p Y z h * (‖L_p β p h‖ * ‖L_p β p h‖))
                        ≤ (Cω p) * (arguinTaiWeight β p Y z h * (‖L_p β p h‖ * ‖L_p β p h‖)) := by
                          exact mul_le_mul_of_nonneg_right hω hn
                    _ ≤ (Cω p) * (arguinTaiWeight β p Y z h * ((‖2 * β‖ * Cω p) * (‖2 * β‖ * Cω p))) := by
                          exact mul_le_mul_of_nonneg_left hwLp2 (Cω_nonneg p)
              _ = (Cω p) * ((‖2 * β‖ * Cω p) * (‖2 * β‖ * Cω p)) * arguinTaiWeight β p Y z h := by
                  ring
  have hg :
      Integrable (fun h =>
        (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h)) μ01 :=
    hintW.const_mul ((Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))))
  have hnorm :
      ‖∫ h,
          (omega_p p h) •
            (((ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] ℝ) (ℂ →L[ℝ] ℂ))
                  ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM))
              ((arguinTaiWeight β p Y z h) •
                (ContinuousLinearMap.smulRight (L_p β p h) (L_p β p h)))) ∂μ01‖
        ≤ ∫ h, (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01 :=
    MeasureTheory.norm_integral_le_of_norm_le hg hbound
  have hsimp : ∫ h, (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * (arguinTaiWeight β p Y z h) ∂μ01
      = (Cω p) * ((‖(2 * β)‖ * (Cω p)) * (‖(2 * β)‖ * (Cω p))) * ∫ h, arguinTaiWeight β p Y z h ∂μ01 := by
    rw [← MeasureTheory.integral_const_mul]
  rw [hsimp] at hnorm
  simpa [DDN_p, Z_p, mul_assoc, mul_left_comm, mul_comm] using hnorm

/-! ## `FDerivLipschitz` for `F_p` -/

/-- A convenient way to prove `FDerivLipschitz`: if the real derivative `fderiv` is differentiable
and its derivative is uniformly bounded, then `fderiv` is globally Lipschitz. -/
lemma FDerivLipschitz.of_fderiv_fderiv_bound
    {F : ℂ → ℂ} {M : ℝ≥0}
    (hF : ∀ z, DifferentiableAt ℝ F z)
    (hF' : Differentiable ℝ (fun z => fderiv ℝ F z))
    (hbound : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ F z) z‖₊ ≤ M) :
    FDerivLipschitz F M := by
  refine ⟨hF, ?_⟩
  simpa using (lipschitzWith_of_nnnorm_fderiv_le (f := fun z => fderiv ℝ F z) hF' hbound)

noncomputable def invDerivBase (Z0 : ℂ) : ℂ →L[ℝ] ℂ :=
  -((ContinuousLinearMap.mulLeftRight ℝ ℂ) Z0⁻¹) Z0⁻¹

noncomputable def DF_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  let DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z
  let DN : ℂ →L[ℝ] ℂ := DN_p β p Y z
  let Z0 : ℂ := (Z_p β p Y z : ℂ)
  let inv' : ℂ →L[ℝ] ℂ := invDerivBase Z0
  (N_p β p Y z) • (inv'.comp (Complex.ofRealCLM.comp DZ)) + (Z0⁻¹) • DN

noncomputable def DF_p_simpl (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  let DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z
  let DN : ℂ →L[ℝ] ℂ := DN_p β p Y z
  let Zr : ℝ := Z_p β p Y z
  (N_p β p Y z) • (Complex.ofRealCLM.comp ((-(Zr ^ 2)⁻¹) • DZ)) + ((Zr⁻¹ : ℂ) • DN)

noncomputable def invZ_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℝ :=
  (Z_p β p Y z)⁻¹

noncomputable def DinZ_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-(Z_p β p Y z ^ 2)⁻¹) • (DZ_p β p Y z)

noncomputable def DDinZ_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) :
    ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  let Zr : ℝ := Z_p β p Y z
  let DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z
  let DDZ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := DDZ_p β p Y z
  let dcoef : ℝ := - (-(2 * Zr) / (Zr ^ 2) ^ 2)
  (-(Zr ^ 2)⁻¹) • DDZ + (dcoef • DZ).smulRight DZ

set_option maxHeartbeats 400000 in
lemma hasFDerivAt_DinZ_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (DinZ_p β p Y) (DDinZ_p β p Y z0) z0 := by
  classical
  have hZ : HasFDerivAt (Z_p β p Y) (DZ_p β p Y z0) z0 :=
    hasFDerivAt_Z_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
  have hDZ : HasFDerivAt (DZ_p β p Y) (DDZ_p β p Y z0) z0 :=
    hasFDerivAt_DZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
  have hZ0_ne : Z_p β p Y z0 ≠ 0 :=
    Z_p_ne_zero_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (Z_p β p Y z0)) (Z_p β p Y z0) := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id (Z_p β p Y z0)).mul (hasDerivAt_id (Z_p β p Y z0)))
  have ht2 : (Z_p β p Y z0) ^ 2 ≠ 0 := by
    simpa [pow_two] using (mul_ne_zero hZ0_ne hZ0_ne)
  have hinvSq :
      HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹)
        (-(2 * (Z_p β p Y z0)) / ((Z_p β p Y z0) ^ 2) ^ 2) (Z_p β p Y z0) := by
    simpa using (HasDerivAt.inv (x := (Z_p β p Y z0)) (c := fun t : ℝ => t ^ 2) (c' := 2 * (Z_p β p Y z0))
      hsq ht2)
  have hcoef1d :
      HasDerivAt (fun t : ℝ => -(t ^ 2)⁻¹)
        (- (-(2 * (Z_p β p Y z0)) / ((Z_p β p Y z0) ^ 2) ^ 2)) (Z_p β p Y z0) := by
    simpa using hinvSq.neg
  have hcoef :
      HasFDerivAt (fun z : ℂ => -(Z_p β p Y z ^ 2)⁻¹)
        ((- (-(2 * (Z_p β p Y z0)) / ((Z_p β p Y z0) ^ 2) ^ 2)) • (DZ_p β p Y z0)) z0 := by
    simpa [Function.comp] using (HasDerivAt.comp_hasFDerivAt (x := z0) hcoef1d hZ)
  have hsmul := (HasFDerivAt.smul (𝕜 := ℝ) (𝕜' := ℝ) hcoef hDZ)
  have hsmul' :
      HasFDerivAt (DinZ_p β p Y)
        (-((Z_p β p Y z0 ^ 2)⁻¹ • DDZ_p β p Y z0) +
            (-((-(2 * Z_p β p Y z0) / (Z_p β p Y z0 ^ 2) ^ 2) • DZ_p β p Y z0)).smulRight
              (DZ_p β p Y z0))
        z0 := by
    simpa [DinZ_p] using hsmul
  refine hsmul'.congr_fderiv ?_
  simp only [DDinZ_p, pow_two, neg_smul]
  ring_nf
  simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, neg_smul, inv_pow, neg_neg,
    add_left_inj]
  ext x x_1 : 2
  simp_all only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, neg_smul]

lemma hasFDerivAt_invZ_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (invZ_p β p Y) (DinZ_p β p Y z0) z0 := by
  have hZ : HasFDerivAt (Z_p β p Y) (DZ_p β p Y z0) z0 :=
    hasFDerivAt_Z_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
  have hZ0_ne : Z_p β p Y z0 ≠ 0 :=
    Z_p_ne_zero_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z0)
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(Z_p β p Y z0 ^ 2)⁻¹) (Z_p β p Y z0) :=
    hasDerivAt_inv hZ0_ne
  simpa [invZ_p, DinZ_p, Function.comp] using (HasDerivAt.comp_hasFDerivAt (x := z0) hinv hZ)

lemma DF_p_simpl_eq'
    (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) :
    DF_p_simpl β p Y z
      = (N_p β p Y z) • (Complex.ofRealCLM.comp (DinZ_p β p Y z))
        + ((invZ_p β p Y z : ℂ) • (DN_p β p Y z)) := by
  simp [DF_p_simpl, invZ_p, DinZ_p]

lemma DF_p_eq_DF_p_simpl (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) :
    DF_p β p Y z = DF_p_simpl β p Y z := by
  classical
  ext u
  set Zr : ℝ := Z_p β p Y z
  set Z0 : ℂ := (Zr : ℂ)
  set DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z
  set DN : ℂ →L[ℝ] ℂ := DN_p β p Y z
  have hL :
      (DF_p β p Y z) u =
        (N_p β p Y z) *
            (-(Z0⁻¹ * Z0⁻¹) * (Complex.ofReal (DZ u)))
          + (Z0⁻¹) * (DN u) := by
    simp [DF_p, invDerivBase, Zr, Z0, DZ, DN, ContinuousLinearMap.mulLeftRight,
      ContinuousLinearMap.comp_apply, mul_assoc]
  have hR :
      (DF_p_simpl β p Y z) u =
        (N_p β p Y z) * (Complex.ofReal (-(Zr ^ 2)⁻¹ * (DZ u)))
          + (Z0⁻¹) * (DN u) := by
    change
      ((N_p β p Y z) • (Complex.ofRealCLM.comp ((-(Zr ^ 2)⁻¹) • DZ))
          + ((Zr⁻¹ : ℂ) • DN)) u =
        (N_p β p Y z) * (Complex.ofReal (-(Zr ^ 2)⁻¹ * (DZ u)))
          + (Z0⁻¹) * (DN u)
    rw [ContinuousLinearMap.add_apply]
    congr 1
  rw [hL, hR]
  have hcoef : -(Z0⁻¹ * Z0⁻¹) = (-(Zr ^ 2)⁻¹ : ℂ) := by
    by_cases hZ : Zr = 0
    · simp [Z0, hZ]
    · have hZc : (Zr : ℂ) ≠ 0 := by exact_mod_cast hZ
      have hsq : (Z0⁻¹) * (Z0⁻¹) = ((Zr ^ 2 : ℝ)⁻¹ : ℂ) := by
        field_simp [Z0, hZc]
        simp [Z0]
      simp [Z0, hsq]
  simp [hcoef, Z0]

lemma hasFDerivAt_F_p_of_bounded'
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (F_p β p Y) (DF_p β p Y z0) z0 := by
  simpa [DF_p, invDerivBase] using
    (hasFDerivAt_F_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0)

/-! ### Second derivative of `DF_p` and a uniform bound -/

private lemma norm_smulRight_le₂_real (L₁ L₂ : ℂ →L[ℝ] ℝ) :
    ‖ContinuousLinearMap.smulRight L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (ContinuousLinearMap.smulRight L₁ L₂) (by positivity) ?_
  intro u
  calc
    ‖(ContinuousLinearMap.smulRight L₁ L₂) u‖ = ‖L₁ u‖ * ‖L₂‖ := by
      simp [ContinuousLinearMap.smulRight_apply, norm_smul, mul_comm]
    _ ≤ (‖L₁‖ * ‖u‖) * ‖L₂‖ := by
      gcongr
      exact L₁.le_opNorm u
    _ = (‖L₁‖ * ‖L₂‖) * ‖u‖ := by
      ring_nf

private lemma norm_smulRight_le₂_clm (L₁ L₂ : ℂ →L[ℝ] ℂ) :
    ‖ContinuousLinearMap.smulRight L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (ContinuousLinearMap.smulRight L₁ L₂) (by positivity) ?_
  intro u
  calc
    ‖(ContinuousLinearMap.smulRight L₁ L₂) u‖ = ‖L₁ u‖ * ‖L₂‖ := by
      simp [ContinuousLinearMap.smulRight_apply, norm_smul, mul_comm]
    _ ≤ (‖L₁‖ * ‖u‖) * ‖L₂‖ := by
      gcongr
      exact L₁.le_opNorm u
    _ = (‖L₁‖ * ‖L₂‖) * ‖u‖ := by
      ring_nf

/-! A lightweight norm bound for the ℂ-action on `ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)`.

We avoid the generic lemma `norm_smul_le` here because it routes through `IsBoundedSMul`/`dist`
and can trigger very expensive typeclass search on higher-order `→L[ℝ]` spaces.
-/
private lemma norm_smul_le_clm_clm (c : ℂ) (T : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) :
    ‖c • T‖ ≤ ‖c‖ * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (c • T) (mul_nonneg (norm_nonneg c) (norm_nonneg T)) ?_
  intro u
  calc
    ‖(c • T) u‖ = ‖c • (T u)‖ := by simp
    _ = ‖c‖ * ‖T u‖ := by simp [norm_smul]
    _ ≤ ‖c‖ * (‖T‖ * ‖u‖) := by
          gcongr
          exact T.le_opNorm u
    _ = (‖c‖ * ‖T‖) * ‖u‖ := by ring_nf

private noncomputable def Kβp (β : ℝ) (p : ℕ) : ℝ := ‖(2 * β)‖ * (Cω p)

private lemma Kβp_nonneg (β : ℝ) (p : ℕ) : 0 ≤ Kβp β p := by
  dsimp [Kβp]
  positivity [Cω_nonneg p]

private noncomputable def M_F_p (β : ℝ) (p : ℕ) : ℝ≥0 :=
  ⟨(6 : ℝ) * (‖(2 * β)‖ * ‖(2 * β)‖) * (Cω p * (Cω p * Cω p)), by
    have : 0 ≤ (‖(2 * β)‖ * ‖(2 * β)‖) := by positivity
    have : 0 ≤ (Cω p * (Cω p * Cω p)) := by positivity [Cω_nonneg p]
    positivity [Cω_nonneg p]⟩

private noncomputable def C_F_p (β : ℝ) (p : ℕ) : ℝ :=
  (‖(2 * β)‖ * ‖(2 * β)‖) * (Cω p * (Cω p * Cω p))

private lemma C_F_p_nonneg (β : ℝ) (p : ℕ) : 0 ≤ C_F_p β p := by
  dsimp [C_F_p]
  positivity [Cω_nonneg p]

private lemma Z_mul_invZ_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    (Z_p β p Y z) * (invZ_p β p Y z) = 1 := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hZne : Z_p β p Y z ≠ 0 := ne_of_gt hZpos
  simp [invZ_p, hZne]

private lemma invZ_mul_Z_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    (invZ_p β p Y z) * (Z_p β p Y z) = 1 := by
  simpa [mul_comm] using
    (Z_mul_invZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))

private lemma norm_post1_comp_le (S : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) :
    ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp S‖ ≤ ‖S‖ := by
  simpa using norm_post_ofRealCLM_comp_le (S := S)

private lemma norm_post1_apply_le (T : ℂ →L[ℝ] ℝ) :
    ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) T‖ ≤ ‖T‖ := by
  simpa using norm_ofRealCLM_comp_le (T := T)

private lemma norm_DinZ_p_le_Kβp_mul_invZ_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DinZ_p β p Y z‖ ≤ (Kβp β p) * (invZ_p β p Y z) := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hZne : Z_p β p Y z ≠ 0 := ne_of_gt hZpos
  have hDZ :
      ‖DZ_p β p Y z‖ ≤ (Kβp β p) * (Z_p β p Y z) := by
    simpa [Kβp] using
      (norm_DZ_p_le_norm_two_mul_beta_mul_Cω_mul_Z_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  calc
    ‖DinZ_p β p Y z‖ = ‖(-(Z_p β p Y z ^ 2)⁻¹)‖ * ‖DZ_p β p Y z‖ := by
      simp [DinZ_p, norm_smul]
    _ = (Z_p β p Y z ^ 2)⁻¹ * ‖DZ_p β p Y z‖ := by
      have hZ2pos : 0 < (Z_p β p Y z) ^ (2 : ℕ) := by
        simpa [pow_two] using (mul_pos hZpos hZpos)
      simp [Real.norm_eq_abs]
    _ ≤ (Z_p β p Y z ^ 2)⁻¹ * ((Kβp β p) * (Z_p β p Y z)) := by
      have hnonneg : 0 ≤ (Z_p β p Y z ^ 2)⁻¹ := by positivity [le_of_lt hZpos]
      exact mul_le_mul_of_nonneg_left hDZ hnonneg
    _ = (Kβp β p) * (invZ_p β p Y z) := by
      have : (Z_p β p Y z ^ 2)⁻¹ * ((Kβp β p) * (Z_p β p Y z))
          = (Kβp β p) * (Z_p β p Y z)⁻¹ := by
        field_simp [pow_two, hZne]

      simp [invZ_p, this]

set_option maxHeartbeats 600000 in
private lemma norm_DDinZ_p_le_three_mul_Kβp_sq_mul_invZ_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DDinZ_p β p Y z‖ ≤ (3 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
  classical
  set Zr : ℝ := Z_p β p Y z
  have hZpos : 0 < Zr := by
    simpa [Zr] using
      (Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hZne : Zr ≠ 0 := ne_of_gt hZpos
  set DZ : ℂ →L[ℝ] ℝ := DZ_p β p Y z
  set DDZ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := DDZ_p β p Y z
  have hDZ : ‖DZ‖ ≤ (Kβp β p) * Zr := by
    simpa [DZ, Zr, Kβp] using
      (norm_DZ_p_le_norm_two_mul_beta_mul_Cω_mul_Z_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hDDZ : ‖DDZ‖ ≤ (Kβp β p * Kβp β p) * Zr := by
    simpa [DDZ, Zr, Kβp, mul_assoc, mul_left_comm, mul_comm] using
      (norm_DDZ_p_le_norm_two_mul_beta_sq_mul_Cω_sq_mul_Z_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hZ2pos : 0 < Zr ^ (2 : ℕ) := by
    simpa [pow_two] using (mul_pos hZpos hZpos)
  have hdcoef : ‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ = (2 : ℝ) / (Zr ^ (3 : ℕ)) := by
    have hZrpos : 0 < Zr := hZpos
    have hZabs : |Zr| = Zr := abs_of_pos hZpos
    have hx : (- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ) = (2 : ℝ) / (Zr ^ (3 : ℕ)) := by
      field_simp [pow_succ, pow_two, hZne]
    have hpos : 0 < (2 : ℝ) / (Zr ^ (3 : ℕ)) := by positivity [hZrpos]
    simp [hx, Real.norm_eq_abs, hZabs]
  have hterm1 :
      ‖(-(Zr ^ 2)⁻¹) • DDZ‖ ≤ (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
    have hsmul :
        ‖((-(Zr ^ 2)⁻¹ : ℝ) • DDZ)‖ ≤ ‖(-(Zr ^ 2)⁻¹ : ℝ)‖ * ‖DDZ‖ := by
      refine ContinuousLinearMap.opNorm_le_bound
        ((-(Zr ^ 2)⁻¹ : ℝ) • DDZ) (mul_nonneg (norm_nonneg (-(Zr ^ 2)⁻¹ : ℝ)) (norm_nonneg DDZ)) ?_
      intro u
      calc
        ‖(((-(Zr ^ 2)⁻¹ : ℝ) • DDZ) u)‖ = ‖(-(Zr ^ 2)⁻¹ : ℝ) • (DDZ u)‖ := by simp
        _ = ‖(-(Zr ^ 2)⁻¹ : ℝ)‖ * ‖DDZ u‖ := by simp [norm_smul]
        _ ≤ ‖(-(Zr ^ 2)⁻¹ : ℝ)‖ * (‖DDZ‖ * ‖u‖) := by
              gcongr
              exact DDZ.le_opNorm u
        _ = (‖(-(Zr ^ 2)⁻¹ : ℝ)‖ * ‖DDZ‖) * ‖u‖ := by ring
    have hcoef : ‖(-(Zr ^ 2)⁻¹ : ℝ)‖ = (Zr ^ 2)⁻¹ := by
      have hpos : 0 < (Zr ^ 2)⁻¹ := by positivity [hZ2pos]
      simp [Real.norm_eq_abs]
    calc
      ‖(-(Zr ^ 2)⁻¹) • DDZ‖
          ≤ (Zr ^ 2)⁻¹ * ‖DDZ‖ := by simpa [hcoef] using hsmul
      _ ≤ (Zr ^ 2)⁻¹ * ((Kβp β p * Kβp β p) * Zr) := by
            have hnonneg : 0 ≤ (Zr ^ 2)⁻¹ := by positivity [le_of_lt hZ2pos]
            exact mul_le_mul_of_nonneg_left hDDZ hnonneg
      _ = (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
            have : (Zr ^ 2)⁻¹ * ((Kβp β p * Kβp β p) * Zr) =
                (Kβp β p * Kβp β p) * Zr⁻¹ := by
              field_simp [pow_two, hZne]
            simp [invZ_p, Zr, this]
  have hterm2 :
      ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ‖
        ≤ (2 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
    have hsr :
        ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ‖
          ≤ ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ)‖ * ‖DZ‖ :=
      norm_smulRight_le₂_real ((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ) DZ
    have hcoefDZ :
        ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ)‖
          ≤ ‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ * ‖DZ‖ := by
      have h :=
        (NormedSpace.norm_smul_le (a := (- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)) (b := DZ))
      have hden : 0 ≤ (Zr ^ 2) ^ (2 : ℕ) := by positivity
      simpa [Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_of_nonneg hden, mul_assoc, mul_left_comm,
        mul_comm] using h
    have hDZ2 : ‖DZ‖ * ‖DZ‖ ≤ ((Kβp β p) * Zr) * ((Kβp β p) * Zr) := by
      have h0 : 0 ≤ ‖DZ‖ := norm_nonneg _
      have h1 : 0 ≤ (Kβp β p) * Zr := by
        have : 0 ≤ Kβp β p := Kβp_nonneg β p
        positivity [this, le_of_lt hZpos]
      exact mul_le_mul hDZ hDZ h0 h1
    calc
      ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ‖
          ≤ ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ)‖ * ‖DZ‖ := hsr
      _ ≤ (‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ * ‖DZ‖) * ‖DZ‖ := by
            gcongr
      _ = ‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ * (‖DZ‖ * ‖DZ‖) := by ring
      _ ≤ ‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ * (((Kβp β p) * Zr) * ((Kβp β p) * Zr)) := by
            gcongr
      _ = (2 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
            have hdcoef : ‖(- (-(2 * Zr) / (Zr ^ 2) ^ 2) : ℝ)‖ = 2 * Zr / (Zr ^ 2) ^ 2 := by
              have hnum : 0 < 2 * Zr := by positivity [hZpos]
              have hden : 0 < (Zr ^ 2) ^ 2 := by positivity [hZ2pos]
              simp only [Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hnum, abs_of_pos hden]
            rw [hdcoef]
            have hinvZ : invZ_p β p Y z = Zr⁻¹ := by simp [invZ_p, Zr]
            rw [hinvZ]
            field_simp [pow_two, pow_succ, hZne]
  have hmain :
      ‖DDinZ_p β p Y z‖
        ≤ (Kβp β p * Kβp β p) * (invZ_p β p Y z)
          + (2 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z) := by
    have htri :
        ‖(-(Zr ^ 2)⁻¹) • DDZ + ((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ‖
          ≤ ‖(-(Zr ^ 2)⁻¹) • DDZ‖
            + ‖((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ‖ := by
        exact
          ContinuousLinearMap.opNorm_add_le (-(Zr ^ 2)⁻¹ • DDZ)
            ((-(-(2 * Zr) / (Zr ^ 2) ^ 2) • DZ).smulRight DZ)
    have hdef :
        DDinZ_p β p Y z =
          (-(Zr ^ 2)⁻¹) • DDZ + ((- (-(2 * Zr) / (Zr ^ 2) ^ 2)) • DZ).smulRight DZ := by
      simp [DDinZ_p, Zr, DZ, DDZ]
    simpa [hdef] using (htri.trans (add_le_add hterm1 hterm2))
  have : (Kβp β p * Kβp β p) * invZ_p β p Y z
        + (2 : ℝ) * (Kβp β p * Kβp β p) * invZ_p β p Y z
      = (3 : ℝ) * (Kβp β p * Kβp β p) * invZ_p β p Y z := by ring
  simpa [this] using hmain

private lemma bound_t1_DDF_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖(N_p β p Y z) •
        (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z))‖
      ≤ (3 : ℝ) * (C_F_p β p) := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hN : ‖N_p β p Y z‖ ≤ (Cω p) * (Z_p β p Y z) :=
    (norm_N_p_le_Cω_mul_Z_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hDDinZ :
      ‖DDinZ_p β p Y z‖ ≤ (3 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z) :=
    norm_DDinZ_p_le_three_mul_Kβp_sq_mul_invZ_p
      (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hpost : ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z)‖
      ≤ ‖DDinZ_p β p Y z‖ :=
    norm_post1_comp_le (S := DDinZ_p β p Y z)
  have hsmul :
      ‖(N_p β p Y z) •
          (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z))‖
        ≤ ‖N_p β p Y z‖ *
            ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z)‖ := by
    simpa using
      (norm_smul_le_clm_clm (c := N_p β p Y z)
        (T := ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z)))
  have hcancel : (Z_p β p Y z) * (invZ_p β p Y z) = 1 :=
    Z_mul_invZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  calc
    ‖(N_p β p Y z) •
        (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z))‖
        ≤ ‖N_p β p Y z‖ * ‖DDinZ_p β p Y z‖ := by
          have : ‖N_p β p Y z‖ *
                ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).comp (DDinZ_p β p Y z)‖
              ≤ ‖N_p β p Y z‖ * ‖DDinZ_p β p Y z‖ :=
            mul_le_mul_of_nonneg_left hpost (norm_nonneg _)
          exact le_trans hsmul this
    _ ≤ ((Cω p) * (Z_p β p Y z)) * ((3 : ℝ) * (Kβp β p * Kβp β p) * (invZ_p β p Y z)) := by
          have h0 : 0 ≤ ‖DDinZ_p β p Y z‖ :=
            ContinuousLinearMap.opNorm_nonneg (DDinZ_p β p Y z)
          have hA : 0 ≤ (Cω p) * (Z_p β p Y z) := by
            have : 0 ≤ (Cω p) := Cω_nonneg p
            have : 0 ≤ (Z_p β p Y z) := le_of_lt hZpos
            positivity
          exact mul_le_mul hN hDDinZ h0 hA
    _ = (3 : ℝ) * (C_F_p β p) := by
          dsimp [C_F_p, Kβp]
          simp [mul_assoc, mul_left_comm, mul_comm]
          ring_nf
          aesop

private lemma bound_t2_DDF_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖(DN_p β p Y z).smulRight (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z))‖
      ≤ (C_F_p β p) := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hDN : ‖DN_p β p Y z‖ ≤ (‖(2 * β)‖ * (Cω p * Cω p)) * (Z_p β p Y z) :=
    (norm_DN_p_le_norm_two_mul_beta_mul_Cω_sq_mul_Z_p
      (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hDinZ : ‖DinZ_p β p Y z‖ ≤ (Kβp β p) * (invZ_p β p Y z) :=
    norm_DinZ_p_le_Kβp_mul_invZ_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hpost : ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z)‖
      ≤ ‖DinZ_p β p Y z‖ :=
    norm_post1_apply_le (T := DinZ_p β p Y z)
  have hsr :
      ‖(DN_p β p Y z).smulRight (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z))‖
        ≤ ‖DN_p β p Y z‖ * ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z)‖ := by
    simpa [ContinuousLinearMap.smulRight] using
      (norm_smulRight_le₂_clm (DN_p β p Y z)
        (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z)))
  have hcancel : (Z_p β p Y z) * (invZ_p β p Y z) = 1 :=
    Z_mul_invZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  calc
    ‖(DN_p β p Y z).smulRight (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z))‖
        ≤ ‖DN_p β p Y z‖ * ‖DinZ_p β p Y z‖ := by
          have : ‖DN_p β p Y z‖ * ‖((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM) (DinZ_p β p Y z)‖
              ≤ ‖DN_p β p Y z‖ * ‖DinZ_p β p Y z‖ :=
            mul_le_mul_of_nonneg_left hpost (norm_nonneg _)
          exact le_trans hsr this
    _ ≤ ((‖(2 * β)‖ * (Cω p * Cω p)) * (Z_p β p Y z)) * ((Kβp β p) * (invZ_p β p Y z)) := by
          have h0 : 0 ≤ ‖DinZ_p β p Y z‖ := norm_nonneg _
          have hA : 0 ≤ (‖(2 * β)‖ * (Cω p * Cω p)) * (Z_p β p Y z) := by
            have : 0 ≤ ‖(2 * β)‖ * (Cω p * Cω p) := by positivity [Cω_nonneg p]
            have : 0 ≤ (Z_p β p Y z) := le_of_lt hZpos
            positivity
          exact mul_le_mul hDN hDinZ h0 hA
    _ = C_F_p β p := by
          dsimp [C_F_p, Kβp]
          simp [mul_assoc, mul_left_comm, mul_comm]
          ring_nf
          aesop

private lemma bound_t3_DDF_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖(invZ_p β p Y z : ℂ) • (DDN_p β p Y z)‖ ≤ (C_F_p β p) := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hinvZ_pos : 0 < invZ_p β p Y z := by
    simpa [invZ_p] using inv_pos.2 hZpos
  have hinvZ_nonneg : 0 ≤ invZ_p β p Y z := le_of_lt hinvZ_pos
  have hcancel : (invZ_p β p Y z) * (Z_p β p Y z) = 1 :=
    invZ_mul_Z_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hDDN :
      ‖DDN_p β p Y z‖ ≤ (Cω p) * ((Kβp β p) * (Kβp β p)) * (Z_p β p Y z) := by
    simpa [Kβp, mul_assoc, mul_left_comm, mul_comm] using
      (norm_DDN_p_le_norm_two_mul_beta_sq_mul_Cω_cube_mul_Z_p
        (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hsmul :
      ‖(invZ_p β p Y z : ℂ) • (DDN_p β p Y z)‖
        ≤ ‖(invZ_p β p Y z : ℂ)‖ * ‖DDN_p β p Y z‖ := by
    simpa using
      (norm_smul_le_clm_clm (c := (invZ_p β p Y z : ℂ)) (T := DDN_p β p Y z))
  have hinvZ_norm : ‖(invZ_p β p Y z : ℂ)‖ = invZ_p β p Y z := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hinvZ_nonneg]
  calc
    ‖(invZ_p β p Y z : ℂ) • (DDN_p β p Y z)‖
        ≤ ‖(invZ_p β p Y z : ℂ)‖ * ‖DDN_p β p Y z‖ := hsmul
    _ = (invZ_p β p Y z) * ‖DDN_p β p Y z‖ := by simp; grind
    _ ≤ (invZ_p β p Y z) * ((Cω p) * ((Kβp β p) * (Kβp β p)) * (Z_p β p Y z)) := by
          exact mul_le_mul_of_nonneg_left hDDN hinvZ_nonneg
    _ = C_F_p β p := by
          dsimp [C_F_p, Kβp]
          simp [mul_assoc, mul_left_comm, mul_comm]
          ring_nf
          grind

private lemma bound_t4_DDF_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖((Complex.ofRealCLM.comp (DinZ_p β p Y z)).smulRight (DN_p β p Y z))‖ ≤ (C_F_p β p) := by
  have hZpos : 0 < Z_p β p Y z :=
    Z_p_pos_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hcancel : (invZ_p β p Y z) * (Z_p β p Y z) = 1 :=
    invZ_mul_Z_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hDinZ : ‖DinZ_p β p Y z‖ ≤ (Kβp β p) * (invZ_p β p Y z) :=
    norm_DinZ_p_le_Kβp_mul_invZ_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z)
  have hDN : ‖DN_p β p Y z‖ ≤ (‖(2 * β)‖ * (Cω p * Cω p)) * (Z_p β p Y z) := by
    simpa using
      (norm_DN_p_le_norm_two_mul_beta_mul_Cω_sq_mul_Z_p
        (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have hsr :
      ‖(Complex.ofRealCLM.comp (DinZ_p β p Y z)).smulRight (DN_p β p Y z)‖
        ≤ ‖Complex.ofRealCLM.comp (DinZ_p β p Y z)‖ * ‖DN_p β p Y z‖ := by
    simpa [ContinuousLinearMap.smulRight] using
      (norm_smulRight_le₂_clm (Complex.ofRealCLM.comp (DinZ_p β p Y z)) (DN_p β p Y z))
  have hpost : ‖Complex.ofRealCLM.comp (DinZ_p β p Y z)‖ ≤ ‖DinZ_p β p Y z‖ := by
    simpa using (norm_ofRealCLM_comp_le (DinZ_p β p Y z))
  calc
    ‖(Complex.ofRealCLM.comp (DinZ_p β p Y z)).smulRight (DN_p β p Y z)‖
        ≤ ‖DinZ_p β p Y z‖ * ‖DN_p β p Y z‖ := by
          have : ‖Complex.ofRealCLM.comp (DinZ_p β p Y z)‖ * ‖DN_p β p Y z‖
              ≤ ‖DinZ_p β p Y z‖ * ‖DN_p β p Y z‖ :=
            mul_le_mul_of_nonneg_right hpost (norm_nonneg _)
          exact le_trans hsr this
    _ ≤ ((Kβp β p) * (invZ_p β p Y z)) * ((‖(2 * β)‖ * (Cω p * Cω p)) * (Z_p β p Y z)) := by
          have h0 : 0 ≤ ‖DN_p β p Y z‖ := norm_nonneg _
          have hA : 0 ≤ (Kβp β p) * (invZ_p β p Y z) := by
            have : 0 ≤ Kβp β p := Kβp_nonneg β p
            have : 0 ≤ invZ_p β p Y z := by
              have : 0 < invZ_p β p Y z := by simpa [invZ_p] using inv_pos.2 hZpos
              exact le_of_lt this
            (expose_names; exact Left.mul_nonneg this_1 this)
          exact mul_le_mul hDinZ hDN (norm_nonneg _) hA
    _ = C_F_p β p := by
          dsimp [C_F_p, Kβp]
          field_simp [hcancel]
          ring_nf
          simp; grind

noncomputable def DDF_p (β : ℝ) (p : ℕ) (Y : ℝ → ℝ) (z : ℂ) :
    ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  let post1 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM
  let N : ℂ := N_p β p Y z
  let DN : ℂ →L[ℝ] ℂ := DN_p β p Y z
  let invZ : ℂ := (invZ_p β p Y z : ℂ)
  let DinZ : ℂ →L[ℝ] ℝ := DinZ_p β p Y z
  let DDN : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := DDN_p β p Y z
  let DDinZ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := DDinZ_p β p Y z
  (N • (post1.comp DDinZ) + (DN).smulRight (post1 DinZ))
    + ((invZ • DDN) + ((Complex.ofRealCLM.comp DinZ)).smulRight DN)

set_option maxHeartbeats 600000 in
lemma hasFDerivAt_DF_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z0 : ℂ) :
    HasFDerivAt (DF_p β p Y) (DDF_p β p Y z0) z0 := by
  classical
  have hDF_simpl :
      HasFDerivAt (DF_p_simpl β p Y) (DDF_p β p Y z0) z0 := by
    let post1 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
      (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM
    have hN : HasFDerivAt (N_p β p Y) (DN_p β p Y z0) z0 :=
      hasFDerivAt_N_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
    have hDN : HasFDerivAt (DN_p β p Y) (DDN_p β p Y z0) z0 :=
      hasFDerivAt_DN_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
    have hDinZ : HasFDerivAt (DinZ_p β p Y) (DDinZ_p β p Y z0) z0 :=
      hasFDerivAt_DinZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
    have hinvZ : HasFDerivAt (invZ_p β p Y) (DinZ_p β p Y z0) z0 :=
      hasFDerivAt_invZ_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z0
    have hpostDinZ :
        HasFDerivAt (fun z => post1 (DinZ_p β p Y z)) (post1.comp (DDinZ_p β p Y z0)) z0 := by
      change
        HasFDerivAt (fun z => post1 (DinZ_p β p Y z)) (post1.comp (DDinZ_p β p Y z0)) z0
      exact (post1.hasFDerivAt.comp z0 hDinZ)
    have hinvZC :
        HasFDerivAt (fun z => (invZ_p β p Y z : ℂ))
          (Complex.ofRealCLM.comp (DinZ_p β p Y z0)) z0 := by
      simpa [Function.comp] using (Complex.ofRealCLM.hasFDerivAt.comp z0 hinvZ)
    have hterm1 :
        HasFDerivAt (fun z => (N_p β p Y z) • (post1 (DinZ_p β p Y z)))
          ((N_p β p Y z0) • (post1.comp (DDinZ_p β p Y z0))
            + (DN_p β p Y z0).smulRight (post1 (DinZ_p β p Y z0))) z0 := by
      simpa using (HasFDerivAt.smul (𝕜 := ℝ) (𝕜' := ℂ) hN hpostDinZ)
    have hterm2 :
        HasFDerivAt (fun z => ((invZ_p β p Y z : ℂ) • (DN_p β p Y z)))
          (((invZ_p β p Y z0 : ℂ) • (DDN_p β p Y z0))
            + (Complex.ofRealCLM.comp (DinZ_p β p Y z0)).smulRight (DN_p β p Y z0)) z0 := by
      simpa using (HasFDerivAt.smul (𝕜 := ℝ) (𝕜' := ℂ) hinvZC hDN)
    have hadd := hterm1.add hterm2
    have hfun_add :
        (fun z => (N_p β p Y z) • (Complex.ofRealCLM.comp (DinZ_p β p Y z)))
          + (fun z => ((invZ_p β p Y z : ℂ) • (DN_p β p Y z)))
          = DF_p_simpl β p Y := by
      funext z
      simpa [Pi.add_apply, post1] using
        (DF_p_simpl_eq' (β := β) (p := p) (Y := Y) (z := z)).symm
    simpa [DDF_p, hfun_add, post1] using hadd
  have hEq : (DF_p β p Y) = (DF_p_simpl β p Y) := by
    funext z
    exact DF_p_eq_DF_p_simpl (β := β) (p := p) (Y := Y) (z := z)
  simpa [hEq] using hDF_simpl

set_option maxHeartbeats 0 in
lemma nnnorm_DDF_p_le_M_F_p
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) (z : ℂ) :
    ‖DDF_p β p Y z‖₊ ≤ M_F_p β p := by
  classical
  let post1 : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM
  let t1 : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := (N_p β p Y z) • (post1.comp (DDinZ_p β p Y z))
  let t2 : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := (DN_p β p Y z).smulRight (post1 (DinZ_p β p Y z))
  let t3 : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := (invZ_p β p Y z : ℂ) • (DDN_p β p Y z)
  let t4 : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (Complex.ofRealCLM.comp (DinZ_p β p Y z)).smulRight (DN_p β p Y z)
  have ht1 : ‖t1‖ ≤ (3 : ℝ) * (C_F_p β p) := by
    simpa [t1, post1] using
      (bound_t1_DDF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have ht2 : ‖t2‖ ≤ (C_F_p β p) := by
    simpa [t2, post1] using
      (bound_t2_DDF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have ht3 : ‖t3‖ ≤ (C_F_p β p) := by
    simpa [t3] using
      (bound_t3_DDF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have ht4 : ‖t4‖ ≤ (C_F_p β p) := by
    simpa [t4] using
      (bound_t4_DDF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  have htri : ‖t1 + t2 + t3 + t4‖ ≤ ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ := by
    have h12 : ‖t1 + t2‖ ≤ ‖t1‖ + ‖t2‖ := norm_add_le t1 t2
    have h123 : ‖t1 + t2 + t3‖ ≤ ‖t1 + t2‖ + ‖t3‖ := norm_add_le (t1 + t2) t3
    have h1234 : ‖t1 + t2 + t3 + t4‖ ≤ ‖t1 + t2 + t3‖ + ‖t4‖ := norm_add_le (t1 + t2 + t3) t4
    calc
      ‖t1 + t2 + t3 + t4‖ ≤ ‖t1 + t2 + t3‖ + ‖t4‖ := h1234
      _ ≤ (‖t1 + t2‖ + ‖t3‖) + ‖t4‖ := by linarith
      _ ≤ ((‖t1‖ + ‖t2‖) + ‖t3‖) + ‖t4‖ := by
            gcongr
      _ = ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ := by ring
  have hsum : ‖t1 + t2 + t3 + t4‖ ≤ (6 : ℝ) * (C_F_p β p) := by
    have : ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ ≤ (6 : ℝ) * (C_F_p β p) := by
      linarith [ht1, ht2, ht3, ht4]
    exact htri.trans this
  have hDDF : DDF_p β p Y z = t1 + t2 + t3 + t4 := by
    simp only [DDF_p, t1, t2, t3, t4, post1]
    abel
  have hM : (M_F_p β p : ℝ) = (6 : ℝ) * (C_F_p β p) := by
    simp only [M_F_p, C_F_p]
    ring_nf; aesop
  have hsum_real : ‖DDF_p β p Y z‖ ≤ (M_F_p β p : ℝ) := by
    simpa [hDDF, hM] using hsum

  exact_mod_cast hsum_real

/-! ### `FDerivLipschitz` for `F_p` and the associated IBP lemma -/

lemma FDerivLipschitz_F_p_of_bounded
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) :
    FDerivLipschitz (F_p β p Y) (M_F_p β p) := by
  have hF : ∀ z, DifferentiableAt ℝ (F_p β p Y) z := by
    intro z
    exact (hasFDerivAt_F_p_of_bounded' (β := β) (p := p) (hY := hY) (CY := CY) hYb z).differentiableAt
  have hfderiv : (fun z => fderiv ℝ (F_p β p Y) z) = DF_p β p Y := by
    funext z
    exact (hasFDerivAt_F_p_of_bounded' (β := β) (p := p) (hY := hY) (CY := CY) hYb z).fderiv
  have hF' : Differentiable ℝ (fun z => fderiv ℝ (F_p β p Y) z) := by
    have : Differentiable ℝ (DF_p β p Y) := by
      intro z
      exact (hasFDerivAt_DF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z).differentiableAt
    simpa [hfderiv] using this
  have hbound : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ (F_p β p Y) z) z‖₊ ≤ M_F_p β p := by
    intro z
    have : fderiv ℝ (fun z => fderiv ℝ (F_p β p Y) z) z = fderiv ℝ (DF_p β p Y) z := by
      simp [hfderiv]
    have hDDF : fderiv ℝ (DF_p β p Y) z = DDF_p β p Y z :=
      (hasFDerivAt_DF_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb z).fderiv
    simpa [this, hDDF] using
      (nnnorm_DDF_p_le_M_F_p (β := β) (p := p) (hY := hY) (CY := CY) hYb (z := z))
  exact FDerivLipschitz.of_fderiv_fderiv_bound hF hF' hbound

section
open scoped ProbabilityTheory
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂(ℙ : Measure Ω)

theorem approx_integral_by_parts_complex_F_p
    {ξ : Ω → ℂ} (hξ_meas : Measurable ξ)
    (hξ3 : Integrable (fun ω => ‖ξ ω‖ ^ (3 : ℕ)) (ℙ : Measure Ω))
    (hEξ  : 𝔼[ξ] = 0)
    (hEξ2 : 𝔼[(fun ω => (ξ ω) ^ 2)] = 0)
    (β : ℝ) (p : ℕ) {Y : ℝ → ℝ} (hY : Measurable Y)
    (CY : ℝ) (hYb : ∀ h, |Y h| ≤ CY) :
    ‖𝔼[(fun ω => ξ ω * (F_p β p Y (ξ ω)))]
        - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => deriv_zbar (F_p β p Y) (ξ ω))]‖
      ≤ (4 * (M_F_p β p)) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
  simpa using
    (approx_integral_by_parts_complex (ξ := ξ) hξ_meas hξ3 hEξ hEξ2
      (F := (F_p β p Y)) (M := (M_F_p β p))
      (FDerivLipschitz_F_p_of_bounded (β := β) (p := p) (hY := hY) (CY := CY) hYb))
end

end

end SpinGlass
