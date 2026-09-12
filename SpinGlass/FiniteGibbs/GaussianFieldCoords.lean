/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GaussianFieldPullback
import Common.Mathlib.Probability.Distributions.Gaussian.PiGaussian

/-!
# Gaussian fields from independent Gaussian coordinates

A centered Gaussian field on a finite state space `α` is most often given as the linear image of a
finite family of **independent** centered real Gaussians `(Z_c)_{c : ι}` of variances `v_c`:
`U(x) = ∑_c A x c · Z_c`. Its kernel is then

`K(x, y) = ∑_c v_c · A x c · A y c`   (`GaussianField.ofCoords`),

the image under `coordLin A` (`GaussianField.mapCLM`) of the coordinates seen as a field on `ι`
with diagonal kernel (`GaussianField.coordField`), since `L† e_x = A x`
(`adjoint_coordLin_std_basis`). This is the construction of the marks fields of Guerra's
interpolation schemes (Talagrand Vol. II, (14.73) and (14.135)).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] {ι : Type*} [Fintype ι]

/-! ### The linear map from coordinates to Hamiltonians -/

/-- `w ↦ (x ↦ ∑_c A x c · w c)`, as a linear map. -/
def coordLinMap (A : α → ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EnergySpace α where
  toFun w := WithLp.toLp 2 fun x => ∑ c, A x c * w c
  map_add' w w' := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r w := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    change ∑ c, A x c * (r * w c) = r * ∑ c, A x c * w c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_left_comm _ _ _

/-- `w ↦ (x ↦ ∑_c A x c · w c)`, as a continuous linear map. -/
def coordLin (A : α → ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EnergySpace α :=
  LinearMap.toContinuousLinearMap (coordLinMap A)

lemma coordLin_apply (A : α → ι → ℝ) (w : EuclideanSpace ℝ ι) (x : α) :
    coordLin A w x = ∑ c, A x c * w c := rfl

/-- The adjoint on Dirac vectors: `L† e_x = A x`. -/
lemma adjoint_coordLin_std_basis (A : α → ι → ℝ) (x : α) :
    (coordLin A).adjoint (std_basis (α := α) x) = WithLp.toLp 2 (A x) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_std_basis_apply, coordLin_apply,
    EuclideanSpace.real_inner_eq_dotProduct]
  rfl

lemma coordLin_adjoint_std_basis_apply (A : α → ι → ℝ) (x : α) (c : ι) :
    (coordLin A).adjoint (std_basis (α := α) x) c = A x c := by
  rw [adjoint_coordLin_std_basis]

/-! ### The field -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype α] in
/-- **Independent centered Gaussian coordinates** `Z_c ~ N(0, v_c)`, `c : ι`, as a Gaussian field
on `ι` with the diagonal kernel `v`. -/
def GaussianField.coordField [DecidableEq ι] (v : ι → ℝ≥0) (Z : Ω → EuclideanSpace ℝ ι)
    (hZ : Measurable Z)
    (hlaw : P.map Z = (Measure.pi fun c => gaussianReal 0 (v c)).map (WithLp.toLp 2)) :
    GaussianField (α := ι) P (fun c c' => if c = c' then (v c : ℝ) else 0) where
  U := Z
  measU := hZ
  hU := by
    have : IsGaussian (P.map Z) := by rw [hlaw]; infer_instance
    exact IsGaussian.hasGaussianLaw (X := Z)
  mean0 := by
    rw [hlaw, map_pi_gaussianReal_eq_multivariateGaussian, integral_id_multivariateGaussian]
    rfl
  cov_eq := fun c c' => by
    rw [hlaw, inner_covarianceOperator_map_pi_gaussianReal, Finset.sum_eq_single c]
    · by_cases h : c = c'
      · subst h
        simp
      · simp [h, std_basis_apply_of_ne (Ne.symm h)]
    · intro i _ hi
      simp [std_basis_apply_of_ne (Ne.symm hi)]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **The linear image of independent centered Gaussian coordinates is a Gaussian field** with
kernel `K(x, y) = ∑_c v_c · A x c · A y c`: the image of `coordField` under `coordLin A`. -/
def GaussianField.ofCoords [DecidableEq ι] (A : α → ι → ℝ) (v : ι → ℝ≥0)
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : Measurable Z)
    (hlaw : P.map Z = (Measure.pi fun c => gaussianReal 0 (v c)).map (WithLp.toLp 2)) :
    GaussianField (α := α) P (fun x y => ∑ c, (v c : ℝ) * A x c * A y c) :=
  ((GaussianField.coordField v Z hZ hlaw).mapCLM (coordLin A)).copy _ fun x y => by
    simp only [coordLin_adjoint_std_basis_apply]
    symm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl]
      ring
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

@[simp] lemma GaussianField.ofCoords_U [DecidableEq ι] (A : α → ι → ℝ) (v : ι → ℝ≥0)
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : Measurable Z)
    (hlaw : P.map Z = (Measure.pi fun c => gaussianReal 0 (v c)).map (WithLp.toLp 2)) (ω : Ω) :
    (GaussianField.ofCoords A v Z hZ hlaw).U ω = coordLin A (Z ω) := rfl

end

end FiniteGibbs

end SpinGlass
