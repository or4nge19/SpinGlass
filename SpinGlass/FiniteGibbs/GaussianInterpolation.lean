import SpinGlass.GaussianTrace
import Common.Mathlib.Probability.Distributions.Gaussian_Interpolation
import Common.Mathlib.Probability.Distributions.Gaussian_ProdCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Guerra's interpolation on an arbitrary finite state space

For a finite state space `α`, two independent centered Gaussian fields `U, V : Ω → EnergySpace α`
with covariance kernels `K₁, K₂` in the Dirac basis, and a fixed vector `c : EnergySpace α`,
Guerra's interpolated free energy is

`φ(t) = 𝔼 F_n(√t U + √(1-t) V + c)`,  `F_n(H) = (1/n) log ∑_x exp(-H x)`.

It is continuous on `[0,1]`, differentiable on `(0,1)`, and its derivative is the disorder average
of the **Guerra trace**

`φ'(t) = 𝔼 (1/2) ∑_{x,y} (K₁ x y - K₂ x y) · (D²F_n)(H_t)(e_y, e_x)
      = 𝔼 (1/(2n)) [ ∑_x (K₁ - K₂)(x,x) g_x - ∑_{x,y} (K₁ - K₂)(x,y) g_x g_y ]`

with `g` the Gibbs weights of `H_t`. This is Talagrand's Lemma 1.3.? / Lemma 14.4.1 in the
generality needed for the broken replica-symmetry bound, where the state space is
`Σ_N × (branches of a cascade)` and the vector `c` carries the field and the random weights. It
is a direct instance of the Gaussian interpolation trace identity
`ProbabilityTheory.IsGaussian.hasDerivAt_integral_gaussianInterp_eq_sum`.

## Main statements

- `SpinGlass.FiniteGibbs.GaussianField`: a centered Gaussian field with a covariance kernel.
- `SpinGlass.FiniteGibbs.pairLaw`: the joint law of an independent pair on the `L²`-product.
- `SpinGlass.FiniteGibbs.guerraPhi`, `SpinGlass.FiniteGibbs.guerraTrace`.
- `SpinGlass.FiniteGibbs.hasDerivAt_guerraPhi`: **the interpolation derivative**.
- `SpinGlass.FiniteGibbs.guerraTrace_eq`: the Guerra trace in Gibbs form.
- `SpinGlass.FiniteGibbs.continuousOn_guerraPhi`, `SpinGlass.FiniteGibbs.guerraPhi_one_le`:
  continuity on `[0,1]` and **Guerra's comparison** `φ(1) ≤ φ(0) + C` from `φ' ≤ C`.
- `SpinGlass.FiniteGibbs.guerraPhi_one`, `SpinGlass.FiniteGibbs.guerraPhi_zero`: the endpoints.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Gaussian fields with a prescribed kernel -/

/-- A **centered Gaussian field on a finite state space with prescribed covariance kernel**: a
random Hamiltonian `U : Ω → EnergySpace α` whose law under `P` is Gaussian and centered, with
covariance operator of entries `K x y` in the Dirac basis. -/
structure GaussianField (P : Measure Ω) (K : α → α → ℝ) where
  /-- The (random) Hamiltonian. -/
  U : Ω → EnergySpace α
  /-- Measurability of the Hamiltonian. -/
  measU : Measurable U
  /-- The law of `U` is Gaussian. -/
  hU : HasGaussianLaw U P
  /-- Centeredness (mean zero). -/
  mean0 : (∫ x : EnergySpace α, x ∂(P.map U)) = 0
  /-- The covariance operator has kernel `K` in the Dirac basis. -/
  cov_eq : ∀ x y,
    inner ℝ ((covarianceOperator (P.map U)) (std_basis (α := α) x)) (std_basis (α := α) y)
      = K x y

namespace GaussianField

variable {P : Measure Ω} {K : α → α → ℝ} (G : GaussianField (α := α) P K)

lemma isGaussian : IsGaussian (P.map G.U) := G.hU.isGaussian_map

lemma integrable : Integrable G.U P := G.hU.integrable

/-- `𝔼 U = 0`. -/
lemma integral_eq_zero : (∫ ω, G.U ω ∂P) = 0 := by
  have hmap : (∫ x : EnergySpace α, x ∂(P.map G.U)) = ∫ ω, G.U ω ∂P := by
    simpa using (MeasureTheory.integral_map (μ := P) (φ := G.U)
      G.measU.aemeasurable measurable_id.aestronglyMeasurable)
  simpa [hmap] using G.mean0

/-- The coordinates of the covariance operator in the Dirac basis are the kernel entries. -/
lemma covarianceOperator_std_basis_apply (x y : α) :
    (covarianceOperator (P.map G.U) (std_basis (α := α) x)) y = K x y := by
  calc (covarianceOperator (P.map G.U) (std_basis (α := α) x)) y
      = inner ℝ (std_basis (α := α) y)
          (covarianceOperator (P.map G.U) (std_basis (α := α) x)) :=
        (inner_std_basis_apply (α := α) y _).symm
    _ = inner ℝ (covarianceOperator (P.map G.U) (std_basis (α := α) x))
          (std_basis (α := α) y) := by rw [real_inner_comm]
    _ = K x y := G.cov_eq x y

/-- The covariance operator on a Dirac vector, expanded in the Dirac basis. -/
lemma covarianceOperator_apply_std_basis_eq_sum (x : α) :
    covarianceOperator (P.map G.U) (std_basis (α := α) x)
      = ∑ y : α, K x y • std_basis (α := α) y := by
  classical
  ext z
  have hsum : (∑ y : α, K x y • std_basis (α := α) y) z = K x z := by
    simp [std_basis]
  rw [G.covarianceOperator_std_basis_apply x z, hsum]

end GaussianField

/-! ### The joint law of an independent pair -/

/-- The `L²`-product carrying the pair `(U, V)`. -/
abbrev PairSpace (α : Type*) := WithLp 2 (EnergySpace α × EnergySpace α)

variable {P : Measure Ω} {K₁ K₂ : α → α → ℝ}
  (G₁ : GaussianField (α := α) P K₁) (G₂ : GaussianField (α := α) P K₂)

/-- The pair `(U, V)` as a random element of the `L²`-product. -/
def pair : Ω → PairSpace α := fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)

/-- The joint law of the pair `(U, V)`. -/
abbrev pairLaw : Measure (PairSpace α) := P.map (pair G₁ G₂)

lemma measurable_pair : Measurable (pair G₁ G₂) :=
  measurable_toLp_prodMk G₁.measU G₂.measU

/-- The joint law of an independent pair of Gaussian fields is Gaussian. -/
lemma isGaussian_pairLaw (hindep : G₁.U ⟂ᵢ[P] G₂.U) : IsGaussian (pairLaw G₁ G₂) :=
  isGaussian_map_toLp_prodMk G₁.hU G₂.hU hindep

/-- The joint law is centered. -/
lemma pairLaw_mean0 : (∫ p : PairSpace α, p ∂pairLaw G₁ G₂) = 0 := by
  have hint : Integrable (pair G₁ G₂) P := by
    have hpair : Integrable (fun ω => (G₁.U ω, G₂.U ω)) P :=
      G₁.integrable.prodMk G₂.integrable
    have := (WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace α) (β := EnergySpace α)).symm.toContinuousLinearMap.integrable_comp hpair
    exact this
  rw [show pairLaw G₁ G₂ = P.map (pair G₁ G₂) from rfl,
    MeasureTheory.integral_map (f := fun p : PairSpace α => p)
      (measurable_pair G₁ G₂).aemeasurable aestronglyMeasurable_id]
  set e := WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
    (α := EnergySpace α) (β := EnergySpace α) with he
  refine e.injective ?_
  have hcomm := e.toContinuousLinearMap.integral_comp_comm (μ := P) hint
  simp only [ContinuousLinearEquiv.coe_coe] at hcomm
  have hsimp : (fun ω => e (pair G₁ G₂ ω)) = fun ω => (G₁.U ω, G₂.U ω) := rfl
  have hpair : Integrable (fun ω => (G₁.U ω, G₂.U ω)) P := G₁.integrable.prodMk G₂.integrable
  have h1 := (ContinuousLinearMap.fst ℝ (EnergySpace α) (EnergySpace α)).integral_comp_comm hpair
  have h2 := (ContinuousLinearMap.snd ℝ (EnergySpace α) (EnergySpace α)).integral_comp_comm hpair
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h1 h2
  rw [← hcomm, hsimp]
  refine Prod.ext ?_ ?_
  · rw [← h1]; simpa using G₁.integral_eq_zero
  · rw [← h2]; simpa using G₂.integral_eq_zero

/-- The covariance of the joint law on the first block, in the Dirac basis. -/
lemma covarianceOperator_pairLaw_left (hindep : G₁.U ⟂ᵢ[P] G₂.U) (x : α) :
    covarianceOperator (pairLaw G₁ G₂) (WithLp.toLp 2 (std_basis (α := α) x, 0))
      = WithLp.toLp 2 (∑ y : α, K₁ x y • std_basis (α := α) y, 0) := by
  have : IsGaussian (P.map fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) :=
    isGaussian_map_toLp_prodMk G₁.hU G₂.hU hindep
  have := G₁.isGaussian
  have := G₂.isGaussian
  rw [show pairLaw G₁ G₂ = P.map (fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) from rfl,
    covarianceOperator_map_toLp_prodMk_left G₁.measU G₂.measU hindep G₁.integral_eq_zero
      G₂.integral_eq_zero, G₁.covarianceOperator_apply_std_basis_eq_sum]

/-- The covariance of the joint law on the second block, in the Dirac basis. -/
lemma covarianceOperator_pairLaw_right (hindep : G₁.U ⟂ᵢ[P] G₂.U) (x : α) :
    covarianceOperator (pairLaw G₁ G₂) (WithLp.toLp 2 (0, std_basis (α := α) x))
      = WithLp.toLp 2 (0, ∑ y : α, K₂ x y • std_basis (α := α) y) := by
  have : IsGaussian (P.map fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) :=
    isGaussian_map_toLp_prodMk G₁.hU G₂.hU hindep
  have := G₁.isGaussian
  have := G₂.isGaussian
  rw [show pairLaw G₁ G₂ = P.map (fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) from rfl,
    covarianceOperator_map_toLp_prodMk_right G₁.measU G₂.measU hindep G₁.integral_eq_zero
      G₂.integral_eq_zero, G₂.covarianceOperator_apply_std_basis_eq_sum]

/-! ### Growth of the free-energy density -/

/-- The growth constant `C_n = max (2/n) (log |α| + 1)`. -/
def growthConst (α : Type*) [Fintype α] (n : ℕ) : ℝ :=
  max (2 / (n : ℝ)) (Real.log (Fintype.card α) + 1)

lemma growthConst_nonneg (n : ℕ) : 0 ≤ growthConst α n :=
  le_max_of_le_left (by positivity)

variable [Nonempty α]

lemma abs_free_energy_density_le_growth (n : ℕ) (z : EnergySpace α) :
    |free_energy_density (α := α) n z| ≤ growthConst α n * (1 + ‖z‖) ^ 1 := by
  rw [pow_one]
  refine (abs_free_energy_density_le (α := α) n z).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

lemma norm_fderiv_free_energy_density_le_growth (n : ℕ) (z : EnergySpace α) :
    ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) z‖
      ≤ growthConst α n * (1 + ‖z‖) ^ 1 := by
  rw [pow_one]
  have h1 : (1 : ℝ) / (n : ℝ) ≤ 2 / (n : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg n)
  calc ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) z‖
      ≤ 1 / (n : ℝ) := norm_fderiv_free_energy_density_le (α := α) n z
    _ ≤ growthConst α n := h1.trans (le_max_left _ _)
    _ = growthConst α n * 1 := (mul_one _).symm
    _ ≤ growthConst α n * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) (growthConst_nonneg n)

lemma norm_fderiv_fderiv_free_energy_density_le_growth (n : ℕ) (z : EnergySpace α) :
    ‖fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H)) z‖
      ≤ growthConst α n * (1 + ‖z‖) ^ 1 := by
  rw [pow_one]
  calc ‖fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H)) z‖
      ≤ 2 / (n : ℝ) := norm_fderiv_fderiv_free_energy_density_le (α := α) n z
    _ ≤ growthConst α n := le_max_left _ _
    _ = growthConst α n * 1 := (mul_one _).symm
    _ ≤ growthConst α n * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) (growthConst_nonneg n)

/-! ### The interpolated free energy and the Guerra trace -/

/-- **Guerra's interpolated free energy** `φ(t) = 𝔼 F_n(√t U + √(1-t) V + c)`. -/
def guerraPhi (c : EnergySpace α) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ p : PairSpace α, free_energy_density (α := α) n (gaussianInterp t p + c) ∂pairLaw G₁ G₂

/-- **The Guerra trace** of two kernels at a Hamiltonian `H`:
`(1/2) ∑_{x,y} (K₁ x y - K₂ x y) (D²F_n)(H)(e_y, e_x)`. -/
def guerraTrace (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : α, ∑ y : α, (K₁ x y - K₂ x y)
    * hessian_free_energy (α := α) n H (std_basis (α := α) y) (std_basis (α := α) x)

omit [Nonempty α] in
/-- The Guerra trace in Gibbs form:
`(1/(2n)) [∑_x (K₁ - K₂)(x,x) g_x - ∑_{x,y} (K₁ - K₂)(x,y) g_x g_y]`. -/
lemma guerraTrace_eq (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) :
    guerraTrace K₁ K₂ n H
      = (1 / (2 * (n : ℝ))) * ((∑ x : α, (K₁ x x - K₂ x x) * gibbs_pmf (α := α) H x)
          - ∑ x : α, ∑ y : α, (K₁ x y - K₂ x y)
              * (gibbs_pmf (α := α) H x * gibbs_pmf (α := α) H y)) := by
  classical
  unfold guerraTrace
  have hpt : ∀ x y : α, (K₁ x y - K₂ x y)
      * hessian_free_energy (α := α) n H (std_basis (α := α) y) (std_basis (α := α) x)
      = (1 / (n : ℝ)) * ((K₁ x y - K₂ x y) * (gibbs_pmf (α := α) H y * (if x = y then 1 else 0))
          - (K₁ x y - K₂ x y) * (gibbs_pmf (α := α) H x * gibbs_pmf (α := α) H y)) := by
    intro x y
    rw [hessian_free_energy_std_basis_eq]
    have : (std_basis (α := α) x) y = if x = y then 1 else 0 := by simp [std_basis]
    rw [this]
    ring
  simp_rw [hpt, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hdiag : ∀ x : α, (∑ y : α, (K₁ x y - K₂ x y)
      * (gibbs_pmf (α := α) H y * (if x = y then 1 else 0)))
      = (K₁ x x - K₂ x x) * gibbs_pmf (α := α) H x := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  simp_rw [hdiag]
  ring

/-- The Hessian entries along the path are bounded, hence integrable. -/
lemma integrable_fderiv_fderiv_pairLaw (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ)
    (t : ℝ) (u v : EnergySpace α) :
    Integrable (fun p : PairSpace α =>
        ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
          (gaussianInterp t p + c)) u) v) (pairLaw G₁ G₂) := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  have hcont : Continuous fun p : PairSpace α =>
      ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
        (gaussianInterp t p + c)) u) v := by
    have h2 : Continuous (fderiv ℝ (fderiv ℝ
        (fun H : EnergySpace α => free_energy_density (α := α) n H))) :=
      ((contDiff_free_energy_density (α := α) n).fderiv_right (m := 1) (by simp)).continuous_fderiv
        (by simp)
    exact ((h2.comp ((gaussianInterp t).continuous.add continuous_const)).clm_apply
      continuous_const).clm_apply continuous_const
  refine Integrable.of_bound hcont.aestronglyMeasurable (2 / (n : ℝ) * ‖u‖ * ‖v‖)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  calc |((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
          (gaussianInterp t p + c)) u) v|
      = |hessian_free_energy (α := α) n (gaussianInterp t p + c) u v| := by
        rw [← hessian_free_energy_fderiv_eq_hessian_free_energy]
        rfl
    _ ≤ 2 / (n : ℝ) * ‖u‖ * ‖v‖ := abs_hessian_free_energy_le (α := α) n _ u v

/-- **The interpolation derivative.** For `t ∈ (0,1)`, `φ` is differentiable at `t` with
derivative the disorder average of the Guerra trace along the path. -/
theorem hasDerivAt_guerraPhi (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi G₁ G₂ c n)
      (∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) t := by
  classical
  have := isGaussian_pairLaw G₁ G₂ hindep
  set F : EnergySpace α → ℝ := fun H => free_energy_density (α := α) n H with hF
  set b : OrthonormalBasis α ℝ (EnergySpace α) := EuclideanSpace.basisFun α ℝ with hb
  have hbσ : ∀ x : α, b x = std_basis (α := α) x := fun x => (std_basis_eq_basisFun x).symm
  set u : α → EnergySpace α := fun x => ∑ y : α, K₁ x y • std_basis (α := α) y with hu
  set v : α → EnergySpace α := fun x => ∑ y : α, K₂ x y • std_basis (α := α) y with hv
  have hcovL : ∀ x, covarianceOperator (pairLaw G₁ G₂) (WithLp.toLp 2 (b x, 0))
      = WithLp.toLp 2 (u x, 0) := fun x => by
    rw [hbσ]; exact covarianceOperator_pairLaw_left G₁ G₂ hindep x
  have hcovR : ∀ x, covarianceOperator (pairLaw G₁ G₂) (WithLp.toLp 2 (0, b x))
      = WithLp.toLp 2 (0, v x) := fun x => by
    rw [hbσ]; exact covarianceOperator_pairLaw_right G₁ G₂ hindep x
  have hder := IsGaussian.hasDerivAt_integral_gaussianInterp_eq_sum (P := pairLaw G₁ G₂)
    (pairLaw_mean0 G₁ G₂) b u v hcovL hcovR c F (contDiff_two_free_energy_density (α := α) n)
    (growthConst_nonneg (α := α) n) (abs_free_energy_density_le_growth n)
    (norm_fderiv_free_energy_density_le_growth n)
    (norm_fderiv_fderiv_free_energy_density_le_growth n) ht
  -- identify the derivative with the integrated Guerra trace
  have hpt : ∀ (H : EnergySpace α) (x : α),
      ((fderiv ℝ (fderiv ℝ F) H) (u x)) (b x) - ((fderiv ℝ (fderiv ℝ F) H) (v x)) (b x)
        = ∑ y : α, (K₁ x y - K₂ x y)
            * hessian_free_energy (α := α) n H (std_basis (α := α) y) (std_basis (α := α) x) := by
    intro H x
    simp only [hu, hv, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hbσ]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ((fderiv ℝ (fderiv ℝ F) H) (std_basis (α := α) y)) (std_basis (α := α) x)
        = hessian_free_energy (α := α) n H (std_basis (α := α) y) (std_basis (α := α) x) := by
      rw [← hessian_free_energy_fderiv_eq_hessian_free_energy]
      rfl
    rw [this]
    ring
  have hint : ∀ (x : α) (w : EnergySpace α), Integrable (fun p : PairSpace α =>
      ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) w) (b x)) (pairLaw G₁ G₂) :=
    fun x w => integrable_fderiv_fderiv_pairLaw G₁ G₂ hindep c n t w (b x)
  have hval : (∑ x : α, (1 / 2 : ℝ) *
      ((∫ p : PairSpace α, ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u x)) (b x)
          ∂pairLaw G₁ G₂)
        - ∫ p : PairSpace α, ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v x)) (b x)
          ∂pairLaw G₁ G₂))
      = ∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂ := by
    simp_rw [← integral_sub (hint _ _) (hint _ _), ← integral_const_mul]
    have hint2 : ∀ x ∈ (Finset.univ : Finset α), Integrable (fun p : PairSpace α =>
        (1 / 2 : ℝ) * (((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u x)) (b x)
          - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v x)) (b x))) (pairLaw G₁ G₂) :=
      fun x _ => ((hint x (u x)).sub (hint x (v x))).const_mul _
    rw [← integral_finsetSum _ hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [guerraTrace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hpt, Finset.mul_sum]
  rw [hval] at hder
  exact hder

/-- **`φ` is continuous on `[0,1]`.** -/
theorem continuousOn_guerraPhi (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ) :
    ContinuousOn (guerraPhi G₁ G₂ c n) (Set.Icc (0 : ℝ) 1) := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  exact IsGaussian.continuousOn_integral_gaussianInterp (P := pairLaw G₁ G₂) c
    (fun H => free_energy_density (α := α) n H)
    (contDiff_free_energy_density (α := α) n).continuous (growthConst_nonneg (α := α) n)
    (abs_free_energy_density_le_growth n)

/-- **Guerra's comparison bound**: if the averaged Guerra trace is at most `C` on `(0,1)`, then
`φ(1) ≤ φ(0) + C`. -/
theorem guerraPhi_one_le (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ) {C : ℝ}
    (hC : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) ≤ C) :
    guerraPhi G₁ G₂ c n 1 ≤ guerraPhi G₁ G₂ c n 0 + C := by
  set φ : ℝ → ℝ := guerraPhi G₁ G₂ c n with hφ
  set ψ : ℝ → ℝ := fun t => φ t - C * t with hψ
  have hint : interior (Set.Icc (0 : ℝ) 1) = Set.Ioo (0 : ℝ) 1 := by simp
  have hψ_deriv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt ψ
      ((∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) - C)
      t := by
    intro t ht
    rw [hint] at ht
    exact (hasDerivAt_guerraPhi G₁ G₂ hindep c n ht).sub
      (by simpa using (hasDerivAt_id t).const_mul C)
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) :=
    (continuousOn_guerraPhi G₁ G₂ hindep c n).sub
      (continuous_const.mul continuous_id).continuousOn
  have hψ_anti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hψ_cont
      (fun t ht => (hψ_deriv t ht).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hψ_deriv t ht).deriv]
    rw [hint] at ht
    linarith [hC t ht]
  have := hψ_anti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [hψ, mul_zero, mul_one, sub_zero] at this
  linarith

/-! ### The comparison bound with a `t`-dependent bound on the derivative -/

omit [Nonempty α] in
lemma norm_std_basis (σ : α) : ‖std_basis (α := α) σ‖ = 1 := by
  have h : ‖std_basis (α := α) σ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_std_basis_apply, std_basis_self_apply]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The Guerra trace is bounded, uniformly in the Hamiltonian:
`|trace| ≤ (1/2) ∑_{x,y} |K₁ x y - K₂ x y| · (2/n)`. -/
lemma abs_guerraTrace_le (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) :
    |guerraTrace K₁ K₂ n H|
      ≤ (1 / 2 : ℝ) * ∑ x : α, ∑ y : α, |K₁ x y - K₂ x y| * (2 / (n : ℝ)) := by
  unfold guerraTrace
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_hessian_free_energy_le (α := α) n H (std_basis (α := α) y) (std_basis (α := α) x)
  rwa [norm_std_basis, norm_std_basis, mul_one, mul_one] at this

/-- The Guerra trace is continuous in the Hamiltonian. -/
lemma continuous_guerraTrace (K₁ K₂ : α → α → ℝ) (n : ℕ) :
    Continuous fun H : EnergySpace α => guerraTrace K₁ K₂ n H := by
  unfold guerraTrace
  refine continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_finsetSum _ fun y _ => continuous_const.mul ?_)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ
      (fun H : EnergySpace α => free_energy_density (α := α) n H))) :=
    ((contDiff_free_energy_density (α := α) n).fderiv_right (m := 1) (by simp)).continuous_fderiv
      (by simp)
  have : (fun H : EnergySpace α => hessian_free_energy (α := α) n H
      (std_basis (α := α) y) (std_basis (α := α) x))
      = fun H => ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
        H) (std_basis (α := α) y)) (std_basis (α := α) x) := by
    funext H
    rw [← hessian_free_energy_fderiv_eq_hessian_free_energy]
    rfl
  rw [this]
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

/-- The averaged Guerra trace along the path is continuous in `t`. -/
lemma continuous_integral_guerraTrace (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ) :
    Continuous fun t : ℝ =>
      ∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂ := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  have hcontH := continuous_guerraTrace (α := α) K₁ K₂ n
  have hcontt : ∀ p : PairSpace α, Continuous fun t : ℝ => gaussianInterp t p + c := by
    intro p
    simp_rw [gaussianInterp_apply]
    exact ((Real.continuous_sqrt.smul continuous_const).add
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const)).add
      continuous_const
  refine MeasureTheory.continuous_of_dominated (fun t => (hcontH.comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
    (bound := fun _ => (1 / 2 : ℝ) * ∑ x : α, ∑ y : α, |K₁ x y - K₂ x y| * (2 / (n : ℝ)))
    (fun t => Filter.Eventually.of_forall fun p => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun p => hcontH.comp (hcontt p))
  rw [Real.norm_eq_abs]
  exact abs_guerraTrace_le K₁ K₂ n _

/-- **Guerra's comparison bound with a `t`-dependent bound on the derivative**: if the averaged
Guerra trace is at most `b t` on `(0,1)` with `b` interval integrable, then
`φ(1) - φ(0) ≤ ∫₀¹ b(t) dt`. -/
theorem guerraPhi_one_sub_zero_le (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ)
    {b : ℝ → ℝ}
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) ≤ b t)
    (hbint : IntervalIntegrable b volume 0 1) :
    guerraPhi G₁ G₂ c n 1 - guerraPhi G₁ G₂ c n 0 ≤ ∫ t in (0 : ℝ)..1, b t := by
  set φ' : ℝ → ℝ := fun t =>
    ∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂ with hφ'
  have hftc : ∫ t in (0 : ℝ)..1, φ' t = guerraPhi G₁ G₂ c n 1 - guerraPhi G₁ G₂ c n 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuousOn_guerraPhi G₁ G₂ hindep c n)
      (fun t ht => hasDerivAt_guerraPhi G₁ G₂ hindep c n ht)
      ((continuous_integral_guerraTrace G₁ G₂ hindep c n).intervalIntegrable 0 1)
  rw [← hftc]
  refine intervalIntegral.integral_mono_ae_restrict zero_le_one
    ((continuous_integral_guerraTrace G₁ G₂ hindep c n).intervalIntegrable 0 1) hbint ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc' (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by simp) (by simp)] with t ht htI
  exact hb t (Eq.mpr ht htI)

/-! ### The endpoints -/

omit [Nonempty α] in
lemma gaussianInterp_one (p : PairSpace α) : gaussianInterp 1 p = (WithLp.ofLp p).1 := by
  simp [gaussianInterp_apply]

omit [Nonempty α] in
lemma gaussianInterp_zero (p : PairSpace α) : gaussianInterp 0 p = (WithLp.ofLp p).2 := by
  simp [gaussianInterp_apply]

/-- `φ(1)` is the free energy of the first field. -/
lemma guerraPhi_one (c : EnergySpace α) (n : ℕ) :
    guerraPhi G₁ G₂ c n 1 = ∫ ω, free_energy_density (α := α) n (G₁.U ω + c) ∂P := by
  unfold guerraPhi
  simp_rw [gaussianInterp_one]
  have hmeas : AEStronglyMeasurable
      (fun p : PairSpace α => free_energy_density (α := α) n ((WithLp.ofLp p).1 + c))
      (pairLaw G₁ G₂) :=
    (((contDiff_free_energy_density (α := α) n).continuous.comp
      ((WithLp.prod_continuous_ofLp (p := (2 : ℝ≥0∞)) (α := EnergySpace α)
        (β := EnergySpace α)).fst.add continuous_const))).aestronglyMeasurable
  rw [show pairLaw G₁ G₂ = P.map (pair G₁ G₂) from rfl,
    MeasureTheory.integral_map (measurable_pair G₁ G₂).aemeasurable hmeas]
  rfl

/-- `φ(0)` is the free energy of the second field. -/
lemma guerraPhi_zero (c : EnergySpace α) (n : ℕ) :
    guerraPhi G₁ G₂ c n 0 = ∫ ω, free_energy_density (α := α) n (G₂.U ω + c) ∂P := by
  unfold guerraPhi
  simp_rw [gaussianInterp_zero]
  have hmeas : AEStronglyMeasurable
      (fun p : PairSpace α => free_energy_density (α := α) n ((WithLp.ofLp p).2 + c))
      (pairLaw G₁ G₂) :=
    (((contDiff_free_energy_density (α := α) n).continuous.comp
      ((WithLp.prod_continuous_ofLp (p := (2 : ℝ≥0∞)) (α := EnergySpace α)
        (β := EnergySpace α)).snd.add continuous_const))).aestronglyMeasurable
  rw [show pairLaw G₁ G₂ = P.map (pair G₁ G₂) from rfl,
    MeasureTheory.integral_map (measurable_pair G₁ G₂).aemeasurable hmeas]
  rfl

/-- **Guerra's comparison bound in free-energy form.** -/
theorem integral_free_energy_density_le (hindep : G₁.U ⟂ᵢ[P] G₂.U) (c : EnergySpace α) (n : ℕ)
    {C : ℝ}
    (hC : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p : PairSpace α, guerraTrace K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) ≤ C) :
    (∫ ω, free_energy_density (α := α) n (G₁.U ω + c) ∂P)
      ≤ (∫ ω, free_energy_density (α := α) n (G₂.U ω + c) ∂P) + C := by
  have := guerraPhi_one_le G₁ G₂ hindep c n hC
  rwa [guerraPhi_one, guerraPhi_zero] at this

end

end FiniteGibbs

end SpinGlass
