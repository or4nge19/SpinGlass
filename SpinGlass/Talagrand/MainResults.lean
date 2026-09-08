import SpinGlass.HopfieldConvolution
import SpinGlass.HopfieldLocalization
import SpinGlass.Cascades.GhirlandaGuerra
import SpinGlass.GuerraInequality
import SpinGlass.SKDisorderExists
import SpinGlass.GaussianTrace
import SpinGlass.GuerraDerivativeTrace

/-!
# Talagrand Vol. I–II: main results index

Proved theorems, and the statement-layer `Prop`s that remain to be discharged.
Plans: `Notes/Vol1##.md`, `Notes/Vol2##.md`.

## Proved: Guerra interpolation and bound (Vol. I, §1.3)

The chain is fully general in the covariance profile `ξ`, with the SK and replica-symmetric
kernels as the two instances:

- `trace_overlapCovKernel` — the trace identity for `N · ξ(R₁₂)`, Eq. (1.65). The SK and
  reference traces (`trace_sk`, `trace_simple`) are its specializations.
- `half_trace_sub_overlapCovKernel` / `guerra_trace_sub_overlapCovKernel_eq` — the half-difference
  of two such traces depends only on `ξ₁ - ξ₂`.
- `guerra_trace_sub_rs_eq` — completing the square isolates the overlap defect `⟨(R₁₂ - q)²⟩`.
- `guerra_trace_sub_rs_le` — hence the trace is at most `(β²/4)(1 - q)²`, Eq. (1.71).
- `derivative_value_guerraPhi_eq_trace_integral` — the derivative value is the disorder average
  of that trace. This is *one instance of the general Gaussian interpolation trace identity*
  `IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum` (see below): the interpolated
  Hamiltonian is `Z_t x + h·1` for the general interpolation map `gaussianInterp`, the covariance
  of `disorderPairLaw` is block diagonal with the SK and reference kernels as blocks, and the only
  model-level work left is expanding those blocks in the Dirac basis. No model-specific
  integration by parts remains anywhere in the project.
- `hasDerivAt_guerraPhi_eq_trace_integral` — hence `φ'(t)` equals that trace average
  (dominated differentiation plus the identity above).
- `hasDerivAt_guerraPhi_le`, `deriv_guerraPhi_le` — `φ'(t) ≤ (β²/4)(1 - q)²` on `(0,1)`.
- `continuousOn_guerraPhi` — `φ` is continuous on `[0,1]` (dominated convergence).
- `guerraPhi_one_le`, `integral_free_energy_density_le` — **Guerra's bound**, Theorem 1.3.7:
  the SK free-energy density is at most the replica-symmetric one plus `(β²/4)(1 - q)²`.
- `exists_guerra_bound` — the same, with the disorder constructed, so the bound is unconditional.

## Proved: the general Gaussian second-order calculus (Vol. I, App. A.3; Vol. II, §8.2)

These are stated for an arbitrary centered Gaussian measure on a real Hilbert space, so the
spin-glass identities are specializations rather than separate developments.

- `ProbabilityTheory.IsGaussian.integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2`
  — **Price's theorem** (second-order Gaussian integration by parts):
  `∫ ⟪x,h⟫⟪x,k⟫ F = ⟪C h, k⟫ ∫ F + ∫ (D²F)(C k)(C h)`, with the centered-`F` corollary
  `..._of_integral_eq_zero`.
- `ProbabilityTheory.IsGaussian.integral_apply_self_eq_sum_integral_fderiv_covarianceOperator`
  — **the Gaussian divergence (Stein) identity** for a `C¹` covector field:
  `∫ (Ψ x) x = ∑ i ∫ ((DΨ x)(C bᵢ)) bᵢ`, i.e. `∫ (Ψ x) x = ∫ tr (C ∘ DΨ)`.
  Vector-field and scalar (`Ψ = DF`) forms: `integral_inner_vectorField_eq_sum_integral_fderiv`,
  `integral_fderiv_apply_self_eq_sum_integral_fderiv2`.
- `ProbabilityTheory.IsGaussian.integral_fderiv_clm_add_apply_clm_eq_sum` — **the two-map
  substitution form**, the most general of the family:
  `∫ (DF (A x + c)) (B x) = ∑ i ∫ ((D²F (A x + c)) (A (C bᵢ))) (B bᵢ)` for *independent*
  continuous linear maps `A B : E →L[ℝ] G`. This is exactly what an interpolation derivative
  consumes: `A` is the interpolation map `x ↦ √t·x₁ + √(1-t)·x₂` and `B` is its time derivative,
  which is a different map. `integral_fderiv_affine_apply_self_eq_sum` (`A = a • id`, `B = id`)
  and `..._comp_clm_apply_self_eq_sum` (`B = A`, trace against the *pushforward* covariance
  `covarianceOperator (μ.map A)`) are its corollaries.
- `ProbabilityTheory.gaussianInterp` / `gaussianInterpDeriv` and
  `ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum` — **the Gaussian
  interpolation trace identity**: for a centered Gaussian `P` on `WithLp 2 (E × E)` with block
  diagonal covariance (e.g. the law of an independent pair of Gaussian vectors),
  `∫ (DF (Z_t p + c)) (Ż_t p) ∂P = (1/2) ∑ i [∫ (D²F) uᵢ bᵢ - ∫ (D²F) vᵢ bᵢ]`
  along Talagrand's smart path `Z_t = √t·x + √(1-t)·y`. Sign information about the right-hand side
  is exactly Slepian's inequality and the Sudakov–Fernique inequality — neither of which exists in
  Mathlib. `..._apply_deriv` is the `HasTemperateGrowth` form, and `hasDerivAt_gaussianInterp`,
  `opNorm_gaussianInterp_le`, `hasFDerivAt_gaussianInterp_add_const` are the accompanying calculus.
- `Function.HasTemperateGrowth.fderiv` — the derivative of a function of temperate growth has
  temperate growth (a gap in Mathlib: the converse of `HasTemperateGrowth.of_fderiv`), with
  `exists_bound_fderiv_two` and `hasTemperateGrowth_affine`. All the formulae above are restated
  under this single Mathlib-native hypothesis in `Gaussian_IBP_Temperate`.
- `FiniteGibbs.std_basis_eq_basisFun`, `FiniteGibbs.integral_fderiv_apply_self_eq_sum_std_basis`,
  `FiniteGibbs.integral_inner_mul_inner_mul_std_basis`,
  `FiniteGibbs.integral_fderiv_comp_clm_apply_self_std_basis` — the same identities read in the
  Dirac basis of `EnergySpace α = EuclideanSpace ℝ α`.
- `FiniteGibbs.norm_fderiv_fderiv_free_energy_density_le` (`‖D²F_n‖ ≤ 2/n`, uniform), hence
  `FiniteGibbs.norm_fderiv_free_energy_density_growth` and
  `..._fderiv_fderiv_free_energy_density_growth`: degree-`0` polynomial growth. With these,
  `FiniteGibbs.integral_fderiv_free_energy_density_clm_add_apply_clm` and
  `..._comp_clm_apply_self` are **the trace identity for the free-energy density with every
  growth hypothesis discharged**, i.e. the general theorem applied to Talagrand's actual
  functional, with nothing left to supply at the call site but the maps.

## Proved: Gaussian comparison — Slepian and Sudakov–Fernique

Neither inequality exists in Mathlib. Both are sign consequences of the interpolation trace
identity, stated for arbitrary centered Gaussian measures on a real Hilbert space.

- `ProbabilityTheory.gaussianInterp` / `gaussianInterpDeriv` — Talagrand's smart path
  `Z_t = √t·x + √(1-t)·y` on `WithLp 2 (E × E)` as continuous linear maps, with
  `hasDerivAt_gaussianInterp`, `opNorm_gaussianInterp_le`, `opNorm_gaussianInterp_le_two`,
  `norm_gaussianInterpDeriv_le_of_mem_Icc` and the endpoint identifications
  `gaussianInterp_one`/`_zero`.
- `ProbabilityTheory.IsGaussian.hasDerivAt_integral_gaussianInterp` — `s ↦ ∫ F (Z s p + c) ∂P` is
  differentiable on `(0,1)` with derivative `∫ (DF (Z t p + c)) (Ż t p) ∂P`. Differentiation under
  the integral sign is dominated on compact subintervals of `(0,1)`, where `‖Ż s‖` is uniformly
  bounded and `‖Z s‖ ≤ 2`, so the integrand's `s`-derivative is dominated by `C' (1 + ‖p‖)^(m+1)`,
  which Fernique's theorem makes integrable. `continuousOn_integral_gaussianInterp` gives
  continuity on the closed interval, so the mean value theorem applies on `[0,1]`.
- `ProbabilityTheory.IsGaussian.integral_le_integral_of_trace_nonneg` / `..._nonpos` and their
  pointwise-hypothesis forms `..._of_fderiv2_trace_nonneg` / `..._nonpos` — **the Gaussian
  comparison theorem**: a sign condition on the trace compares the two endpoint integrals.
- `ProbabilityTheory.IsGaussian.slepian` — **Slepian's inequality**: equal variances and
  `B i j ≤ A i j` off the diagonal, plus nonnegative mixed second derivatives of `F`, give
  `𝔼 F(Y + c) ≤ 𝔼 F(X + c)`. The diagonal terms of `∑_{i,j} (Aᵢⱼ - Bᵢⱼ) ∂²_{ji}F` cancel and each
  off-diagonal term is a product of two nonnegative factors.
- `ProbabilityTheory.sum_mul_hess_eq_half_sum_incr` — the algebraic heart of Sudakov–Fernique: for
  a Hessian of smooth-maximum shape the trace reorganizes so that only the *increments*
  `Δᵢᵢ + Δⱼⱼ - 2Δᵢⱼ` survive.
- `ProbabilityTheory.covarianceOperator_map_toLp_prodMk` — **the covariance operator of the
  `L²`-joint law of an independent centered Gaussian pair is block diagonal**, with the marginal
  covariance operators as blocks. This is what makes the hypotheses of the identities above
  *checkable*: without it the comparison theorems would be conditional on a block structure with no
  instance. `isGaussian_map_toLp_prodMk` and `integral_id_map_toLp_prodMk_eq_zero` supply the other
  two inputs, and `inner_covarianceOperator_map` (`⟪C_X x, y⟫ = 𝔼⟪x,X⟫⟪y,X⟫`) the second-moment
  formula behind them.
- `ProbabilityTheory.IsGaussian.slepian_of_indepFun` and `..._sudakov_fernique_of_indepFun` — the
  two inequalities as **unconditional** statements about independent centered Gaussian vectors on a
  probability space, with hypotheses and conclusions written as ordinary expectations:
  `𝔼(Xᵢ-Xⱼ)² ≤ 𝔼(Yᵢ-Yⱼ)²` gives `𝔼 maxᵢ(Xᵢ+cᵢ) ≤ 𝔼 maxᵢ(Yᵢ+cᵢ)`; `𝔼Xᵢ² = 𝔼Yᵢ²` with
  `𝔼YᵢYⱼ ≤ 𝔼XᵢXⱼ` gives `𝔼F(Y+c) ≤ 𝔼F(X+c)`. Nothing about covariance operators is left to check
  at the point of use.
- `ProbabilityTheory.IsGaussian.sudakov_fernique` — **the Sudakov–Fernique inequality**:
  `𝔼(Xᵢ-Xⱼ)² ≤ 𝔼(Yᵢ-Yⱼ)²` for all `i, j` implies `𝔼 maxᵢ (Xᵢ + cᵢ) ≤ 𝔼 maxᵢ (Yᵢ + cᵢ)`, with no
  hypothesis on the variances. Proved through `integral_smoothMax_le_of_incr_le` at every scale
  `l > 0`; since `maxCoord ≤ smoothMax l ≤ maxCoord + l⁻¹ log (card ι)` *uniformly*, letting
  `l → ∞` needs no limit interchange.

## Proved: log-sum-exp and softmax (a Mathlib gap)

Mathlib has neither log-sum-exp nor softmax. `Common.Mathlib.Analysis.SpecialFunctions.LogSumExp`
supplies them with their full Fréchet calculus, and the finite-volume Gibbs objects of this project
turn out to *be* them (see below), so there is one theory rather than two.

- `Real.expSum`, `Real.logSumExp`, `Real.softmax`, `Real.logSumExpHess`, `Real.maxCoord`,
  `Real.smoothMax`; the supremum of the coordinates is Mathlib's `⨆ i, x i`, not a new definition.
- `Real.contDiff_logSumExp`, `Real.fderiv_logSumExp_apply` (the gradient **is** softmax),
  `Real.fderiv_softmax_apply` (`∂_j pᵢ = pᵢ(δᵢⱼ - pⱼ)`),
  `Real.fderiv_fderiv_logSumExp_apply` (the Hessian **is** the softmax covariance form), and its
  Dirac-basis entries `Real.logSumExpHess_basisFun_self` / `..._of_ne`.
- `Real.norm_fderiv_logSumExp_le` (`≤ 1`) and `Real.norm_fderiv_fderiv_logSumExp_le` (`≤ 2`),
  uniformly in `x`; `Real.le_logSumExp`, `Real.logSumExp_le_of_le`, `Real.abs_logSumExp_le`.
- `Real.contDiff_smoothMax`, `Real.fderiv_smoothMax_apply`,
  `Real.fderiv_fderiv_smoothMax_apply`, `Real.norm_fderiv_smoothMax_le`,
  `Real.norm_fderiv_fderiv_smoothMax_le`, `Real.ciSup_coord_le_smoothMax`,
  `Real.smoothMax_le_ciSup_coord_add`, `Real.abs_smoothMax_le`, together with the `⨆` API
  `Real.le_ciSup_coord`, `Real.ciSup_coord_le`, `Real.abs_ciSup_coord_le`,
  `Real.continuous_ciSup_coord`.
- `fderiv_comp_clm`, `fderiv_fderiv_comp_clm_apply`, `fderiv_fderiv_const_mul_apply` — first- and
  second-order chain rules along a continuous linear map, which is how a change of scale
  `x ↦ l • x` transports the calculus.
- `FiniteGibbs.Z_eq_expSum`, `FiniteGibbs.gibbs_pmf_eq_softmax`,
  `FiniteGibbs.free_energy_density_eq_logSumExp`,
  `FiniteGibbs.hessian_free_energy_eq_logSumExpHess` — **all four hold by `rfl`**: the partition
  function, Gibbs weights, free-energy density and Gibbs covariance of this project are the general
  log-sum-exp objects at the negated Hamiltonian. Accordingly *every* result in `FiniteGibbs` and
  `FiniteGibbs.Calculus` is now **derived** from the general theory rather than reproved: the
  negation is the continuous linear map `FiniteGibbs.negCLM`, and the calculus transports along it
  by `fderiv_comp_clm` and `fderiv_fderiv_comp_clm_apply`. In particular
  `fderiv_free_energy_density_apply` is `Real.fderiv_logSumExp_apply`,
  `hessian_free_energy_fderiv_eq_hessian_free_energy` is `Real.fderiv_fderiv_logSumExp_apply`
  (its two sign changes cancelling), the uniform bounds `‖DF_n‖ ≤ 1/n` and `‖D²F_n‖ ≤ 2/n` are
  `Real.norm_fderiv_logSumExp_le` and `Real.norm_fderiv_fderiv_logSumExp_le` rescaled, and the
  growth bound is `Real.abs_logSumExp_le`. There is one theory, not two.

## The disorder ontology

`GaussianDisorder P K` is **one** structure: a random Hamiltonian whose law under `P` is Gaussian
and centered with covariance kernel `K` in the Dirac basis, with Gaussianity carried by Mathlib's
`ProbabilityTheory.HasGaussianLaw`. It is stated over a bare `MeasurableSpace` and an arbitrary
measure `P` — it is a property of the pair `(P, U)` and nothing in it refers to a canonical
`volume`. (It previously demanded `[MeasureSpace Ω]` and `[IsProbabilityMeasure (ℙ : Measure Ω)]`,
which made it *uninhabitable at its most natural instance*: a disorder on `EnergySpace N` itself,
whose `volume` is Lebesgue measure and hence not a probability measure. The `ℙ`-based probability
layer resumes below the structure.) The SK and reference disorders are abbreviations for it at two
kernels,

`SKDisorder β := GaussianDisorder ℙ (sk_cov_kernel N β)`,
`SimpleDisorder β q := GaussianDisorder ℙ (simple_cov_kernel N β (q * ·))`,

so every lemma about `GaussianDisorder` applies to both by dot notation and the six duplicated
special-case corollaries are gone. `GaussianDisorder` is parameterized by the measure `P` rather
than keyed to `volume`, and the magnetic field `h` — which appeared in `SKDisorder`'s type but in
none of its fields — has been removed; it was being auto-included as an unused hypothesis in about
ninety downstream declarations, and in `disorderPair`/`disorderPairLaw` as an unused argument.

## Proved: realizability of the covariances (Vol. II, Eq. (14.57))

- `Matrix.posSemidef_hadamardPow` — Hadamard powers preserve positive semidefiniteness (iterated
  Schur product theorem).
- `posSemidef_overlapMatrix` — the overlap matrix is positive semidefinite (it is a Gram matrix).
- `posSemidef_overlapPolyMatrix` — **the mixed `p`-spin criterion**: `N · ∑ₚ aₚ Rᵖ` is positive
  semidefinite whenever every `aₚ ≥ 0`, so it is the covariance of a centered Gaussian
  Hamiltonian. `posSemidef_skCovMatrix` and `posSemidef_refCovMatrix` are the instances used in
  Vol. I, §1.3.
- `inner_covarianceOperator_multivariateGaussian_std_basis` — the covariance operator of a
  centered `multivariateGaussian` reads off its matrix in the Dirac basis.
- `exists_skDisorder_simpleDisorder_indepFun` — the SK / replica-symmetric disorder pair exists.

## Proved: the cavity identity (Vol. I, §1.7; Vol. II, §12.2)

- `FiniteGibbs.contDiff_gibbs_average_n_det`, `FiniteGibbs.fderiv_gibbs_average_n_det_apply_eq` —
  the `n`-replica Gibbs average is smooth in the Hamiltonian, with derivative
  `n ⟨f⟩ ⟨v⟩ - ∑_l ⟨f v(σˡ)⟩`.
- `FiniteGibbs.integral_gibbs_average_n_det_energy_mul` — **the cavity identity with the energy
  inside the bracket**: `𝔼⟨H_{σⁱ} f⟩ = 𝔼[ m ⟨f · ⟨C e_{σⁱ}⟩⟩ - ∑_{l<m} ⟨f · (C e_{σⁱ})(σˡ)⟩ ]`,
  where the inner average is over a *fresh* replica. This is the form the cavity method uses: the
  Hamiltonian evaluated at a replica is traded for covariances between that replica and the
  others, plus one fresh replica. Obtained from the identity below by expanding over the value of
  the `i`-th replica and collapsing the indicators.
- `FiniteGibbs.integral_inner_mul_gibbs_average_n_det` — **the cavity identity**, in an arbitrary
  direction: `𝔼[⟪H, w⟫ ⟨f⟩] = 𝔼[ n ⟨f⟩ ⟨C w⟩ - ∑_{l<n} ⟨f · (C w)(σˡ)⟩ ]`, obtained by Gaussian
  integration by parts applied to the Gibbs average as a functional of the Hamiltonian. It is
  **exact at every finite volume**, for an arbitrary finite configuration space and an arbitrary
  centered Gaussian Hamiltonian law — unlike the Ghirlanda–Guerra identities, which are its
  asymptotic shadow after the Hamiltonian is replaced by its mean.
  `FiniteGibbs.integral_apply_mul_gibbs_average_n_det` is the coordinate case `w = e_ρ`.
- `FiniteGibbs.integral_gibbs_average_n_det_inner_mul` — the same with an arbitrary *field*
  `σ ↦ ⟪H, w σ⟫` inside the bracket. The generality in `w` is what puts a **component** of the
  disorder on the same footing as the energy: the `p`-spin part of a mixed Hamiltonian is a linear
  image `W H` of it (and a component that is not a function of `H` may be replaced by its
  conditional expectation given `H`, which is), so `(W H) σ = ⟪H, Wᵀ e_σ⟫`. This is the
  prerequisite for the Ghirlanda–Guerra identities at *individual* monomial test functions.

## Proved: the Ghirlanda–Guerra defect (Vol. II, §12.2)

- `FiniteGibbs.integral_gibbs_average_n_det_energy_mul_erase` — the cavity identity with the
  diagonal term `l = i` separated; the constant-diagonal hypothesis `c σ σ = d` enters here and
  nowhere else. It holds for every mixed `p`-spin covariance `c σ τ = N ξ(R_{στ})`, where
  `c σ σ = N ξ(1)`.
- `FiniteGibbs.integral_gibbs_average_one_energy` — the mean energy is the mean two-replica
  covariance minus the diagonal: `𝔼⟨H⟩ = 𝔼⟨c(σ¹,σ²)⟩ - d`.
- `FiniteGibbs.ghirlandaGuerra_defect` — **the Ghirlanda–Guerra defect is the energy–observable
  covariance**: the failure of the Ghirlanda–Guerra identity for a test function `f` of `m`
  replicas equals exactly `𝔼⟨H_{σⁱ} f⟩ - 𝔼⟨f⟩ · 𝔼⟨H⟩`. So the identity holds *exactly* iff the
  energy decorrelates from the observable, and any bound on that covariance — for instance from
  the Gaussian covariance inequality below — is a bound on the Ghirlanda–Guerra error. This is the
  exact finite-volume replacement for the Ghirlanda–Guerra identities, which are false at finite
  volume.
- Supporting: `FiniteGibbs.freshCov` (the Gibbs average of the covariance against a fresh
  replica), `norm_std_basis`, `gibbs_average_one`, `integrable_gibbs_average_n_det_of_bounded`.

## Proved: Ghirlanda–Guerra with an explicit error term (Vol. II, §12.2)

The defect identity says *what* the error is; these results *bound* it, and then compute the bound
exactly. Nothing here is asymptotic — every statement holds at every finite volume.

- `FiniteGibbs.gibbs_average_n_det_eval` — every coordinate of the `m`-replica product Gibbs
  measure has the Gibbs measure as its marginal, `⟨u(σⁱ)⟩ = ⟨u⟩`.
- `FiniteGibbs.sq_sum_gibbs_pmf_mul_abs_le` — Cauchy–Schwarz for the Gibbs bracket,
  `⟨|u|⟩² ≤ ⟨u²⟩`.
- `FiniteGibbs.abs_integral_gibbs_average_energy_mul_sub_le` — **the error bound**:
  `|𝔼⟨H_{σⁱ} f⟩ - a 𝔼⟨f⟩| ≤ ‖f‖_∞ √(𝔼⟨(H - a)²⟩)`, for an arbitrary constant `a`. Neither
  Gaussianity nor centring is used: it is the two Cauchy–Schwarz steps above plus `(𝔼X)² ≤ 𝔼X²`.
- `FiniteGibbs.ghirlandaGuerra_error_le` — **Ghirlanda–Guerra with an explicit error term**,
  the defect identity composed with the bound at `a = 𝔼⟨H⟩`.
- `FiniteGibbs.integral_energy_sq_weight`, `FiniteGibbs.integral_gibbs_average_energy_sq` — one
  Gaussian integration by parts on the *energy-weighted* Gibbs weight `H ↦ H_ρ p_ρ(H)` gives
  `𝔼⟨H²⟩ = d + 𝔼⟨H(σ¹) c(σ¹,σ²)⟩ - d 𝔼⟨H⟩`: differentiating the explicit factor `H_ρ` produces
  the diagonal, differentiating the weight produces the fresh-replica covariance.
- `FiniteGibbs.integral_gibbs_average_sub_mean_sq` — **the energy fluctuation, exactly**:
  `𝔼⟨(H - 𝔼⟨H⟩)²⟩ = d + 𝔼⟨H(σ¹) c(σ¹,σ²)⟩ - d 𝔼⟨H⟩ - (𝔼⟨H⟩)²`.
- `FiniteGibbs.integral_gibbs_average_sub_mean_sq_eq_covariance` — **the fluctuation as a pure
  covariance bracket**: applying the cavity identity once more, at two replicas and to the
  covariance kernel itself, removes the last Hamiltonian, leaving
  `𝔼⟨(H - 𝔼⟨H⟩)²⟩ = d + 2 𝔼⟨c₁₂ c₁₃⟩ - 𝔼⟨c₁₂²⟩ - (𝔼⟨c₁₂⟩)²`. Centred, the right-hand side is
  `d + 2 𝔼⟨(c₁₂ - A)(c₁₃ - A)⟩ - 𝔼⟨(c₁₂ - A)²⟩`.
- `FiniteGibbs.ghirlandaGuerra_error_le_energy_fluctuation` and
  `FiniteGibbs.ghirlandaGuerra_error_le_covariance` — the bound composed with each form of the
  fluctuation. In the second, neither the Hamiltonian nor the observable appears on the right: the
  Ghirlanda–Guerra error is bounded by an expression in the covariance kernel alone.
- `FiniteGibbs.gibbs_average_two` — the two-replica bracket as an explicit double sum.

## Proved: the replica measure is a Mathlib product measure

- `FiniteGibbs.replicaGibbsMeasure` **is** `MeasureTheory.Measure.pi (fun _ : Fin n => gibbsMeasure
  H)`, by definition rather than by a bespoke atomic construction. Normalisation
  (`IsProbabilityMeasure`) is then the Mathlib instance, and the whole `Measure.pi` API applies to
  the replica bracket.
- `FiniteGibbs.measurePreserving_comp_perm_replicaGibbsMeasure` and
  `FiniteGibbs.gibbs_average_n_det_comp_perm` — **the replicas are exchangeable**: relabelling them
  by a permutation preserves the replica measure, hence the bracket. This is
  `MeasureTheory.measurePreserving_piCongrLeft`, and it is the hypothesis of de Finetti's theorem
  and of the Aldous–Hoover representation that Vol. II Ch. 12–15 needs.
- `FiniteGibbs.replicaGibbsMeasure_apply_singleton` — the atoms are the products of the Gibbs
  weights, from `Measure.pi_pi`.

## Dependencies

`matteo-ax/GibbsMeasure` (rev `8a158f0`) is pinned for **one** layer: exchangeability, the
Hewitt–Savage zero-one law, and `existsUnique_mixing_of_isExchangeable` (de Finetti in Dynkin's
form, with uniqueness over a standard Borel space). Mathlib has none of these, and they are the
ancestors of Aldous–Hoover and Dovbysh–Sudakov, which Vol. II Ch. 12–15 needs. It is imported
through `SpinGlass/Limit/Exchangeability.lean` and used in `SpinGlass/Limit/AsymptoticGibbs.lean`.
The DLR/specification half of that repository is not imported.

## Proved: the asymptotic Gibbs measure (Vol. II, Ch. 12; Panchenko)

The limit layer that Vol. II starts from. The finite-volume replicas are i.i.d., hence
exchangeable; the state spaces are unified by embedding `Config N` into the compact metrizable
spin space `ℕ → Bool`; Prokhorov gives limit points; exchangeability survives the limit; de Finetti
represents the limit as a mixture of i.i.d. product measures. The mixing measure is Talagrand's and
Panchenko's *asymptotic Gibbs measure*.

- `MeasureTheory.ProbabilityMeasure.isClosed_setOf_map_eq` — **invariance under a continuous map is
  a closed condition** in the topology of convergence in distribution: the invariance locus is the
  equaliser of `ProbabilityMeasure.continuous_map` and the identity, and the space of probability
  measures is Hausdorff. `map_eq_of_tendsto` and
  `Measure.map_eq_of_tendsto_probabilityMeasure` are the limit forms. Absent from Mathlib; it is
  the mechanism behind Krylov–Bogolyubov and behind every infinite-volume limit construction.
- `MeasureTheory.GibbsMeasure.continuous_permute`,
  `MeasureTheory.GibbsMeasure.isExchangeable_of_tendsto` — hence **exchangeability passes to weak
  limits**, which is the step that makes de Finetti applicable to a *limit* law rather than to a
  fixed one, and `existsUnique_mixing_of_tendsto` is that composition.
- `MeasureTheory.GibbsMeasure.exists_subseq_tendsto_mixing` — on a compact standard Borel state
  space, **every** sequence of exchangeable laws has a subsequence converging to a unique de
  Finetti mixture. No hypothesis on the sequence.
- `MeasureTheory.Measure.map_comp_infinitePi_const` — the finite-dimensional marginals of an
  i.i.d. infinite product along an arbitrary *injective reindexing* (Mathlib has only the canonical
  `Finset.restrict` marginal, `Measure.infinitePi_map_restrict`).
- `SpinGlass.spinLaw`, `SpinGlass.replicaArrayLaw`, `SpinGlass.replicaArray`,
  `SpinGlass.isExchangeable_replicaArrayLaw` — the one-replica and replica-array laws of a
  finite-volume Gibbs measure, read on the spin space along an arbitrary embedding, and their
  exchangeability.
- `SpinGlass.map_take_replicaArrayLaw` — **the bridge**: the first `n` replicas of the replica array
  are exactly `FiniteGibbs.replicaGibbsMeasure n H` transported along the embedding, so the finite
  replica calculus (`gibbs_average_n_det`, the Ghirlanda–Guerra brackets) is the
  finite-dimensional shadow of the asymptotic object.
- `SpinGlass.exists_asymptoticGibbsMeasure` — **the asymptotic Gibbs measure exists**: for an
  arbitrary sequence of Hamiltonians and an arbitrary family of embeddings, some subsequence of the
  replica-array laws converges, and the limit is `∫ λ^{⊗ℕ} m(dλ)` for a *unique* probability
  measure `m` on the probability measures of the spin space. Unconditional.
- `MeasureTheory.GibbsMeasure.isExchangeable_bind` — a **mixture** of exchangeable laws is
  exchangeable (`Measure.map_bind`: pushing a mixture forward is the mixture of the pushforwards).
- `FiniteGibbs.continuous_gibbs_pmf`, `FiniteGibbs.measurable_gibbsMeasure` — **the Gibbs measure
  depends measurably on the Hamiltonian**, which is what lets a random Hamiltonian be integrated
  out.
- `SpinGlass.annealedReplicaArrayLaw`, `SpinGlass.isExchangeable_annealedReplicaArrayLaw`,
  `SpinGlass.exists_asymptoticGibbsMeasure_random` — the same for a **random** Hamiltonian: the
  disorder-averaged replica array is a mixture of exchangeable laws, hence exchangeable, and de
  Finetti's mixing measure of its limit is the **law of the random asymptotic Gibbs measure**. This
  is Panchenko's object; the statement is unconditional in the sequence of random Hamiltonians.

## Proved: the asymptotic overlap array (Vol. II, Ch. 12–15; the Dovbysh–Sudakov hypothesis)

De Finetti is about exchangeable *sequences*; Vol. II is about exchangeable **arrays** — the
overlap array `R_{l,l'}`, invariant under the *diagonal* action of a permutation of the replica
index. Its law lives on `[-1,1]^{ℕ×ℕ}`, compact metrizable **independently of `N`**, which is why
the thermodynamic limit is taken there and not on the configuration space.

- `MeasureTheory.GibbsMeasure.permuteArray`, `MeasureTheory.GibbsMeasure.IsJointlyExchangeable` —
  the diagonal action and joint (weak) exchangeability; `measurable_permuteArray`,
  `continuous_permuteArray`.
- `MeasureTheory.GibbsMeasure.pairArray`,
  `MeasureTheory.GibbsMeasure.isJointlyExchangeable_map_of_isExchangeable` — **the array of
  pairwise values of an exchangeable sequence is jointly exchangeable**, for an arbitrary
  two-variable measurable function. This is how the overlap array acquires the hypothesis of
  Aldous–Hoover and Dovbysh–Sudakov, and it is the bridge from de Finetti-style exchangeability to
  array exchangeability. Absent from Mathlib and from the `GibbsMeasure` package.
- `MeasureTheory.GibbsMeasure.isJointlyExchangeable_bind`,
  `..._of_tendsto`, `exists_subseq_tendsto_jointlyExchangeable` — mixtures, weak limits, and
  Prokhorov limit points, exactly as for sequences.
- `MeasureTheory.ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed` — **a closed
  almost-sure property survives a weak limit** (portmanteau at mass one). With
  `isClosed_setOf_map_eq` this is the pair of general facts that let a limit law inherit both the
  symmetries and the pointwise constraints of the approximating laws.
- `SpinGlass.abs_overlap_le_one`, `SpinGlass.overlapUnit` — the overlap valued in `[-1,1]`;
  `SpinGlass.configReplicaArrayLaw`, `SpinGlass.overlapArrayLaw`, `SpinGlass.overlapArray` and
  `SpinGlass.isJointlyExchangeable_overlapArrayLaw`.
- `SpinGlass.gramArray`, `SpinGlass.isClosed_gramArray`,
  `SpinGlass.pairArray_overlapUnit_mem_gramArray` — the **Gram condition** (symmetric, unit
  diagonal, positive semidefinite) is closed, and every finite-`N` overlap array satisfies it: the
  positive semidefiniteness is the identity
  `∑_{l,l'} c_l c_{l'} R(σ^l,σ^{l'}) = (1/N) ∑_i (∑_l c_l σ^l_i)²`.
- `SpinGlass.exists_asymptoticOverlapArray` and
  `SpinGlass.exists_asymptoticOverlapArray_random` — **the asymptotic overlap array exists**, is
  jointly exchangeable, and is almost surely a Gram array, for an arbitrary sequence of (random)
  Hamiltonians on arbitrary positive system sizes. Unconditional. This is precisely the hypothesis
  of the Dovbysh–Sudakov theorem.

## Proved: the §15.3 ontology and its stability (Vol. II, Definitions 15.3.1–15.3.4)

Talagrand Vol. II, §15.3 fixes the three properties expected of the limiting law `μ*` of the
overlap array. `IsJointlyExchangeable` is his Definition 15.3.1 (*symmetric*, i.e. weakly
exchangeable) and `gramArray` is his `𝓒⁺`; that `μ*(𝓒⁺) = 1`, which he asserts, is
`exists_asymptoticOverlapArray`. The remaining two definitions and everything structural about them
are here. Talagrand's Definition 15.3.4 is stated with *continuous* test functions, which is what is
formalised; Panchenko writes the same identities with bounded measurable ones.

- `SpinGlass.IsUltrametric` (Definition 15.3.2, form (15.38); Panchenko (1.3)) and
  `SpinGlass.isUltrametric_iff_forall` — **the equivalence with form (15.39)**, which Talagrand
  states without proof: the complement of the ultrametric set is the countable union over the
  rationals of the sets of (15.39).
- `SpinGlass.isClosed_ultrametricSet`, `SpinGlass.isUltrametric_of_tendsto` — ultrametricity is a
  closed condition, hence passes to weak limits.
- `SpinGlass.SatisfiesGhirlandaGuerra` (Definition 15.3.4, equation (15.40); Panchenko (1.1)),
  with `SpinGlass.DependsOnFirst` for Talagrand's restriction on the test function.
- `SpinGlass.satisfiesGhirlandaGuerra_of_tendsto` — **the Ghirlanda–Guerra identities pass to weak
  limits**: every term of (15.40) is the integral of a fixed continuous function, hence a
  continuous function of the measure, so the identity is a closed condition.
- `SpinGlass.satisfiesGhirlandaGuerra_map` — **Exercise 15.3.5**: the identities survive an
  entrywise continuous change of variable.
- `SpinGlass.oneOverlapLaw`, `SpinGlass.map_entry_eq_oneOverlapLaw` — **all pairwise overlaps of a
  weakly exchangeable array are equidistributed**, so "the limiting law of the overlap" of (15.41)
  is well defined. The permutation carrying `(0,1)` to `(l,l')` is built from two transpositions.
- `SpinGlass.tendsto_asymptoticArrayLaw` — the four properties (weak exchangeability, the Gram
  condition, ultrametricity, Ghirlanda–Guerra) **all pass to weak limits simultaneously**, so each
  may be verified along any approximating sequence.

- `SpinGlass.blockRestrict`, `SpinGlass.blockExtend`, `SpinGlass.dependsOnFirst_iff_exists` —
  **Talagrand's restriction on the test function is factorisation through the `n × n` overlap
  block**. Every continuous function of the finite overlap matrix is admissible
  (`dependsOnFirst_comp_blockRestrict`), and the admissible functions form an algebra
  (`dependsOnFirst_const`, `dependsOnFirst_entry`, `DependsOnFirst.add`, `.mul`, `.smul`, `.mono`).
  Without this the side condition would have no verified instances.
- `SpinGlass.satisfiesGhirlandaGuerra_of_denseSpan` — **the identities need only be checked on a
  set whose *span* is dense**. For fixed `n` and `f` the identity is a *linear* condition on `φ`
  (`integral_comp_mul_add`, `integral_comp_mul_smul`) and a closed one (each term is bounded by
  `‖φ‖‖f‖`, `lipschitzWith_integral_comp_mul`), so it propagates from `S` to `Submodule.span ℝ S`
  and then to its closure. The span, not the set, is what may be assumed dense —
  `satisfiesGhirlandaGuerra_of_dense` is the corollary at `S` itself dense.
- `SpinGlass.satisfiesGhirlandaGuerra_of_monomial` — hence **monomial test functions suffice**. The
  monomials `x ↦ xᵖ` are *not* dense in `C([-1,1], ℝ)`, so the dense-set form would not apply; they
  do span a dense subspace (`polynomialFunctions_subset_span_monomials` with Stone–Weierstrass,
  `dense_polynomialFunctions`). This is the sharpest usable form and the one a family of models
  delivers: a mixed `p`-spin Hamiltonian has covariance profile `ξ(r) = ∑ₚ βₚ² rᵖ`, and
  differentiating in the couplings isolates the individual monomials.
  `satisfiesGhirlandaGuerra_of_polynomial` is the intermediate form.
- `SpinGlass.SatisfiesGhirlandaGuerra'` and
  `SpinGlass.satisfiesGhirlandaGuerra_iff_of_isJointlyExchangeable` — **Talagrand's (15.40) and
  Panchenko's (1.1) are the same condition for a weakly exchangeable law**: the two differ only in
  whether the isolated factor is `𝔼ψ(R_{1,n+1})` or `𝔼ψ(R_{1,2})`, and those agree by
  `map_entry_eq_oneOverlapLaw`.
- `SpinGlass.isUltrametric_bind` — ultrametricity, being almost sure, survives mixtures.
- `SpinGlass.constArray`, `SpinGlass.rsArrayLaw` and
  `isJointlyExchangeable_rsArrayLaw`, `constArray_mem_gramArray`, `gramArray_rsArrayLaw`,
  `isUltrametric_rsArrayLaw`, `satisfiesGhirlandaGuerra_rsArrayLaw`, `oneOverlapLaw_rsArrayLaw` —
  **the ontology is non-vacuous**: for `q ∈ [0,1]` the array with all off-diagonal entries `q`
  satisfies *every* §15.3 property at once, with one-overlap law `δ_q`. It is the
  replica-symmetric `μ*` of Talagrand's Theorem 15.3.6 at `μ = δ_q`, and it shows that the four
  conditions are jointly satisfiable — a definition with no instance would be worthless.

In this ontology, Talagrand's Research Problem 15.3.7 — do the Ghirlanda–Guerra identities on `𝓒⁺`
imply ultrametricity? — reads `SatisfiesGhirlandaGuerra μ → μ gramArray = 1 → IsUltrametric μ`. It
was answered affirmatively by Panchenko (*The Parisi ultrametricity conjecture*, Ann. of Math. 177
(2013), Theorem 1) and is the next capstone.

## Proved: the Ghirlanda–Guerra identities as a disintegration (Vol. II, (15.40); Panchenko (1.2))

Talagrand and Panchenko both *state* the identities as integral identities against test functions,
and that is the form in which they are verified. It is not the form in which they are used: every
downstream argument reads them as a statement about the **conditional law of the new overlap given
the overlaps of the first `n` replicas**. That implication is proved here, and with it the
identities extend from continuous, block-only test functions to arbitrary bounded measurable ones
that may also depend on the new overlap.

- `SpinGlass.ggKernel` — the Ghirlanda–Guerra kernel `x ↦ (1/n) ν + (1/n) ∑_{l=1}^{n-1} δ_{x₀ₗ}`,
  a genuine Markov kernel on the space of `n × n` overlap blocks
  (`SpinGlass.isMarkovKernel_ggKernel`); `SpinGlass.integral_ggKernel_of_bounded` computes
  integrals against it.
- `SpinGlass.map_prod_blockRestrict_eq_compProd` — **the disintegration**: the joint law of
  `(Rⁿ, R_{0,n})` is `(law of Rⁿ) ⊗ₘ ggKernel n ν`. The proof is a measure-identification, not an
  approximation: both sides integrate products of bounded continuous functions equally, and a
  finite Borel measure on a product of `HasOuterApproxClosed` spaces is determined by those
  integrals (`MeasureTheory.Measure.ext_of_integral_mul_boundedContinuousFunction`).
- `SpinGlass.condDistrib_entry_eq_ggKernel` — Panchenko's (1.2): the regular conditional
  distribution `condDistrib (R_{0,n}) (Rⁿ)` **is** the Ghirlanda–Guerra kernel.
- `SpinGlass.integral_ghirlandaGuerra` — **the identities for bounded measurable test functions**,
  with the test function allowed to depend jointly on the block and on the new overlap. This is
  strictly stronger than the hypothesis it is derived from.
- `SpinGlass.SatisfiesGhirlandaGuerra'.map_prod_blockRestrict_eq_compProd` and
  `SpinGlass.SatisfiesGhirlandaGuerra.map_prod_blockRestrict_eq_compProd` — the two stated forms
  both disintegrate, the second for a weakly exchangeable law, with `ν = oneOverlapLaw μ`.
- Supporting Mathlib gap: `ProbabilityTheory.Kernel.instModule` — **kernels form a module over the
  scalars that act on measures**. Mathlib gives `Kernel` only the `ℕ`-action from its additive
  monoid structure, so no explicit mixture kernel could be written down.

## Proved: Griffiths' lemma (Vol. I, §1.3, after Theorem 1.3.9; Vol. II, Lemma 12.1.5)

Convexity is what converts the existence of the thermodynamic limit into convergence of its
*derivatives*. Mathlib has the complete one-sided derivative calculus for convex functions but not
this consequence, and it has no convexity statement for log-sum-exp at all.

- `Real.log_sum_exp_le`, `convexOn_log_sum_exp` — **log-sum-exp is convex** (a Mathlib gap). The
  proof is the classical one: after normalising, the inequality is weighted AM–GM applied
  coordinatewise, i.e. Hölder.
- `SpinGlass.FiniteGibbs.convexOn_log_Z`, `convexOn_free_energy_density`,
  `convexOn_free_energy_density_comp_affine` — **the free energy is convex in the Hamiltonian**
  (Talagrand Vol. I (1.81), Vol. II (12.8)), hence in every parameter entering it affinely.
- `ConvexOn.rightDeriv_le_slope_add`, `ConvexOn.sub_le_rightDeriv` — **the two-scale sandwich**: the
  right derivative of a convex `θ` at `x` lies between the difference quotients of an *arbitrary*
  comparison function `p`, up to `‖θ - p‖/b` at the three points `x - b, x, x + b`.
- `ConvexOn.abs_rightDeriv_sub_le` — **Talagrand Vol. II, Lemma 12.1.5**, in one-sided form: no
  differentiability is assumed anywhere.
- `ConvexOn.tendsto_rightDeriv_of_tendsto`, `ConvexOn.tendsto_deriv_of_tendsto` — **Griffiths'
  lemma**. Weaker hypotheses than the reference: the approximating functions need not be
  differentiable, and the limit need only have equal one-sided derivatives at the point.
- `ConvexOn.countable_setOf_leftDeriv_ne_rightDeriv` — **a convex function on `ℝ` is differentiable
  off a countable set**: the jump intervals `(leftDeriv p x, rightDeriv p x)` at distinct points are
  pairwise disjoint. This discharges the hypothesis of Griffiths' lemma for all but countably many
  points, which is how Talagrand uses it. `ConvexOn.hasDerivAt_of_leftDeriv_eq_rightDeriv` and
  `ConvexOn.countable_setOf_not_differentiableAt` are the same statements for the two-sided
  derivative.
- `ConvexOn.integral_abs_rightDeriv_sub_le` — **Griffiths' lemma in mean**, Talagrand Vol. II,
  Lemmas 12.1.5–12.1.6 combined: for a *random* convex `θ` with mean `p`,
  `𝔼|θ'(x) - p'(x)| ≤ (p'(x+b) - p'(x-b)) + (1/b)·(the three mean fluctuations of θ)`. This is the
  step that converts concentration of the free energy into self-averaging of the energy.

## Proved: the free energy along an affine path in the Hamiltonian

Talagrand Vol. I (1.83); Vol. II (12.6)–(12.9).

Every parameter of a mean-field model enters the Hamiltonian affinely, so every parameter
derivative of the free energy is a derivative along `x ↦ H + x • V`. These identities are ordinary
calculus for log-sum-exp: no probabilistic hypothesis, no Gaussianity, exact at every finite volume
and for an arbitrary finite configuration space.

- `SpinGlass.FiniteGibbs.gibbs_average` — the Gibbs bracket `⟨f⟩_H`, at last stated for an
  arbitrary finite configuration space; `SpinGlass.gibbs_average` is its `Config N` instance.
- `SpinGlass.FiniteGibbs.hasDerivAt_free_energy_density_add_smul` — `n Φ'(x) = -⟨V⟩`, Talagrand
  Vol. I (1.83), Vol. II (12.6).
- `SpinGlass.FiniteGibbs.hasDerivAt_gibbsAverage_add_smul` and
  `SpinGlass.FiniteGibbs.hessian_free_energy_self_eq_variance` — `n Φ''(x) = ⟨(V - ⟨V⟩)²⟩`,
  Talagrand Vol. II (12.8): **the second derivative of the free energy in any parameter is the
  Gibbs fluctuation of the conjugate energy**. Hence
  `hessian_free_energy_self_nonneg`, convexity with a quantitative witness.
- `SpinGlass.FiniteGibbs.hasDerivAt_integral_free_energy_density`,
  `SpinGlass.FiniteGibbs.hasDerivAt_integral_gibbsAvg` — the same two identities after averaging
  over the disorder, by differentiation under the integral sign. The domination is uniform in the
  parameter (`|Φ'| ≤ ‖V‖/n`, `|Φ''| ≤ 2‖V‖²/n`), so the derivative exists at *every* parameter
  value, not merely locally.
- `SpinGlass.FiniteGibbs.integral_fluctuation_eq_sub` and
  `SpinGlass.FiniteGibbs.integral_variance_eq_sub` — **Talagrand Vol. II, equation (12.9)**:
  `∫_a^b 𝔼⟨(V - ⟨V⟩)²⟩/n dx = p'(b) - p'(a)`. The integrand is nonnegative, so the *total* energy
  fluctuation over a parameter window is bounded by an increment of `p'`: this is the mechanism by
  which the energy self-averages, and, through `ghirlandaGuerra_error_le`, the mechanism by which
  the Ghirlanda–Guerra identities become exact in the limit.

## Proved: Griffiths' lemma for the SK free energy (Vol. I, §1.3)

- `ProbabilityTheory.multivariateGaussian_map_smul` (a Mathlib gap) and
  `Matrix.PosSemidef.smul_sq` — a multivariate Gaussian scales: dilating by `c` scales the mean by
  `c` and the covariance matrix by `c²`.
- `SpinGlass.skCovMatrix_eq_smul`, `SpinGlass.skFreeEnergy_eq_integral_smul` — since the SK
  covariance is `N β² R²/2`, the disorder at inverse temperature `β` is `β` times **one**
  `β`-independent Gaussian field (Talagrand Vol. I, (1.82)).
- `SpinGlass.convexOn_skFreeEnergy`, `SpinGlass.convexOn_skFreeEnergyLimit` — the free energy and
  its thermodynamic limit are convex in `β` (Talagrand Vol. I, (1.81)).
- `SpinGlass.tendsto_rightDeriv_skFreeEnergy` — **Griffiths' lemma for the SK model**: at every `β`
  where the limiting free energy is differentiable, `∂p_N/∂β → ∂p/∂β`.
  `SpinGlass.countable_setOf_not_tendsto_rightDeriv_skFreeEnergy` and
  `SpinGlass.ae_tendsto_rightDeriv_skFreeEnergy` — this holds at all but countably many `β`, hence
  at almost every `β`. Combined with Talagrand's Lemma 1.3.11,
  `∂p_N/∂β = (β/2)(1 - 𝔼⟨R₁₂²⟩)`, it is the statement that `lim_N 𝔼⟨R₁₂²⟩` exists.
- `SpinGlass.hasDerivAt_skFreeEnergy` — the SK free energy is differentiable in `β` at every point,
  with `∂p_N/∂β = -𝔼⟨H⟩/N`; hence `SpinGlass.tendsto_deriv_skFreeEnergy`,
  `SpinGlass.countable_setOf_not_differentiableAt_skFreeEnergyLimit` and
  `SpinGlass.ae_tendsto_deriv_skFreeEnergy` state Griffiths' lemma for the honest two-sided
  derivative.
- `SpinGlass.integral_skFluctuation_eq_sub` — **equation (12.9) for the SK model**: the Gibbs
  fluctuation of the energy, integrated over the inverse temperature, is the increment of
  `∂p_N/∂β`.

## Proved: the derivative of the free energy is the covariance gap

Talagrand Vol. I, Lemma 1.3.11; Vol. II, Lemma 12.1.4.

The parameter calculus above computes `∂p_n/∂β = -𝔼⟨H⟩/n` — a statement about the Hamiltonian. One
Gaussian integration by parts removes the Hamiltonian and leaves the overlap.

- `SpinGlass.FiniteGibbs.covarianceGap` and
  `SpinGlass.FiniteGibbs.hessian_free_energy_covarianceOperator_std_basis` — contracting the Gibbs
  covariance form with `(C e_σ, e_σ)` gives `(p_σ c(σ,σ) - p_σ ⟨c(σ,·)⟩)/n`, so the trace of the
  Hessian against the covariance is the gap between the diagonal bracket and the two-replica
  bracket.
- `SpinGlass.FiniteGibbs.integral_gibbs_average_self_eq_covariance_gap` — **the general identity**:
  for a centered Gaussian disorder with covariance kernel `c` and an arbitrary deterministic field,
  `∂/∂β 𝔼F_n(βH + c₀) = (β/n) 𝔼(⟨c(σ,σ)⟩ - ⟨c(σ¹,σ²)⟩)`. The proof is the two-map trace identity
  `integral_fderiv_free_energy_density_clm_add_apply_clm` at `A = β·id`, `B = id`.
  `integral_gibbs_average_self_eq_of_diag` is its constant-diagonal form, which is the case of
  every mixed `p`-spin model.
- `SpinGlass.deriv_skFreeEnergy_eq` — **Talagrand's Lemma 1.3.11**, `∂p_N/∂β = (β/2)(1 - 𝔼⟨R₁₂²⟩)`.
  Combined with `ae_tendsto_deriv_skFreeEnergy` this is exactly the statement Talagrand records
  after Theorem 1.3.9: **`lim_N 𝔼⟨R₁₂²⟩` exists at almost every inverse temperature.**
- `SpinGlass.deriv_skFreeEnergy_nonneg_le` — **Talagrand's Lemma 12.1.4**, `0 ≤ ∂p_N/∂β ≤ β/2`,
  uniformly in the volume: the bound that makes `(12.9)` say the energy self-averages.
- Supporting general lemmas: `SpinGlass.abs_overlap_le_one`, `abs_overlap_sq_le_one`,
  `gibbs_average₂_le_of_le`, `abs_gibbs_average₂_le`, `sum_gibbs_pmf_mul_sum_gibbs_pmf` — the
  two-replica bracket is a probability average, so it inherits any bound on its integrand.

## Proved: self-averaging of the energy (Vol. II, Theorem 12.1.1 / equation (12.10))

Equation `(12.9)` controls the fluctuation in `L²`; what the Ghirlanda–Guerra error bound consumes
is the `L¹` fluctuation. Three Cauchy–Schwarz steps bridge them.

- `MeasureTheory.sq_integral_le_measureReal_univ_mul_integral_sq` (a Mathlib gap) — **Cauchy–Schwarz
  against the constant function**, `(∫ f dμ)² ≤ μ(univ) ∫ f² dμ`, for any finite measure. Mathlib
  has Hölder for `lintegral` and Cauchy–Schwarz inside `L²`, but not this. Proof: the discriminant
  of `t ↦ ∫ (f - t)² dμ`. The square-root forms and the interval forms
  (`intervalIntegral.sq_integral_le_mul_integral_sq`,
  `intervalIntegral.integral_le_sqrt_mul_integral_sq`) are corollaries; the interval form is
  `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`.
- `SpinGlass.FiniteGibbs.sq_gibbs_average_abs_sub_le` — Cauchy–Schwarz inside the Gibbs bracket:
  `(⟨|V - ⟨V⟩|⟩/n)² ≤ (1/n)·Φ''`.
- `SpinGlass.FiniteGibbs.integral_absFluct_le_sqrt` — Cauchy–Schwarz against the disorder.
- `SpinGlass.FiniteGibbs.intervalIntegral_absFluct_le` — **equation (12.10)**:
  `∫_a^b 𝔼⟨|V/n - ⟨V/n⟩|⟩ dx ≤ √((b-a)(p'(b) - p'(a))/n)`.
- `SpinGlass.intervalIntegral_skEnergy_fluctuation_le` — **Theorem 12.1.1 for the SK model**:
  `∫_a^b 𝔼⟨|H/N - ⟨H/N⟩|⟩ dβ ≤ √((b-a)·b/(2N))`. The uniform bound `0 ≤ ∂p_N/∂β ≤ β/2` is what
  makes the right-hand side vanish; the rate is `N^{-1/2}`, sharper than the `N^{-1/4}` of
  Talagrand's Theorem 12.1.1 (whose rate is limited by its other half, the disorder fluctuation of
  `⟨H⟩`, controlled by `ConvexOn.integral_abs_rightDeriv_sub_le` together with Gaussian
  concentration).
- Supporting: `SpinGlass.FiniteGibbs.gibbs_average_abs_le`,
  `gibbs_average_abs_sub_gibbs_average_le`, `gibbs_average_abs_smul_sub_const_le_norm` — the Gibbs
  mean absolute deviation of a direction is at most twice its norm.

## Proved: Theorem 12.1.1 — the energy self-averages (Vol. II, §12.1)

The other half of Theorem 12.1.1 controls the fluctuation of `⟨V/n⟩` under the **disorder**.
Convexity converts concentration of the free energy into concentration of its derivative; the
resulting error telescopes when integrated in the parameter.

- `intervalIntegral.integral_sub_shift_le_of_monotone` (a Mathlib gap) — for monotone `g` and
  `δ > 0`, `∫_a^b (g(x+δ) - g(x-δ)) dx ≤ 2δ (g(b+δ) - g(a-δ))`, with **no ordering of `a` and `b`
  required**: interval integrals are signed and the telescoping is unconditional. This is what
  makes the `1/δ` price of Griffiths' lemma integrable in the parameter.
- `ConvexOn.abs_deriv_sub_le` and `ConvexOn.integral_abs_deriv_sub_le` — Talagrand's
  Lemmas 12.1.5–12.1.6 in the two-sided-derivative form he states them.
- `SpinGlass.FiniteGibbs.convexOn_integral_free_energy_density`,
  `deriv_integral_free_energy_density`, `monotone_deriv_integral_free_energy_density` — the mean
  free energy is convex and differentiable everywhere along an affine path, so its derivative is
  monotone.
- `SpinGlass.FiniteGibbs.intervalIntegral_integral_abs_meanEnergy_sub_le` — **the second half**:
  `∫_a^b 𝔼|⟨V/n⟩ - 𝔼⟨V/n⟩| dx ≤ 2δ (p'(b+δ) - p'(a-δ)) + 3(b-a)C/δ` for any `C` bounding the mean
  absolute deviation of the free energy *on the enlarged window* — a weaker hypothesis than a
  global bound, which matters because the SK constant grows with `β`.
- `SpinGlass.FiniteGibbs.gibbs_average_abs_smul_sub_const_le` and
  `SpinGlass.FiniteGibbs.intervalIntegral_integral_totalFluct_le` — **the split**: the total
  fluctuation is at most the Gibbs part plus the disorder part.
- `SpinGlass.FiniteGibbs.variance_free_energy_density_add_const_le_gibbs_covariance` and
  `memLp_free_energy_density_affine` — the sharp self-averaging bound and the `L²` membership, both
  generalized to carry an **external field** inside the free energy (the previous statements were
  the `c₀ = 0` case).
- `SpinGlass.variance_skFreeEnergy_le` — `Var[p_N^ω(β)] ≤ β²/(2N)`, Talagrand Vol. I,
  Theorem 1.3.4 for the SK model, from the Dirichlet-energy form of Gaussian Poincaré; hence
  `SpinGlass.integral_abs_skFreeEnergy_sub_mean_le`, `𝔼|p_N^ω(β) - p_N(β)| ≤ |β|/√(2N)`.
- `SpinGlass.intervalIntegral_skMeanEnergy_fluctuation_le` and
  `SpinGlass.intervalIntegral_skTotalEnergy_fluctuation_le` — **Theorem 12.1.1 for the SK model**,
  fully explicit:
  `∫_a^b 𝔼⟨|H/N - 𝔼⟨H/N⟩|⟩ dβ ≤ √((b-a)b/(2N)) + δ(b+δ) + 3(b-a)(b+δ)/(δ√(2N))`
  for every `δ > 0`; at `δ = N^{-1/4}` this is `O(N^{-1/4})`, Talagrand's rate. **The energy per
  site self-averages.**

## Proved: self-averaging for an arbitrary bounded Gaussian disorder (Vol. II, §12.1–12.2)

Everything Talagrand proves about the fluctuations of the energy uses only three properties of the
covariance matrix `S`: it is positive semidefinite, its diagonal is the constant `D`, and
`|S σ τ| ≤ D`. Every mixed `p`-spin model has them (`posSemidef_overlapPolyMatrix` supplies the
first; `D = N ξ(1)` and `|ξ(r)| ≤ ξ(1)` on `[-1,1]` the others), and so does Guerra's
replica-symmetric reference kernel. The whole chain is therefore proved once, for such an `S`, and
the Sherrington–Kirkpatrick statements are the instance `S = skCovMatrix N 1`, `D = N/2`.

- `SpinGlass.gaussField`, `gaussField_map_smul`, `covarianceOperator_gaussField_apply` — the
  reference field, and the fact that the disorder at strength `β` is the reference field **dilated**
  by `β`. That dilation is what makes the free energy convex in `β` with computable derivative.
- `SpinGlass.gaussFreeEnergy_eq_integral_smul`, `hasDerivAt_gaussFreeEnergy`.
- `SpinGlass.deriv_gaussFreeEnergy_eq` — **Lemma 1.3.11 in general form**:
  `∂p_N/∂β = (β/N)(D - 𝔼⟨S(σ¹,σ²)⟩)`; `abs_deriv_gaussFreeEnergy_le` — **Lemma 12.1.4**,
  `|∂p_N/∂β| ≤ 2βD/N`.
- `SpinGlass.variance_gaussFreeEnergy_le` — **Theorem 1.3.4**, `Var[p_N^ω(β)] ≤ β²D/N²`; and
  `integral_abs_gaussFreeEnergy_sub_mean_le`, `𝔼|p_N^ω - p_N| ≤ |β|√D/N`.
- `SpinGlass.intervalIntegral_gaussEnergy_fluctuation_le`,
  `intervalIntegral_gaussMeanEnergy_fluctuation_le`,
  `intervalIntegral_gaussTotalEnergy_fluctuation_le` — **Theorem 12.1.1**, in the two halves and
  combined, with every constant explicit.
- `SpinGlass.integral_gibbs_average_abs_sub_mean_gaussField_eq` — the normalisation dictionary
  between the error bound (Gibbs measure at the Gaussian sample) and Theorem 12.1.1 (the dilation
  path over a fixed reference field): they differ by exactly one factor `β N`.
- `SpinGlass.abs_gaussGhirlandaGuerra_error_le` and
  `exists_beta_abs_gaussGhirlandaGuerra_error_le` — **the Ghirlanda–Guerra error and its
  `O(N^{-1/4})` bound**, for any such disorder.

## Proved: the Ghirlanda–Guerra identities for the SK model, up to `O(N^{-1/4})` (Vol. II, §12.2)

- `FiniteGibbs.abs_integral_gibbs_average_energy_mul_sub_le_integral_abs` and
  `FiniteGibbs.ghirlandaGuerra_error_le_integral_abs` — **the sharp `L¹` error bound**,
  `|𝔼⟨H_{σⁱ}f⟩ - a𝔼⟨f⟩| ≤ B · 𝔼⟨|H - a|⟩`. This is Hölder, not Cauchy–Schwarz, and it is the form
  Theorem 12.1.1 closes: that theorem controls exactly the mean *absolute* fluctuation. The `L²`
  form `abs_integral_gibbs_average_energy_mul_sub_le` / `ghirlandaGuerra_error_le` is now a
  corollary of it, obtained by two further Cauchy–Schwarz steps — the previous statements were the
  weaker ones.
- `SpinGlass.skCovMatrix_diag`, `abs_skCovMatrix_le`, `skFieldAt`, `skFieldAt_eq`,
  `skField_map_smul_eq_skFieldAt` — the SK model as an instance of the general hypotheses:
  `S = skCovMatrix N 1`, `D = N/2`.
- `SpinGlass.abs_skGhirlandaGuerra_error_le` — **the Ghirlanda–Guerra error of the SK model at
  inverse temperature `β`**, bounded by `B β N` times the fluctuation of Theorem 12.1.1. Exact at
  every finite volume, with no perturbation added.
- `SpinGlass.exists_beta_abs_skGhirlandaGuerra_error_le` — **the identities hold up to an explicit
  `O(N^{-1/4})` error at some inverse temperature in every window.** The mean value theorem for
  interval integrals turns Theorem 12.1.1's integrated bound into a bound at a single `β`, which is
  Talagrand's conclusion "for the typical value of `x`".
- `SpinGlass.variance_skFreeEnergy_le`, `integral_abs_skFreeEnergy_sub_mean_le` are now one-line
  instances of the general theorems; the sharper SK constants in
  `intervalIntegral_skTotalEnergy_fluctuation_le` come from the sharper input
  `0 ≤ ∂p_N/∂β ≤ β/2` (`deriv_skFreeEnergy_nonneg_le`), which uses `0 ≤ 𝔼⟨R₁₂²⟩ ≤ 1` and is not
  available for a general kernel.

## Proved: the Ghirlanda–Guerra combination of a kernel, and of a disorder *component* (§12.2)

The identities at the model's own profile `ξ` come from the defect identity for the Hamiltonian.
The identities at *individual monomial* test functions `r ↦ rᵖ` come from the same identity applied
to a single `p`-spin **component** of a mixed Hamiltonian. This section is that generalisation,
carried out once at the level of the finite replica calculus.

- `FiniteGibbs.freshKernelAvg` — the fresh-replica average `⟨c ρ ·⟩` of an *arbitrary* kernel: no
  Gaussian structure, and linear in the kernel (`freshKernelAvg_add`, `freshKernelAvg_smul`).
- `FiniteGibbs.covKernel μ w σ τ = Cov(⟪H, w σ⟫, H τ)` — the cross-covariance kernel along a family
  of directions `w`; for `w = e_·` the Hamiltonian's own kernel, for `w σ = Wᵀ e_σ` the cross kernel
  of the component `W H`. In general **not symmetric**.
- `FiniteGibbs.componentField w H` — the component field `σ ↦ ⟪H, w σ⟫`, packaged as a vector of
  `EnergySpace α` so that the whole calculus written for the energy applies to it verbatim;
  `componentField_std_basis` says the coordinate case is the disorder itself.
- `FiniteGibbs.ghirlandaGuerraCombinationOf μ c m f i` — **the Ghirlanda–Guerra combination of a
  kernel** (Vol. II, Definition 15.3.4; Panchenko (1.1)), with the kernel a parameter;
  `ghirlandaGuerraCombination` is the Hamiltonian's own case.
- `FiniteGibbs.integral_inner_mul_gibbs_average_n_det`,
  `FiniteGibbs.integral_gibbs_average_n_det_inner_mul`,
  `FiniteGibbs.integral_gibbs_average_n_det_inner_mul_erase`,
  `FiniteGibbs.integral_gibbs_average_one_inner` — the cavity identity, the cavity identity with a
  component field inside the bracket, its diagonal-separated form, and the mean of a component
  field. The coordinate cases are the energy statements, now corollaries.
- `FiniteGibbs.ghirlandaGuerra_defect_of` — **the component defect identity**: the
  Ghirlanda–Guerra combination of `c_w` is the covariance between the component field at the `i`-th
  replica and the observable.
- `FiniteGibbs.abs_integral_gibbs_average_field_mul_sub_le_integral_abs` — the sharp `L¹` bound
  `|𝔼⟨(u H)_{σⁱ} f⟩ - a 𝔼⟨f⟩| ≤ B 𝔼⟨|u H - a|⟩` for an **arbitrary** field `u`, with the three
  integrability facts as hypotheses and **no Gaussian hypothesis at all**.
- `FiniteGibbs.ghirlandaGuerra_error_of_le_integral_abs` — **the component Ghirlanda–Guerra error
  bound**: the combination of `c_w` is at most `B` times the mean absolute fluctuation of the
  component field. Exact at every finite volume.
- `LinearMap.IsPositive.range_le_range_of_le` — **Douglas' lemma in finite dimensions** (a Mathlib
  gap): `0 ≤ T ≤ S ⟹ range T ≤ range S`, via
  `LinearMap.IsPositive.apply_eq_zero_of_inner_self_eq_zero` and
  `LinearMap.IsSymmetric.range_le_range_of_ker_le_ker`. This is what produces the directions `w`
  realising a prescribed monomial kernel: with `S` the Hamiltonian's covariance and `T` the
  monomial's, every column of `T` is `S` applied to something — the conditional expectation of the
  component given the Hamiltonian.

## Proved: the disorder as a linear image of an abstract Gaussian (Vol. I, §1.7; Vol. II, §12.1)

The Hamiltonian of a spin glass built from independent pieces is a *linear image* `A x` of an
underlying Gaussian vector `x`, and the perturbation arguments differentiate with respect to a
component of `x` that is not the Hamiltonian. The whole cavity layer is therefore stated for
`(P, A)`, with the current theory as the case `A = id`.

- `ProbabilityTheory.IsGaussian.integral_inner_mul_comp_clm` — **first-order Gaussian integration
  by parts along a linear substitution** (a Mathlib gap):
  `∫ ⟪x, h⟫ G(A x) ∂P = ∫ (DG (A x)) (A (C_P h)) ∂P`. The direction in which `G` is differentiated
  is the *cross-covariance* `A (C_P h)`; this is the first-order companion of the second-order
  two-map trace identity `IsGaussian.integral_fderiv_clm_add_apply_clm`.
- `FiniteGibbs.integral_inner_mul_gibbs_average_n_det_comp` — **the cavity identity for a
  Hamiltonian that is a linear image of the disorder**:
  `∫ ⟪x, h⟫ ⟨f⟩_{A x} ∂P = ∫ ( n ⟨f⟩ ⟨v⟩ - ∑_{l<n} ⟨f · v(σˡ)⟩ ) ∂P` with `v = A (C_P h)`.
  `integral_inner_mul_gibbs_average_n_det` and `integral_apply_mul_gibbs_average_n_det` are now
  three-line corollaries.
- `FiniteGibbs.integral_gibbs_average_n_det_inner_mul_comp` — **the same with a component field
  inside the bracket**: for directions `w` in the *disorder* space,
  `𝔼⟨⟪x, w(σⁱ)⟫ f⟩ = 𝔼[ m ⟨f ⟨c(σⁱ,·)⟩⟩ - ∑_{l<m} ⟨f c(σⁱ,σˡ)⟩ ]` with the cross-covariance
  kernel `c(σ,τ) = Cov(⟪x, w σ⟫, (A x) τ) = (A (C_P (w σ))) τ`. With `Ω = E × E`,
  `A (x,y) = x + t y` and `w σ = (0, e_σ)` this isolates the second summand of the Hamiltonian and
  its kernel is `t` times the second block's covariance — constant diagonal, as §12.1 requires.
- `Matrix.PosSemidef.apply_symm`, `Matrix.PosSemidef.transpose_eq`,
  `EuclideanSpace.real_inner_eq_dotProduct` — the elementary algebra, for an arbitrary finite index
  type.
- `ProbabilityTheory.inner_covarianceOperator_multivariateGaussian`,
  `covarianceOperator_multivariateGaussian_apply` — **the covariance operator of a centered
  `multivariateGaussian` is multiplication by its matrix** (a Mathlib gap: Mathlib has the bilinear
  form, but it is the *operator* that appears in Gaussian integration by parts).
- `ProbabilityTheory.multivariateGaussian_map_add_prod` — **the sum of two independent centered
  multivariate Gaussians is the centered multivariate Gaussian with the summed covariance** (a
  Mathlib gap), and `multivariateGaussian_map_add_smul_prod` — the law of the interpolating field
  `x + t y` is `mvG 0 (S + t²T)`.
- `SpinGlass.overlapCovMatrix_add_smul`, `nonneg_coeff_add_smul_sq`,
  `map_add_smul_prod_gaussField_overlapCovMatrix` — **the interpolating field of two independent
  mixed `p`-spin disorders is again a mixed `p`-spin disorder**, with profile `A + t²B`. Taking
  `B = aₚrᵖ` and `A = ξ - aₚrᵖ` the family passes through the model at `t = 1`, its covariance is
  overlap-driven with nonnegative coefficients for *every* `t` — hence constant diagonal and
  dominated by it — and differentiating in `t` differentiates in the `p`-spin coupling alone.

## Proved: single monomials are components of the disorder (Vol. II, §12.2 → §15.3)

Douglas' lemma turns the algebra into an actual construction, and the Ghirlanda–Guerra identities
at *individual monomial* test functions are then reduced to one concentration statement.

- `SpinGlass.inner_covarianceOperator_multivariateGaussian` — for a centered
  `multivariateGaussian`, the covariance operator's bilinear form is the quadratic form of the
  matrix, at **every** pair of vectors (the Dirac-basis statement is now its corollary).
- `SpinGlass.exists_directions_covKernel_eq` — **every positive semidefinite kernel dominated by
  the disorder's own covariance is the cross kernel of a component of the disorder**: if
  `0 ≤ T ≤ S` then there are directions `w` with `Cov(⟪H, w σ⟫, H τ) = T σ τ`.
- `SpinGlass.exists_directions_covKernel_monomial` — for a mixed `p`-spin model, applied to the
  single monomial `aₚ N Rᵖ` (the difference `N ξ(R) - aₚ N Rᵖ` is again an overlap-driven kernel
  with nonnegative coefficients, hence positive semidefinite).
- `SpinGlass.ghirlandaGuerraCombinationOf_eq_overlapArrayLaw`,
  `ghirlandaGuerra_defect_eq_combinationOf`, `abs_ghirlandaGuerra_defect_of_le` — the translation
  and the defect identity, now for an **arbitrary** kernel `c σ τ = κ φ(R_{στ})`, not only the
  Hamiltonian's own; the own-kernel statements are corollaries.
- `SpinGlass.abs_ghirlandaGuerra_defect_le_of_covKernel_monomial` (and its existence form
  `exists_abs_ghirlandaGuerra_defect_monomial_le`) — **the monomial capstone**: for a mixed
  `p`-spin model, the defect in Definition 15.3.4 at `φ(r) = rᵖ` is at most `‖g‖/(n aₚ N)` times
  the mean absolute fluctuation of the `p`-spin component field `σ ↦ ⟪H, w σ⟫`. Exact at every
  finite volume, no perturbation added. Since monomial test functions suffice
  (`satisfiesGhirlandaGuerra_of_monomial`), the identities at *every* continuous test function are
  now reduced to the self-averaging of that single field.

## Proved: mixed `p`-spin models as an instance (Vol. II, Eq. (14.57))

Talagrand's realizability criterion says that `c(σ,τ) = N ξ(R_{στ})` is a Gaussian covariance as
soon as `ξ` has nonnegative coefficients. That makes every mixed `p`-spin model an instance of the
three hypotheses (`PosSemidef`, constant diagonal `D`, `|S| ≤ D`) under which the whole of §12.1
was proved above, with `D = N ξ(1)`, so that `D/N = ξ(1)` is a constant and every bound is
uniform in the volume.

- `Polynomial.eval_one_nonneg_of_nonneg_coeff` and
  `Polynomial.abs_eval_le_eval_one_of_nonneg_coeff` — `|P(r)| ≤ P(1)` for `|r| ≤ 1` when the
  coefficients are nonnegative (a Mathlib gap).
- `SpinGlass.overlapCovMatrix`, `overlapCovMatrix_diag` (`= N ξ(1)`), `abs_overlapCovMatrix_le`,
  `posSemidef_overlapCovMatrix_of_polynomial` — the model and its three properties.
- `SpinGlass.deriv_mixedPSpinFreeEnergy_eq` — **Lemma 1.3.11 for a mixed `p`-spin model**:
  `∂p_N/∂β = β(ξ(1) - 𝔼⟨ξ(R₁₂)⟩)`.
- `SpinGlass.abs_deriv_mixedPSpinFreeEnergy_le` — **Lemma 12.1.4**: `|∂p_N/∂β| ≤ 2βξ(1)`.
- `SpinGlass.variance_mixedPSpinFreeEnergy_le` — **Theorem 1.3.4**: `Var[p_N^ω(β)] ≤ β²ξ(1)/N`;
  and `integral_abs_mixedPSpinFreeEnergy_sub_mean_le` — `𝔼|p_N - 𝔼p_N| ≤ |β|√(ξ(1)/N)`.
- `SpinGlass.intervalIntegral_mixedPSpinTotalEnergy_fluctuation_le` — **Theorem 12.1.1**.
- `SpinGlass.exists_beta_abs_mixedPSpinGhirlandaGuerra_error_le` — the Ghirlanda–Guerra error of an
  arbitrary mixed `p`-spin model, `O(N^{-1/4})` at some `β` in every window.

## Proved: Theorem 12.1.1 in Markov form (Vol. II, §12.1)

Theorem 12.1.1 bounds the energy fluctuation *on average* over a temperature window; Markov's
inequality converts that into a statement about *most* temperatures, which is strictly stronger
than the mean-value form.

- `MeasureTheory.measureReal_setOf_le_inter_le_of_integrableOn` and
  `intervalIntegral.measureReal_setOf_le_le`, `..._of_continuous` — **Markov's inequality on a set
  and for an interval integral** (a Mathlib gap: Mathlib had only the whole-space form
  `mul_meas_ge_le_integral_of_nonneg`).
- `SpinGlass.measureReal_setOf_gaussTotalEnergy_fluctuation_ge_le` — the set of `β ∈ (a,b]` where
  the mean absolute energy fluctuation exceeds `t` has measure at most `ε/t`, `ε` being Theorem
  12.1.1's bound.
- `SpinGlass.measureReal_setOf_gaussGhirlandaGuerra_error_gt_le` — hence **the Ghirlanda–Guerra
  identities hold at all but a set of inverse temperatures of measure `≤ ε/t`**.

## Proved: overlap-array integrals are finite Gibbs brackets (the §12.2 ↔ §15.3 dictionary)

Talagrand states the identities for the *law of the overlap array* (Ch. 15) and proves them by the
*finite replica calculus* (§12.2). These are the same numbers, and the translation is now a
theorem.

- `SpinGlass.FiniteGibbs.gibbs_average_n_det_mul_sum_gibbs_pmf` — **the fresh-replica identity**:
  averaging a kernel against an independent extra draw turns an `n`-replica bracket into an
  `(n+1)`-replica bracket, `⟨F ∑_τ p(τ) c(σⁱ,τ)⟩ₙ = ⟨F c(σⁱ,σⁿ⁺¹)⟩ₙ₊₁`. This is what puts the
  "new replica" term and the "old replica" terms in one and the same space.
- `SpinGlass.map_take_configReplicaArrayLaw` — any finite injectively-indexed family of replicas
  of the i.i.d. replica array is the finite replica Gibbs measure.
- `SpinGlass.integral_overlapArrayLaw_comp_take` — **the dictionary**: for any injective indexing
  of `k` replica labels, `∫ g(R_{e l, e l'}) d(overlapArrayLaw N H) = ⟨g((R(σˡ,σˡ')))⟩ₖ`. The
  generality in the indexing is what lets the four terms of (15.40) — which live on the label sets
  `{0,…,n-1}`, `{0,…,n}` and `{0,n}` — all be translated at once.
- `SpinGlass.integral_bind_overlapArrayLaw_comp_take`,
  `integral_annealedOverlapArrayLaw_comp_take` — the disorder-averaged forms, via
  `MeasureTheory.Measure.integral_bind`.

## Proved: the Ghirlanda–Guerra combination **is** the defect in (15.40) (Vol. II, §12.2 ↔ §15.3)

- `SpinGlass.FiniteGibbs.ghirlandaGuerraCombination` — the Ghirlanda–Guerra combination as a
  **definition** (Vol. II, Definition 15.3.4 / Eq. (15.40); Panchenko (1.1)), replacing the
  spelled-out expression that previously appeared in every statement.
- `SpinGlass.overlapReplicaFun`, `SpinGlass.blockEntryCM`, `SpinGlass.blockReindex` — pulling a
  continuous test function of the `n × n` overlap block back to a function of `n` configurations.
- `SpinGlass.ghirlandaGuerraCombination_eq_overlapArrayLaw` — **the translation**: for any
  Hamiltonian law whose covariance kernel is `κ φ(R_{στ})`,
  `ggCombination ν n (g ∘ overlaps) i`
  `  = κ (n ∫ φ(R_{i,n}) g - (∫φ(R_{i,n}))(∫g) - ∑_{l≠i} ∫ φ(R_{i,l}) g)`.
- `SpinGlass.ghirlandaGuerra_defect_eq_combination` — hence **the defect in Talagrand's identity
  (15.40) is exactly `ggCombination/(nκ)`**, and `abs_ghirlandaGuerra_defect_le` turns any bound on
  the combination into a bound on the defect.
- `SpinGlass.exists_beta_abs_mixedPSpinGhirlandaGuerra_defect_le` — **the capstone**: for every
  mixed `p`-spin model, at some inverse temperature in every window, the defect in (15.40) at the
  model's own profile `φ = ξ` is at most `‖g‖/(nβ)` times Theorem 12.1.1's bracket, which is
  `O(N^{-1/4})`. No perturbation, no limit: an explicit finite-volume rate.

## Proved: Gaussian concentration (Vol. I, §1.3)

Write `C = covarianceOperator μ` and `Q h = ∫ ⟪C (∇ h x), ∇ h x⟫ ∂μ` for the Dirichlet energy of
`h` against `C`. All of the following are absent from Mathlib.

- `ProbabilityTheory.IsGaussian.integral_prod_mul_fderiv_gaussRot_eq` — **the slice identity**, the
  engine. At each angle the quarter-turn rotation `map_gaussRotMap_prod` restores `μ ⊗ μ`, so the
  first variable becomes an affine function of the rotated pair and one Gaussian integration by
  parts (`integral_inner_mul_eq_integral_fderiv_covarianceOperator`) trades the surviving linear
  factor for a derivative, producing the chain-rule weight `-sin θ`. Since `∫₀^{π/2} sin θ dθ = 1`,
  every bound on the slice becomes a covariance bound with no constant
  (`abs_covariance_le_of_slice_le`).
- `ProbabilityTheory.IsGaussian.abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator`
  — **the Gaussian covariance inequality**, `|cov[f, g]| ≤ √(Q f) √(Q g)`. The slice is bounded by
  Cauchy–Schwarz for the positive operator `C` in its *weighted* arithmetic–geometric form
  (`LinearMap.IsPositive.abs_inner_le_half_add_smul`, a Mathlib gap, together with
  `LinearMap.IsPositive.sq_inner_le`); the weight rides through the whole argument and is
  optimised only at the end (`Real.le_sqrt_mul_sqrt_of_forall_pos`, the statement that the
  geometric mean is the infimum of the weighted arithmetic means — also a Mathlib gap). That is
  what recovers the Cauchy–Schwarz constant without ever needing Cauchy–Schwarz for an integral.
  The weighted and unweighted forms
  (`abs_covariance_le_half_add_smul_integral_inner_covarianceOperator`,
  `abs_covariance_le_half_add_integral_inner_covarianceOperator`) are also stated.
- `ProbabilityTheory.IsGaussian.variance_le_integral_inner_covarianceOperator_gradient` — **the
  Gaussian Poincaré inequality in its sharp form**, `Var[f] ≤ Q f`, the diagonal `g = f` of the
  above. No constant, no norm: only the Dirichlet energy.
- `ProbabilityTheory.IsGaussian.abs_covariance_le_opNorm_covarianceOperator_mul` and
  `variance_le_opNorm_covarianceOperator_mul_sq` — the operator-norm forms `|cov| ≤ ‖C‖ Kf Kg`,
  `Var[f] ≤ ‖C‖ K²`, obtained from the same slice identity by bounding with operator norms
  instead. The constant is again `1`; the Cauchy–Schwarz-in-`θ` form of the rotation argument,
  which discards the `sin θ` weight, only gives `π²/8`.
- `ProbabilityTheory.IsGaussian.gaussianInterp_eq_gaussRot` identifies the rotation with the
  interpolation path used everywhere above: one smart path in two parameterizations, `cos θ = √t`.
- Supporting Mathlib gaps: `norm_le_add_mul_norm_of_norm_fderiv_le` and
  `MeasureTheory.MemLp.of_norm_fderiv_le` (a map with bounded derivative grows linearly, hence lies
  in every `Lᵖ` in which the identity does, which for a Gaussian measure is every `p ≠ ∞`);
  `norm_gradient` and `ContDiff.continuous_gradient`.

Applied to the free energy:

- `FiniteGibbs.gradient_free_energy_density` — `∇F_n(H) = -(1/n) ∑_σ ⟨σ⟩ e_σ`: the gradient of the
  free energy density **is** the Gibbs measure. Hence `Q F_n` is a two-replica bracket.
- `GaussianDisorder.variance_free_energy_density_le_gibbs_kernel` — **self-averaging in
  Talagrand's form**: `Var[F_N] ≤ (1/N²) 𝔼⟨K(σ¹, σ²)⟩`. For a mixed `p`-spin model
  `K σ τ = N ξ(R_{στ})`, so this is `ξ(1)/N`. The operator-norm route
  (`GaussianDisorder.variance_free_energy_density_le`) is also proved but is far weaker here,
  since `‖C‖` on `EnergySpace N` grows with the number of configurations, not with `N`; the
  Dirichlet-energy form is what makes the bound thermodynamically meaningful. The SK and reference
  disorders are instances of `GaussianDisorder` (see below), so this one statement covers both.

## Proved: Guerra–Toninelli superadditivity (Vol. I, Thm 1.3.9)

The whole interpolation pipeline is now general in the two covariance kernels, so Guerra's
comparison is one theorem with two instances: the replica-symmetric bound and the splitting bound.

- `SpinGlass.guerraTrace` — the pointwise Guerra trace `½(∑∑K₁ D²F - ∑∑K₂ D²F)` of a pair of
  covariance kernels at a Hamiltonian.
- `derivative_value_guerraPhi_eq_trace_integral`, `hasDerivAt_guerraPhi_eq_trace_integral` — the
  interpolation derivative equals the disorder average of the Guerra trace, for an **arbitrary**
  independent pair of centered Gaussian Hamiltonians with symmetric kernels `K₁`, `K₂`. `β` and `q`
  no longer occur: the SK/reference pair is an instance, not the setting.
- `hasDerivAt_guerraPhi_le`, `deriv_guerraPhi_le`, `guerraPhi_one_le`,
  `integral_free_energy_density_le` — **Guerra's comparison theorem**: any pointwise bound
  `guerraTrace K₁ K₂ H ≤ C` gives `𝔼F(U₁ + c) ≤ 𝔼F(U₂ + c) + C`. The replica-symmetric bound is the
  instance `integral_free_energy_density_le_rs` (`C = (β²/4)(1-q)²`, supplied by
  `guerra_trace_sub_rs_le`); the splitting bound is the instance with `C = 0`, supplied by
  `trace_le_trace_of_kernel_le`.
- `SpinGlass.trace_le_trace_of_kernel_le` (and its general-`α` source
  `FiniteGibbs.trace_le_trace_of_kernel_le`) — **Slepian's sign condition for `log Z`**: if two
  covariance kernels agree on the diagonal and the first is pointwise below the second, the trace
  of the free-energy Hessian is larger for the first.
- `FiniteGibbs.sumEnergy` — the Hamiltonian of a **non-interacting composite system**, along a
  relabelling `α ≃ β × γ` of the configuration space, as a continuous linear map of the pair of
  subsystem Hamiltonians; `FiniteGibbs.Z_sumEnergy` (`Z = Z₁·Z₂`),
  `FiniteGibbs.log_Z_sumEnergy` and `FiniteGibbs.mul_free_energy_density_sumEnergy`
  (`n F_n = n₁ F_{n₁} + n₂ F_{n₂}`).
- `SpinGlass.configSplit`, `cast_mul_overlap_split` (`N R = N₁R₁ + N₂R₂`), `splitCovKernel`,
  `sk_cov_kernel_le_splitCovKernel` and `sk_cov_kernel_diag_eq_splitCovKernel` — the SK kernel is
  **dominated** by the split kernel and **agrees with it on the diagonal**, which are exactly the
  two hypotheses of `trace_le_trace_of_kernel_le`. The domination is Sedrakyan's inequality
  `Real.sq_add_div_add_le`, the two-term case of Mathlib's `Finset.sq_sum_div_le_sum_sq_div`.
- `GaussianDisorder.split` — **the non-interacting composite disorder**: two independent Gaussian
  disorders on the two blocks, assembled into a centered Gaussian Hamiltonian on the composite
  configuration space with kernel `splitCovKernel`. Its covariance is computed from the
  block-diagonal covariance of the joint law, not by hand.
- `SpinGlass.H_field_eq_sumEnergy` — the external field does not couple the two blocks.
- `SpinGlass.guerraTrace_splitCovKernel_nonpos` — the Guerra trace of the splitting comparison is
  nonpositive.
- `SpinGlass.mul_integral_free_energy_density_add_le` — **Guerra–Toninelli superadditivity**:
  `N₁ 𝔼F_{N₁} + N₂ 𝔼F_{N₂} ≤ (N₁+N₂) 𝔼F_{N₁+N₂}`.
- `Superadditive` and `Superadditive.tendsto_lim` — **Fekete's lemma in superadditive form**:
  if `u m + u n ≤ u (m + n)` and the averages are bounded above then `u n / n → sSup`. Mathlib has
  only the subadditive form (`Subadditive.tendsto_lim`); the superadditive one is the shape the
  thermodynamic limit takes, with `u N = N p_N`.

## Proved: the law of a Gaussian disorder is determined by its kernel

- `ProbabilityTheory.covarianceOperator_map_toLp_prodMk` and its two block corollaries are now
  stated for a pair of random vectors valued in **two different** Hilbert spaces. That is what a
  splitting argument needs (the two blocks live on different configuration spaces) and it is the
  general form of the statement; the same-space case used by Guerra's interpolation is an instance.
- `GaussianDisorder.map_U_eq` — two Gaussian Hamiltonians with the same covariance kernel, carried
  by any two probability spaces, have the same law (`ProbabilityTheory.IsGaussian.ext` at the
  coordinate expansion of `covarianceBilin`), and `GaussianDisorder.integral_comp_eq` — hence every
  disorder average is a function of the kernel alone.

## Proved: the thermodynamic limit (Vol. I, Theorem 1.3.9)

**`SpinGlass.tendsto_skFreeEnergy : ∀ β h, Tendsto (fun N => skFreeEnergy N β h) atTop`**
**`(nhds (skFreeEnergyLimit β h))`** — unconditional, no hypotheses. The chain:

- `skFreeEnergy N β h` — the SK free energy as a *function of `N`, `β`, `h` alone*, computed on the
  canonical Gaussian disorder law `multivariateGaussian 0 (skCovMatrix N β)`. That this is
  legitimate is `GaussianDisorder.map_U_eq_multivariateGaussian` (the law of a Gaussian disorder is
  the canonical multivariate Gaussian at its kernel matrix) and
  `integral_free_energy_density_eq_skFreeEnergy` (every SK disorder on every probability space
  computes it).
- `SplitSample`, `splitSampleLaw`, `map_blockOne_splitSampleLaw` and its two siblings — the
  canonical probability space for the splitting comparison: the product of the two block Gaussian
  laws with the whole-system one. Its three coordinates are SK disorders, the two blocks are
  independent (`indepFun_iff_map_prod_eq_prod_map_map`, their joint law being the first factor),
  and their non-interacting composite is independent of the whole-system Hamiltonian
  (`indepFun_prod`).
- `mul_skFreeEnergy_add_le` — hence `N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁+N₂) p_{N₁+N₂}` for the sequence,
  and `superadditive_mul_skFreeEnergy` — `N ↦ N p_N` is `Superadditive` (the degenerate cases
  `N = 0` are trivial).
- `simpleDisorderZero` — the trivial disorder: the zero Hamiltonian is a centered Gaussian disorder
  at the replica-symmetric kernel with `q = 0`, which vanishes identically. It is independent of
  everything (`indepFun_const_right`), so Guerra's bound applies to it with no construction.
- `free_energy_density_le_of_neg_le` (`F_N(H) ≤ log 2 + b/N` when `-H σ ≤ b`; there are `2^N`
  configurations), `abs_magnetization_le` (`|m(σ)| ≤ N`) and `free_energy_density_H_field_le` — the
  free energy of the pure external field is at most `log 2 + |h|`.
- `skFreeEnergy_le` — Guerra's bound at `q = 0` compares `p_N` with that deterministic free energy:
  `p_N ≤ log 2 + |h| + β²/4`, **uniformly in `N`**. This is the `BddAbove` hypothesis of Fekete.
- `tendsto_skFreeEnergy` and `skFreeEnergy_le_limit` — Fekete's lemma in superadditive form:
  `p_N → p` and `p = sup_N p_N`.
- `gaussFreeEnergy N S h` and `integral_free_energy_density_eq_gaussFreeEnergy` — the free energy
  of *any* centered Gaussian disorder, as a function of `(N, S, h)` alone; `skFreeEnergy` and
  `refFreeEnergy` are its two instances.
- `exists_disorder_triple` — three independent Gaussian disorders at any three positive
  semidefinite covariances, with the composite of the first two independent of the third. This is
  the data a splitting comparison consumes, and both the SK superadditivity and the reference
  additivity are obtained from it.

## Proved: the replica-symmetric upper bound, explicitly (Vol. I, §1.3, Eq. (1.73))

**`SpinGlass.skFreeEnergyLimit_le_rs : ∀ β q h, 0 ≤ q →`**
**`p(β,h) ≤ 𝔼 log (2 cosh (β√q z + h)) + (β²/4)(1-q)²`** — unconditional, `z` a standard Gaussian.
Guerra's bound made quantitative in the thermodynamic limit. The chain:

- `simple_cov_kernel_eq_splitCovKernel` — the replica-symmetric kernel `N β² q R` is **additive
  over sites**: it *is* its own split kernel, because `N R = N₁ R₁ + N₂ R₂`. Consequently
- `mul_refFreeEnergy_add` — the reference free energy is *additive*, not merely superadditive, so
- `refFreeEnergy_eq_one` — `p^ref_N = p^ref_1` for every `N ≥ 1`: the reference model has no
  size dependence at all.
- `oneSiteRefDisorder` — on one site the reference Hamiltonian is `V(σ) = β√q z σ` for a standard
  Gaussian `z`, realised as a continuous linear image of `z` on `Ω = ℝ` with the law
  `gaussianReal 0 1` (which the `MeasurableSpace`-only form of `GaussianDisorder` now permits
  directly, with no wrapper type).
- `Z_one_oneSiteRef` — hence `Z₁ = 2 cosh(β√q z + h)`, and `refFreeEnergy_one_eq` —
  `p^ref_1 = 𝔼 log (2 cosh(β√q z + h))`.
- `skFreeEnergy_le_refFreeEnergy`, `skFreeEnergyLimit_le`, `skFreeEnergy_le_rs`,
  `skFreeEnergyLimit_le_rs` — Guerra's bound at every size and in the limit, in closed form.

## Proved: Hopfield (Vol. I Ch. 4 / Vol. II Ch. 10)

- §4.2 / Lemma 4.2.1: `hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`.

## Statement layer (not yet discharged)

These are `Prop`-valued definitions recording Talagrand's statements; each still needs a proof.

- `SpinGlass.Cascades.HopfieldLocalizationLumps` — Vol. I, Thm. 4.3.2 (Bovier–Gayrard).
- `SpinGlass.Cascades.HopfieldLocalizationCenter` — Vol. II, Thm. 10.3.1.
- `GG1`, `GG1_prefix`, `SK_GG1`, `Hopfield_SK_GG1`, `HopfieldOverlap_GG1Kernel` — Vol. II Ch. 12
  Ghirlanda–Guerra identities. `GG1_of_GG1_prefix` and
  `GG1_prefix_of_condExp_lastReplica_ae` reduce them to a conditional-expectation identity.

  **The finite-volume Gibbs replica law does not satisfy them**: at `N = n = 1` `SK_GG1` asserts
  `m = m ^ 3` for the magnetization `m`. No definition names that false proposition. The
  Ghirlanda–Guerra identities hold exactly only for asymptotic Gibbs measures, or after a
  perturbation; the exact finite-volume statement is the cavity identity and the defect identity
  above.
-/

namespace SpinGlass

end SpinGlass
