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
`ProbabilityTheory.HasGaussianLaw`. The SK and reference disorders are abbreviations for it at two
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
- `FiniteGibbs.integral_apply_mul_gibbs_average_n_det` — **the cavity identity**:
  `𝔼[H_ρ ⟨f⟩] = 𝔼[ n ⟨f⟩ ⟨C e_ρ⟩ - ∑_{l<n} ⟨f · (C e_ρ)(σˡ)⟩ ]`, obtained by Gaussian
  integration by parts applied to the Gibbs average as a functional of the Hamiltonian. It is
  **exact at every finite volume**, for an arbitrary finite configuration space and an arbitrary
  centered Gaussian Hamiltonian law — unlike the Ghirlanda–Guerra identities, which are its
  asymptotic shadow after the Hamiltonian is replaced by its mean.

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
  exact finite-volume replacement for the (false) `SK_GG1_gibbsKernel`.
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
- `FiniteGibbs.ghirlandaGuerra_error_le_energy_fluctuation` — the two combined: the
  Ghirlanda–Guerra error is bounded by a covariance-kernel expression in which the observable no
  longer appears at all.

## Dependencies

`GibbsMeasure` (branch `mc3`, rev `8a158f0`) is required for its exchangeability layer only:
`IsExchangeable`, the Hewitt–Savage zero-one law, and `existsUnique_mixing_of_isExchangeable`
(de Finetti in Dynkin's form, with uniqueness over a standard Borel space). Mathlib has none of
these. They are the ancestors of Aldous–Hoover and Dovbysh–Sudakov, which Vol. II Ch. 12–15 needs.
The DLR/specification half of that repository is not imported.

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

## Proved: Hopfield (Vol. I Ch. 4 / Vol. II Ch. 10)

- §4.2 / Lemma 4.2.1: `hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`.

## Statement layer (not yet discharged)

These are `Prop`-valued definitions recording Talagrand's statements; each still needs a proof.

- `SpinGlass.Cascades.HopfieldLocalizationLumps` — Vol. I, Thm. 4.3.2 (Bovier–Gayrard).
- `SpinGlass.Cascades.HopfieldLocalizationCenter` — Vol. II, Thm. 10.3.1.
- `GG1`, `GG1_prefix`, `SK_GG1`, `Hopfield_SK_GG1`, `HopfieldOverlap_GG1Kernel` — Vol. II Ch. 12
  Ghirlanda–Guerra identities. `GG1_of_GG1_prefix` and
  `GG1_prefix_of_condExp_lastReplica_ae` reduce them to a conditional-expectation identity.

  **`SK_GG1_gibbsKernel` is false at finite volume** and names an asymptotic target only: at
  `N = n = 1` it asserts `m = m ^ 3` for the magnetization `m`. The Ghirlanda–Guerra identities
  hold exactly only for asymptotic Gibbs measures, or after a perturbation. The exact
  finite-volume statement is the cavity identity below.
-/

namespace SpinGlass

end SpinGlass
