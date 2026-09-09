import SpinGlass.HopfieldConvolution
import SpinGlass.MixedPSpinThermodynamicLimit
import SpinGlass.GuerraInequality
import SpinGlass.SKDisorderExists
import SpinGlass.GaussianTrace
import SpinGlass.GuerraDerivativeTrace

/-!
# Talagrand Vol. I–II: main results index

Proved theorems, and the outstanding capstones. There is no statement layer: every named
object in the library is either a definition of a mathematical object or a proved theorem.
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

## Proved: Lemma 12.1.4 for a component of the disorder (Vol. II, §12.1)

The cavity layer is now complete for a linear-image Hamiltonian, and the first quantitative
consequence — a *volume-uniform* bound on the mean energy of a single summand — is in place.

- `FiniteGibbs.crossKernel P A w σ τ = Cov(⟪x, w σ⟫, (A x) τ)` — **the cross-covariance kernel of
  a component of the disorder against a linear-image Hamiltonian**, with `abs_crossKernel_le`.
- `FiniteGibbs.fderiv_gibbs_average_n_det_add_const` — the replica bracket differentiates through
  an additive shift of the Hamiltonian, so the external field costs nothing: all the linear-image
  cavity identities are stated for the **affine** Hamiltonian `A x + c`.
- `FiniteGibbs.integral_gibbs_average_n_det_inner_mul_comp_erase` — the component cavity identity
  with the diagonal term separated.
- `FiniteGibbs.integral_gibbs_average_one_inner_comp` — the mean of a component field is its mean
  cross kernel against a fresh replica, minus the diagonal.
- `FiniteGibbs.abs_integral_gibbs_average_one_inner_comp_le` — **Talagrand, Vol. II, Lemma 12.1.4,
  for a component**: `|𝔼⟨⟪x, w ·⟫⟩| ≤ 2 M` whenever the cross kernel is bounded by `M`.
- `SpinGlass.exists_gaussianDisorder_pair_indepFun` — **a pair of independent centered Gaussian
  disorders with prescribed positive semidefinite covariance kernels exists**, for *arbitrary*
  kernels. `exists_skDisorder_simpleDisorder_indepFun` is now a two-line corollary.
- `SpinGlass.pairAffine` — the interpolation `(x, y) ↦ x + t y` as a continuous linear map. Unlike
  `gaussianInterp` this path is **affine in the Hamiltonian**, so the free energy is convex along
  it, which is what Griffiths' lemma and the second half of Theorem 12.1.1 require.
- `SpinGlass.crossKernel_pairAffine_std_basis_right` — the cross kernel of the second block against
  `H_A + t H_B` is `t K₂`: symmetric, constant diagonal, dominated by it.
- `SpinGlass.abs_integral_gibbs_average_component_le` — **Lemma 12.1.4 for the `p`-spin
  component**: `|𝔼⟨H_B⟩| ≤ 2|t| M₂`, so for a mixed `p`-spin model the mean `p`-spin energy *per
  site* is at most `2|t| aₚ` — a constant, uniform in the volume.
- `FiniteGibbs.covarianceOperator_map_std_basis_eq_crossKernel` — **the Hamiltonian's own
  covariance kernel is the cross kernel at the adjoint directions**: if `⟪p, w σ⟫ = (A p) σ` then
  `Cov((A x) σ, (A x) τ) = (A (C_P (w σ))) τ`. No adjoint appears in the statement or the proof —
  the defining property of `w` is used once on each side.
- `SpinGlass.pairDir`, `inner_pairDir`, `crossKernel_pairAffine_pairDir` and
  `covarianceOperator_map_pairAffine_std_basis` — **the interpolated Hamiltonian `H_A + t H_B` has
  covariance kernel `K₁ + t² K₂`**, read off directly from the covariance operator with no
  identification of the law. For a mixed `p`-spin model that is `N(ξ - (1-t²)aₚrᵖ)(R)`: again
  overlap-driven with nonnegative coefficients for *every* real `t`, hence with constant diagonal
  and dominated by it — the §12.1 hypotheses, along the whole path.

## Proved: Theorem 12.1.1 for a component of the disorder (Vol. II, §12.1)

The two halves of Theorem 12.1.1 now run along the affine interpolation `H_A + x H_B`, giving the
self-averaging of a *single summand* of a mixed Hamiltonian.

- `SpinGlass.integral_id_map_pairAffine` — the interpolated Hamiltonian is centered.
- `SpinGlass.integral_abs_free_energy_density_pairAffine_sub_mean_le` — **the free energy
  concentrates along the interpolation**: `𝔼|Φ - 𝔼Φ| ≤ √(M₁ + x² M₂)/N`. Proved by Gaussian
  Poincaré on the *pair* space, transported by `variance_map` and evaluated with
  `covarianceOperator_map_pairAffine_std_basis`; no identification of the interpolated law is
  needed.
- `SpinGlass.intervalIntegral_component_fluctuation_le` — **Theorem 12.1.1 for a component**:

  `∫_a^b 𝔼⟨|H_B/N - 𝔼⟨H_B/N⟩|⟩ dx ≤ √((b-a)·2(|a|+|b|)M₂/N²)`
  `                                   + (4δ(|a|+|b|+2δ)M₂/N + 3(b-a)√(M₁+(|a|+|b|+δ)²M₂)/(δN))`.

  All three terms are explicit. For a mixed `p`-spin model `M₁, M₂ = O(N)`, so they are
  `O(N^{-1/2})`, `O(δ)` and `O(N^{-1/2}/δ)`: at `δ = N^{-1/4}` the bound is `O(N^{-1/4})`,
  Talagrand's rate. **The `p`-spin component self-averages.**

## Proved: the Ghirlanda–Guerra error of a component (Vol. II, §12.2)

- `FiniteGibbs.abs_integral_gibbs_average_field_mul_sub_le_integral_abs'` — the sharp `L¹`
  bound with the Hamiltonian `Hm p` and the tested field `u p` *separate* functions of the
  disorder, on an arbitrary measure space, with **no Gaussian hypothesis**. The old statement is
  the case `Hm = id`.
- `FiniteGibbs.componentField` — now defined for an arbitrary real inner-product disorder space.
- `FiniteGibbs.integrable_gibbs_average_n_det_comp_of_bounded`,
  `integrable_gibbs_average_n_det_inner_mul_comp`,
  `integrable_sum_gibbs_pmf_mul_abs_inner_sub_comp` — the integrability layer for a linear-image
  Hamiltonian.
- `FiniteGibbs.ghirlandaGuerra_defect_of_comp` — **the component defect identity** for a
  linear-image Hamiltonian: the combination of the cross kernel, taken against the law
  `P.map (A · + c₀)` of the Hamiltonian, is the component–observable covariance. (No new definition
  is needed: `ghirlandaGuerraCombinationOf` at that pushforward *is* the pair-setting combination,
  so the whole §15.3 translation applies verbatim.)
- `FiniteGibbs.ghirlandaGuerra_error_of_comp_le_integral_abs` — **the component Ghirlanda–Guerra
  error bound** for a linear-image Hamiltonian.
- `SpinGlass.abs_ghirlandaGuerraCombinationOf_component_le` — **the error is `B N` times exactly
  the quantity Theorem 12.1.1 controls.**
- `SpinGlass.exists_coupling_abs_ghirlandaGuerraCombinationOf_component_le` — **the composition**:
  at some coupling `x` in every window, the Ghirlanda–Guerra combination of the component's cross
  kernel is at most `B N · ε/(b-a)` with `ε` Theorem 12.1.1's bound, hence `O(N^{3/4})` — and
  dividing by the kernel scale `x aₚ N`, the defect in Talagrand's (15.40) at `φ(r) = rᵖ` is
  `O(N^{-1/4})`.

## Proved: the Ghirlanda–Guerra identity of a component, with a rate (Vol. II, §12.2 → §15.3)

The composition is closed and instantiated. The one Mathlib gap on the way — a Gaussian measure on
a Euclidean space *is* the multivariate Gaussian of its covariance matrix — is filled in general.

- `ContinuousLinearMap.ext_basis₂` — two continuous bilinear maps agreeing on all pairs of basis
  vectors are equal (the continuous `LinearMap.ext_basis`; a Mathlib gap).
- `ProbabilityTheory.covarianceBilin_eq_inner_covarianceOperator` — for a centered measure with
  second moments, `covarianceBilin μ x y = ⟪C_μ x, y⟫`.
- `ProbabilityTheory.covMatrix μ` — the covariance matrix of a measure on `EuclideanSpace ℝ ι`, as
  `LinearMap.toMatrix₂` of `covarianceBilin μ` in the standard basis; `posSemidef_covMatrix`,
  `dotProduct_covMatrix_mulVec`, `covMatrix_multivariateGaussian`.
- `ProbabilityTheory.IsGaussian.eq_multivariateGaussian` — **every Gaussian measure on a Euclidean
  space is `multivariateGaussian μ[id] (covMatrix μ)`**, with no hypothesis; and the identification
  forms `eq_multivariateGaussian_of_covarianceBilin` and
  `eq_multivariateGaussian_of_inner_covarianceOperator` from a covariance kernel prescribed on the
  standard basis (a Mathlib gap: Mathlib has
  `IsGaussian.ext` but never records the finite-dimensional consequence).
- `SpinGlass.map_pairAffine_disorderPairLaw` — hence **the law of `H_A + t H_B` is the centered
  Gaussian field with kernel `K₁ + t² K₂`**, not merely a measure with that covariance.
- `SpinGlass.exists_coupling_abs_ghirlandaGuerra_defect_component_le` — **the identity at the
  profile of a component, with a rate**: if `K₂ = κ₀ φ(R)` then at some coupling `x` in every window
  the defect in Definition 15.3.4, Eq. (15.40), at `φ` is at most `‖g‖ N ε / ((b-a) n |x κ₀|)`, `ε`
  being Theorem 12.1.1's bound for the component.
- `SpinGlass.exists_coupling_abs_ghirlandaGuerra_defect_split_le` — for any split `ξ = A + B` of
  an overlap profile into nonnegative-coefficient parts, the model with profile `A + x² B` satisfies
  the identity at `φ = B` up to that bound with `M₁ = N A(1)`, `M₂ = N B(1)`, `κ₀ = N`.
- `SpinGlass.exists_coupling_abs_ghirlandaGuerra_defect_mixedPSpin_le` — **the mixed `p`-spin
  capstone of §12.2**: for every mixed `p`-spin model `ξ` with `aₚ ≠ 0`, external field `h`, and
  window `[a,b] ⊂ (0,∞)`, there is `x ∈ [a,b]` such that the model with its `p`-th coefficient
  rescaled by `x²` satisfies the Ghirlanda–Guerra identity at `φ(r) = rᵖ` up to

  `‖g‖ N (√((b-a)·2(|a|+|b|)aₚ/N) + 4δ(|a|+|b|+2δ)aₚ`
  `      + 3(b-a)√(N(ξ(1)-aₚ) + (|a|+|b|+δ)²aₚN)/(δN)) / ((b-a) n x aₚ N)`,

  i.e. `O(N^{-1/4})` at `δ = N^{-1/4}`. The statement is about the canonical field
  `gaussField N (overlapCovMatrix N ξₓ)` shifted by the external field — no coupling space, no
  perturbation, no unproved hypothesis, at every finite volume.

## Proved: the extended Ghirlanda–Guerra identities at finite volume (Vol. II, Theorem 12.2.2)

Talagrand perturbs a Hamiltonian by a family of independent Gaussian components `∑ₛ βₛ Hₛ` and
isolates one at a time: for each `s` the pair `(∑_{i≠s} βᵢHᵢ, Hₛ)` is an independent pair to which
Theorem 12.1.1 applies, and Fubini over the couplings produces one coupling vector good for every
component. All of it is now formal, with the couplings *exhibited* rather than averaged over.

- `ProbabilityTheory.multivariateGaussian_zero` — `multivariateGaussian m 0 = dirac m`.
- `ProbabilityTheory.multivariateGaussian_map_sum_smul_pi` — **a linear combination of independent
  centered multivariate Gaussians is the centered multivariate Gaussian with the combined
  covariance**: `∑ᵢ cᵢ xᵢ ∼ mvG 0 (∑ᵢ cᵢ² Sᵢ)` under `Measure.pi` (a Mathlib gap; the two-summand
  `multivariateGaussian_map_add_prod` is its induction step).
- `Fin.insertNth_eq_update` — inserting at `p` is updating the `p`-th coordinate (a Mathlib gap).
- `SpinGlass.FiniteGibbs.continuous_integral_totalFluct_param` (and the chain
  `measurable_gibbs_average_param`, `abs_integral_gibbs_average_param_le`,
  `continuous_integral_gibbs_average_param`, `continuous_integral_abs_meanEnergy_sub_param`,
  `integrable_totalFluct_param`) — **the energy-fluctuation functionals are continuous in a
  parameter of the Hamiltonian ranging over any first-countable space**; the affine-path statements
  are now the case `E = ℝ`.
- `SpinGlass.GaussianDisorder.ofMap` — a measurable Hamiltonian whose law is `gaussField N S` is a
  Gaussian disorder with kernel `S`.
- `SpinGlass.familyLaw`, `familyLaw_map_eval`, `familyLaw_map_sum_smul`,
  `familyLaw_map_sum_erase_smul`, `iIndepFun_eval_familyLaw`, `indepFun_sum_erase_eval`,
  `familyCoord`, `familyRest`, `indepFun_familyRest_familyCoord` — **the canonical carrier of a
  finite family of independent Gaussian disorders** (the product of the canonical fields), its
  coordinates, their combinations, and the independent pair `(∑_{i≠s} cᵢ ωᵢ, ωₛ)` as
  `GaussianDisorder`s.
- `SpinGlass.familyHam`, `familyHam_update_eq`, `sum_erase_sq_smul_add` — the perturbed
  Hamiltonian `c₀ + H₀ + ∑ₛ βₛ Hₛ` (Talagrand's (12.33)) and its pair decomposition at each `s`.
- `SpinGlass.familyFluct`, `continuous_familyFluct`, `familyFluct_update_eq` — **the fluctuation
  functional `𝔼⟨|Hₛ/N − 𝔼⟨Hₛ/N⟩|⟩` of component `s`** as a continuous function of the couplings.
- `SpinGlass.energyFluctuationBound` — Theorem 12.1.1's explicit three-term bound, named.
- `SpinGlass.integral_disorderPairLaw_totalFluct` — the pair-space fluctuation integrand pulled
  back to the sample space.
- `SpinGlass.intervalIntegral_familyFluct_update_le` — **Theorem 12.1.1 for one component of a
  family**, uniformly in the other couplings.
- `SpinGlass.abs_ghirlandaGuerra_defect_family_le` — **the (15.40) defect of the perturbed model
  at the profile of component `s` is at most `‖g‖ N 𝔼⟨|Hₛ/N − 𝔼⟨Hₛ/N⟩|⟩/(k |βₛ κₛ|)`**, for the
  canonical law `gaussField N (T 0 + ∑ₛ βₛ² Tₛ)` shifted by the external field.
- `SpinGlass.setIntegral_familyFluct_le` — **Fubini over the box** `[a,b]^{m+1}`
  (`measurePreserving_piFinSuccAbove`, `integral_prod_symm`, `Measure.restrict_pi_pi`).
- `SpinGlass.exists_couplings_familyFluct_le` — **one coupling vector good for every component**,
  by the mean value principle `MeasureTheory.exists_le_setAverage`.
- `SpinGlass.exists_couplings_abs_ghirlandaGuerra_defect_family_le` — **Theorem 12.2.2 at finite
  volume**: for a family of overlap-driven components `Tₛ = κₛ φₛ(R)` and `[a,b] ⊂ (0,∞)`, couplings
  `β ∈ [a,b]^{m+1}` at which the perturbed model satisfies the Ghirlanda–Guerra identity at every
  `φₛ` simultaneously, for every test function, up to `‖g‖ N (∑ₚ εₚ)/((b-a) k |βₛ κₛ|)`.
- `SpinGlass.monomialPerturbationKernel`, `monomialPerturbationKernel_zero_add_sum`,
  `exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le` — **the mixed `p`-spin
  instance**: perturbing by `wₛ² N Rˢ⁺¹`, `s = 0, …, m`, the perturbed model is the mixed `p`-spin
  model with profile `ξ(r) + ∑ₛ (βₛwₛ)² rˢ⁺¹`, and at the exhibited couplings it satisfies the
  identities at **all monomials `r, …, rᵐ⁺¹` at once**, with the explicit rate. With
  `wₛ = c_N 2^{-(s+1)}`, `δ = N^{-1/4}` this is Talagrand's `O(N^{-1/4} c_N^{-2})`.

Talagrand's statement takes `β ∈ [-1,1]^ℕ` (infinitely many components) and bounds the defect on
average. Here the family is finite (`m+1` components, `m` arbitrary), the window `[a,b] ⊂ (0,∞)`
avoids the singularity at `βₛ = 0`, and the good couplings are exhibited — which is exactly what
the passage to the limit consumes.

## Proved: the Ghirlanda–Guerra identities in the thermodynamic limit (Vol. II, §12.2 → §15.3)

The finite-volume extended identities hold up to a defect; in the limit they hold exactly. The
passage is formal and the capstone is fully explicit.

- `SpinGlass.ggDefect ν n φ g` — **the defect in Talagrand's (15.40)** for a law `ν` of overlap
  arrays; `continuous_ggDefect` (it is continuous in the law, in the topology of convergence in
  distribution); `satisfiesGhirlandaGuerra_iff_ggDefect` (the identities are its vanishing at every
  block observable); `ggDefect_monomial_zero` (it vanishes identically at `φ = 1`).
- `SpinGlass.satisfiesGhirlandaGuerra_of_tendsto_ggDefect` — **approximate identities pass to the
  limit**: if the defects at every monomial tend to `0` along a convergent family of laws, the limit
  satisfies the identities at every continuous test function.
- `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra` — for a sequence of jointly
  exchangeable Gram array laws with vanishing monomial defects, some subsequence converges to a
  jointly exchangeable Gram law satisfying the Ghirlanda–Guerra identities.
- `SpinGlass.mixedPSpinArrayLaw N ξ h` — **the annealed overlap-array law of the mixed `p`-spin
  model** with profile `ξ` and field `h`; `isJointlyExchangeable_mixedPSpinArrayLaw`,
  `mixedPSpinArrayLaw_gramArray`; `perturbedProfile ξ w` — the profile `ξ(r) + ∑ₛ wₛ² rˢ⁺¹`.
- `SpinGlass.tendsto_perturbation_rate` — the finite-volume rate, normalised by the kernel scale,
  vanishes under the scaling hypotheses `c_N → 0`, `δ_N → 0`, `(m_N+1)δ_N → 0`,
  `(m_N+1)c_N² → 0`, `(m_N+1)/(c_N²δ_N√N) → 0`.
- `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin` — **the capstone of
  §12.2**: for every mixed `p`-spin model and every admissible scaling, there are couplings
  `β_N ∈ [a,b]^{m_N+1}` such that along a subsequence the annealed overlap-array laws of the
  perturbed models (profile `ξ(r) + ∑ₛ (β_{N,s}c_N)² rˢ⁺¹`, perturbation variance per site
  `≤ b²(m_N+1)c_N² → 0`) converge in distribution to a jointly exchangeable Gram law that
  **satisfies the Ghirlanda–Guerra identities**.
- `SpinGlass.tendsto_floor_rpow_mul_rpow_neg`, `explicitScaling_tendsto`,
  `exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin_explicit` — the same with the
  **explicit scaling** `c_N = N^{-1/16}`, `δ_N = N^{-1/4}`, `m_N = ⌊N^{1/16}⌋`: no free parameter
  remains.

## Proved: the free energy under an independent Gaussian perturbation (Vol. II, Lemma 12.2.1)

- `SpinGlass.integral_exp_mul_apply_gaussField` — **the exponential moment of a coordinate of a
  Gaussian field**: `𝔼 exp(t H(σ)) = exp(T σ σ t²/2)`, through Mathlib's one-dimensional marginal
  `IsGaussian.map_eq_gaussianReal` and `mgf_gaussianReal`; `integrable_exp_mul_apply_gaussField`.
- `SpinGlass.le_integral_free_energy_density_add` — Jensen for the convex free energy: an
  independent centered perturbation cannot lower the mean free energy.
- `SpinGlass.integral_free_energy_density_add_le` — Jensen for the logarithm (through the tangent
  line at the mean partition function) and the Gaussian exponential moment: a perturbation of
  variance at most `D` per configuration raises the free energy per site by at most `D/(2N)`.
- `SpinGlass.gaussFreeEnergy_le_gaussFreeEnergy_add`, `SpinGlass.gaussFreeEnergy_add_le` —
  **Lemma 12.2.1**: `gaussFreeEnergy N S h ≤ gaussFreeEnergy N (S + T) h ≤ gaussFreeEnergy N S h
  + D/(2N)`, for the law of the sum of independent fields (`multivariateGaussian_map_add_prod`) and
  Fubini.
- `SpinGlass.abs_gaussFreeEnergy_perturbedProfile_sub_le` — for a mixed `p`-spin model perturbed by
  the monomial components with weights `w`, **the free energy moves by at most `(∑ₛ wₛ²)/2`**; with
  the couplings of the Ghirlanda–Guerra capstone this is `≤ b²(m_N+1)c_N²/2 → 0`: the perturbation
  that produces the identities is invisible to the free energy in the limit.

## Proved: Talagrand's positivity principle (Vol. II, §12.3)

"If a system satisfies the extended Ghirlanda–Guerra identities, the overlap `R_{1,2}` is 
  essentially
nonnegative" — Theorem 12.3.1, with both halves of Talagrand's proof.

- `SpinGlass.ggDefect_sub`, `ggDefect_smul`, `ggDefect_finsetSum`, `abs_ggDefect_le` — the defect
  is linear in the test function and bounded by `2‖φ‖‖g‖`.
- `SpinGlass.TendstoGGDefectUniform` — **Talagrand's Definition 15.4.1**: the extended identities
  hold asymptotically, uniformly over the observables of the first `n` replicas.
- `SpinGlass.tendstoGGDefectUniform_of_monomial` — monomial test functions suffice, uniformly
  (Stone–Weierstrass plus linearity of the defect).
- `SpinGlass.sum_sum_mul_mul_overlap_nonneg` — Gram positivity for weighted configurations,
  `∑ p σ p τ R(σ,τ) = (1/N) ∑ᵢ (∑ p σ σᵢ)² ≥ 0`.
- `SpinGlass.sum_filter_le_of_overlap` (Lemma 12.3.3), `sum_mul_negMass_pow_le` (**Proposition
  12.3.2** for a probability vector: `∑ p σ (negMass p ε σ)^m ≤ (4 log(m+1) + 1)/(ε(m+1))`).
- `SpinGlass.negSet`, `overlapArrayLaw_negSet_eq`, `bind_overlapArrayLaw_real_negSet_le` —
  Proposition 12.3.2 for the annealed overlap-array law of any random Hamiltonian, through the exact
  product formula for the mass of Talagrand's `D_n` under the finite-volume replica measure.
- `SpinGlass.rampCM`, `negRamp`, `negObs` — the continuous ramps and the observables
  `G_j = ∏ ψ_l(R_{0,l})`; `negObs_le_indicator_negSet`, `negRamp_mul_negObs` (absorption).
- `SpinGlass.negObsInt_succ_ge` (the recursion `I_{j+1} ≥ ((j+a)/(j+1)) I_j − |defect|`, from the
  identity, exchangeability and absorption), `negMassLaw_mul_negProd_sub_le` (its iteration),
  `negObsInt_le_real_negSet` — **Proposition 12.3.4**.
- `SpinGlass.exp_neg_sub_le_one_sub`, `sum_Ico_inv_succ_le_log`, `sum_Ico_inv_succ_sq_le`,
  `negProd_ge` (`P_k(a) ≥ e⁻² k^{a-1}`), `exists_good_k` — the elementary estimates.
- `SpinGlass.tendsto_negMassLaw` — **Theorem 12.3.1**: for jointly exchangeable array laws with the
  extended identities asymptotically and the bound of Proposition 12.3.2, `μ_N{R_{0,1} ≤ −2ε} → 0`.
- `SpinGlass.tendsto_real_negLevel_bind` — Theorem 12.3.1 for the annealed overlap-array laws of
  Gibbs measures, at every level `−ε'`; `measure_negOverlap_eq_zero_of_tendsto` — any
  distributional limit gives no mass to `{R_{0,1} < 0}` (Portmanteau, open sets).
- `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin` now also delivers the
  **uniform** extended identities (`TendstoGGDefectUniform`) along the perturbed sequence, and
  `exists_subseq_tendsto_satisfiesGhirlandaGuerra_nonnegOverlap_mixedPSpin` — **the capstone with
  positivity**: the limit law is jointly exchangeable, Gram, satisfies the Ghirlanda–Guerra
  identities, and has nonnegative overlaps almost surely.

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
- `GaussianDisorder.map_U_eq_multivariateGaussian` (now with **no positivity hypothesis**: the
  covariance matrix of a Gaussian law is positive semidefinite by
  `ProbabilityTheory.posSemidef_covMatrix`) and
  `GaussianDisorder.map_U_eq` — two Gaussian Hamiltonians with the same covariance kernel, carried
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

## Proved: the thermodynamic limit of convex mixed `p`-spin models (Vol. I Thm. 1.3.9)

`MixedPSpinThermodynamicLimit`. Guerra–Toninelli superadditivity is proved for an arbitrary pair of
kernels, `mul_integral_free_energy_density_add_le_of_kernel_le`: whenever the kernel of the whole
system is dominated by the non-interacting split kernel and agrees with it on the diagonal, the
Guerra trace of the splitting interpolation is nonpositive
(`guerraTrace_splitCovKernel_nonpos_of_le`) and `N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁+N₂) p_{N₁+N₂}`. For an
overlap-driven kernel `N ξ(R)` the domination is Jensen's inequality for a profile `ξ` convex on
`[-1,1]` (`overlapCovKernel_le_splitCovKernel`);
the SK model is the corollary `ξ(r) = β² r²/2` (`convexOn_skCovXi`), replacing the earlier ad hoc
Sedrakyan argument.

- `mixedPSpinFreeEnergy N ξ h = gaussFreeEnergy N (overlapCovMatrix N ξ) h`, with
  `skFreeEnergy_eq_mixedPSpinFreeEnergy` by `rfl`.
- `mul_mixedPSpinFreeEnergy_add_le` — Guerra–Toninelli for every convex profile whose kernel is a
  covariance; `mixedPSpinFreeEnergy_le` — the annealed bound `p_N ≤ log 2 + |h| + ξ(1)/2`.
- `mixedPSpinFreeEnergyLimit`, `tendsto_mixedPSpinFreeEnergy`, `mixedPSpinFreeEnergy_le_limit` —
  Fekete: the limit exists and is the supremum.
- `convexOn_eval_of_even_coeff`, `tendsto_mixedPSpinFreeEnergy_of_polynomial` — every even mixed
  `p`-spin model (nonnegative coefficients on even powers) has a thermodynamic limit.
- `tendsto_mixedPSpinFreeEnergy_perturbedProfile`,
  `tendsto_mixedPSpinFreeEnergy_perturbedProfile_explicit` — Lemma 12.2.1 in the limit: the
  Ghirlanda–Guerra perturbation of the capstone does not change the free energy limit.

## Proved: Ghirlanda–Guerra at almost every temperature (Vol. II Thm. 12.1.3, 12.1.10)

`FiniteGibbs/PointwiseFluctuation` is Panchenko's Theorem 12.1.3 in the general finite-Gibbs
setting `U + x • V`. The two-replica fluctuation `ψ(x) = 𝔼⟨|V(σ¹) - V(σ²)|⟩/n` (`pairAverage`,
`pairDeriv`) is differentiable with `|ψ'| ≤ 4p''` (`hasDerivAt_pairFluct`,
`abs_integral_pairDeriv_le`, Lemma 12.1.7); `ψ ∓ 4p'` are therefore monotone
(`pairFluct_le_pairFluct_add`), a point of the window has `p'' ≤ D(x,b)/2b`
(`exists_integral_hessian_le_window`), and Lemma 12.1.8 follows (`pairFluct_le_window`). Griffiths'
lemma in mean bounds the disorder part at the fixed parameter
(`integral_abs_gibbs_average_sub_le_window`), and `integral_totalFluct_le_window` is the
finite-volume form of Theorem 12.1.3; `tendsto_zero_of_le_window` is the passage "first `N → ∞`,
then `b → 0`".
`ConvexOn.exists_eventually_deriv_sub_deriv_le` (Common, GriffithsLemma) is Lemma 12.1.9.

`MixedPSpinDifferentiability` instantiates it for every even mixed `p`-spin model with external
field along the temperature path `β ↦ H_field + β H`: `mixedPSpinPathFreeEnergy`, its convex limit
`mixedPSpinPathLimit` (Guerra–Toninelli), `tendsto_mixedPSpinTotalFluct_of_differentiableAt`
(**Theorem 12.1.3**) and `ae_tendsto_mixedPSpinTotalFluct`; then, via the disorder-pair route with
the zero disorder in the first slot (`GaussianDisorder.zero`, `abs_ggDefect_mixedPSpin_le`),
`tendsto_ggDefect_mixedPSpin_of_differentiableAt` and `ae_tendsto_ggDefect_mixedPSpin`
(**Theorem 12.1.10, second half**): the Ghirlanda–Guerra defect of the model's own profile vanishes
at every `β ≠ 0` where `𝒫` is differentiable, hence at almost every `β`, and every subsequential
limit law satisfies the identity (15.40) for `ξ` (`ggDefect_eq_zero_of_tendsto_mixedPSpin`).

## Proved: Poisson point processes, Poisson–Dirichlet identities, cascades (Vol. II §13.1, §14.2)

Mathlib has no Poisson point process. `Common/Mathlib/Probability/PointProcess` builds the theory
Mathlib-first. `PoissonFinite`: a finite-intensity process is a `Poisson (ν E)` number of i.i.d.
positions, recorded as the `Measure`-valued random variable `countingMeasure`
(`measurable_countingMeasure`); its **Laplace functional** `𝔼 e^{-∫φ dN} = e^{-∫(1-e^{-φ}) dν}`
(`integral_negExp_countingMeasure`, with `ENNReal.negExp` handling `φ = ∞`) is Fubini on the
sample space plus the Poisson series. `PoissonSuperposition`: countably many independent finite
pieces on `Measure.infinitePi` give the process of **any s-finite intensity**, through Mathlib's
canonical decomposition `sfiniteSeq`: `poissonPointProcess (Λ) [SFinite Λ]` is a probability
measure on `Measure E`, with the Laplace functional (`integral_negExp_lintegral_poissonPointProcess`,
by dominated convergence) and the **void probabilities** `P(N B = 0) = e^{-Λ B}`
(`measureReal_poissonPointProcess_eq_zero`), both transported to any random measure with this law
(`HasLaw.integral_negExp_lintegral`, `HasLaw.measureReal_eq_zero`), and all of it stated as well
for the superposition of *any* decomposition into finite pieces (`…poissonPointProcessSum`,
`HasLaw.integral_negExp_lintegral_sum`, `HasLaw.lintegral_lintegral_sum`), since Mathlib's
`sfiniteSeq` is opaque and a construction that needs the structure of the pieces must choose them
itself. `StableIntensity`:
Talagrand's `μ_m` with density `u^{-m-1}` on `(0,∞)` (s-finite, of infinite mass), the
**scaling identity** `∫(1-e^{-au})u^{-m-1} du = a^m c_m` with `0 < c_m < ∞`
(`integral_one_sub_exp_mul_rpow`, Lemma 13.1.1 in Laplace form), the moment integral
`∫(1-e^{-a u^m})u^{-m'-1} du = a^{m'/m} c_{m'/m}/m` (`integral_one_sub_exp_mul_rpow_rpow`), and
`μ_m(c,∞) = c^{-m}/m`, and the **explicit decomposition** `μ_m = ∑ₙ μ_m|_{(1/(n+2),1/(n+1)] ∪ (n+1,n+2]}`
into nonzero finite pieces for every `m` (`stableSeq`, `sum_stableSeq`). `PoissonDirichlet`: the
marked process `(u_α, g_α)` with intensity `μ_m ⊗ η` (`pdProcess`, a measure on
`Measure (ℝ × M)`), built as the superposition of the **product** pieces `(stableSeq m n) ⊗ η`
(`pdSeq`) so that the marks are i.i.d. and independent of the weights by construction, the weighted sums
`S_v = ∑ u_α v(g_α)` for `ℝ≥0∞`-valued weights (`pdSum`), their **Laplace transform**
`𝔼 e^{-sS_v} = exp(-s^m c_m ∫v^m dη)` (`integral_negExp_pdSum`, unconditional in `ℝ≥0∞`), the
**moments** `𝔼 S_v^{m'} = (c_m ∫v^m dη)^{m'/m} c_{m'/m}/(m c_{m'})` for `0 < m' < m`
(`lintegral_pdSum_rpow`, which contains (13.8) and (13.9)), a.s. finiteness and positivity, the
tails `P(S_v > t) ≤ C t^{-m}` and `P(S_v < t) ≤ e^{-C t^{-m}}`, hence `𝔼|log S_v| < ∞`
(`integrable_log_pdSum`, from the general `integrable_log_toReal_of_tails`); and, through
Frullani's integral (`Common/Mathlib/Analysis/SpecialFunctions/FrullaniExp`:
`log x = ∫(e^{-s}-e^{-xs})/s ds` and `𝔼 log S = ∫(e^{-s} - 𝔼e^{-sS})/s ds`),
**Talagrand's identity (13.10)** `𝔼 log ∑u_α v(g_α) = 𝔼 log ∑u_α + (1/m) log ∫v^m dη`
(`integral_log_pdSum_eq`) and **Theorem 13.1.5** `𝔼 log ∑ v_α V_α = (1/m) log 𝔼V^m` for the
Poisson–Dirichlet weights (`integral_log_pdSum_div_eq`), all in `HasLaw` form as well.

`Cascade`: the **Poisson–Dirichlet cascades** of Vol. II §14.2, by recursion on the number of
levels — a `(k+1)`-level cascade is the Poisson–Dirichlet process of parameter `m₁` whose marks are
`(z₁, k-level cascade)` (`CascadeSpace`, `cascadeLaw`, `hasLaw_superCounting_cascadeLaw`). The
cascade sums `∑_α u*_α G(z_{1,α}, …, z_{k,α})` (`cascadeSum`, jointly measurable) and Talagrand's
recursion (14.5) in `ℝ≥0∞` (`cascadeRec`) and in his real form `F_p = (1/m_p) log 𝔼_p exp(m_p
F_{p+1})` (`parisiRec`, `parisiRec_succ`). **Proposition 14.2.2** (`lintegral_cascadeSum_rpow`):
for `0 < m₀ < m₁ < ⋯ < m_k < 1`, `𝔼 (∑_α u*_α G(α))^{m₀} = cascadeRec^{m₀} · C(m₀, …, m_k)` with
an explicit constant, unconditionally in `ℝ≥0∞`. **Theorem 14.2.1**
(`integral_log_cascadeSum_div_eq`, `integral_log_cascadeSum_exp_div_eq`): `𝔼 log ∑_α v_α exp
F(α) = F₁` for the cascade weights `v_α = u*_α/∑ u*_γ`, from (13.10) at the top level and the
moments of the sub-cascade, under the single hypothesis `cascadeRec < ∞` — implied by Talagrand's
(14.4) `𝔼 exp F < ∞` through Jensen (`cascadeRec_le_lintegral_pi`), with no need for
`𝔼|F| < ∞` nor for the limit `m₀ → 0` of Lemma 14.2.3.

`Mecke`: **the Mecke formula** `𝔼 ∑_{x ∈ N} f(x, N) = ∫ 𝔼 f(x, N + δ_x) dΛ(x)` for the Poisson
process of any s-finite intensity (`lintegral_lintegral_poissonPointProcess`, `HasLaw` form
`HasLaw.lintegral_lintegral`, Campbell's formula as the special case), proved from the structure
of the sample space: resampling one coordinate of an infinite product leaves it invariant
(`Measure.infinitePi_prod_map_update`, `lintegral_infinitePi_update`, new for Mathlib), an i.i.d.
product is exchangeable (`lintegral_infinitePi_comp_equiv`), and `(n+1) P(n+1) = Λ(E) P(n)` for
the Poisson weights. `PoissonDirichletIdentities`: **Theorem 13.1.6** — the identities (13.13)
`𝔼 (∑ u_α U_α)/(∑ u_α V_α) = 𝔼[U V^{m-1}]/𝔼 V^m` (`lintegral_pdSum_mul_inv_pdSum`, real form
`integral_pdSum_div_pdSum`), (13.14) `𝔼 (∑ u_α² U_α W_α)/(∑ u_α V_α)² = (1-m) 𝔼[U W V^{m-2}]/𝔼 V^m`
(`lintegral_pdSumSq_mul_inv_pdSum_sq`) and (13.17) `𝔼 ∑ v_α² = 1 - m`
(`lintegral_pdSumSq_mul_inv_pdSum_one_sq`). Talagrand differentiates Theorem 13.1.5 and calls the
justification "tedious"; here they are direct consequences of the Mecke formula, the Laplace
representations `x⁻¹ = ∫₀^∞ e^{-sx} ds`, `x⁻² = ∫₀^∞ s e^{-sx} ds` valid in all of `ℝ≥0∞`
(`ENNReal.inv_eq_lintegral_negExp`), the Gamma integrals, and `m c_m = Γ(1 - m)`
(`mul_stableConst_eq_Gamma`, by integration by parts on `(0, ∞)`). The same route gives (13.14)
with a general exponent, `𝔼 (∑ u_α² A_α)(∑ u_α V_α)^{a-2} = K₂(a) ∫ A V^{m-2} dη` for `a < m`
(`lintegral_pdSumSq_mul_rpow_pdSum`), with `K₂(a) κ = (1-m)/(1-a) · 𝔼 S_V^a`.

`CascadeIdentities`: **Proposition 14.3.3** (Vol. II (14.38)), the fundamental identity of the
cascade Gibbs average `𝔼⟨1_{(α,γ)=r}⟩ = m_r - m_{r-1}` for every weight `exp F`
(`lintegral_cascadePairIndicator`), in the equivalent cumulative form `𝔼⟨1_{α|r = γ|r}⟩ = 1 - m_r`
(`lintegral_cascadeSq_mul_inv_sq`). Talagrand differentiates Theorem 14.2.1 twice and skips the
justification; here `⟨1_{α|r=γ|r}⟩ = Q_r/S²` with `Q_r` the sum over the prefixes of length `r` of
the squared partial sums (`cascadeSq`, built by the cascade recursion), and the mixed moments
`𝔼 Q_r S^{a-2} = (1-m_r)/(1-a) · 𝔼 S^a` (`lintegral_cascadeSq_mul_rpow`) follow by induction on
the levels from the general-exponent (13.14) and Proposition 14.2.2, with no differentiation.

`FiniteGibbs/GaussianInterpolation`: **Guerra's interpolation on an arbitrary finite state
space** — for independent centered Gaussian fields `U, V` with kernels `K₁, K₂` and any fixed
vector `c`, `φ(t) = 𝔼 F_n(√t U + √(1-t) V + c)` is continuous on `[0,1]`, differentiable on
`(0,1)` with derivative the averaged **Guerra trace** `(1/2)∑(K₁-K₂)(x,y) D²F_n(H_t)(e_y,e_x)`
in Gibbs form (`hasDerivAt_guerraPhi`, `guerraTrace_eq`), and `φ(1) ≤ φ(0) + C` from
`φ' ≤ C` (`integral_free_energy_density_le`). This is the form of Lemma 14.4.1 that the broken
replica-symmetry bound needs (state space `Σ_N × branches`, `c` carrying the field and the cascade
weights); it is a direct instance of the Hilbert-space interpolation identity in
`Common/Mathlib/Probability/Distributions/Gaussian_Interpolation`. The comparison bound also holds
with a `t`-dependent bound on the derivative, `φ(1) - φ(0) ≤ ∫₀¹ b(t) dt` for `b` interval
integrable (`guerraPhi_one_sub_zero_le`, by the fundamental theorem of calculus: the averaged
trace is continuous in `t`, `continuous_integral_guerraTrace`). `FiniteGibbs/GaussianFieldPullback`:
a Gaussian field pulls back along any map `f` of finite state spaces to a field with kernel
`K (f x) (f y)` (`GaussianField.comp`, through the adjoint of the pullback of Hamiltonians) — the
lift of the model's Hamiltonian to `Σ_N × branches`, and the restriction of a field to a subset.
`FiniteGibbs/WeightedInterpolation`: **Guerra's comparison bound for a weighted free energy**
`(1/n) log ∑_x w_x e^{-H x}`, `w ≥ 0` not all zero, with the derivative controlled by the
**weighted Guerra trace** in Gibbs form (`wFreeEnergy_sub_le`) — the weighted free energy is the
free energy of `H - log w` on the support of `w`, to which the fields are restricted. This is
Lemma 14.4.1 for the weights `w_α` of a finite family of branches, zero weights allowed: the form
needed for a truncated Poisson–Dirichlet cascade, some of whose branches do not exist.

`Parisi/TreeTrace`: on `Σ_N × A`, the weighted Guerra trace of the model kernel `N ξ(R_{στ})`
against a **tree kernel** `N R_{στ} ξ'(q_{α,γ})` with `q_{α,α} = q̄` (Talagrand's (14.63)) is
exactly `(1/2)(ξ(1) - ξ'(q̄)) - (1/2)⟨ξ(R) - R ξ'(q_{α,γ})⟩` (`wGuerraTrace_tree_eq`, (14.68)),
and when `ξ` lies above its tangents — convexity, (14.61) — at most
`(1/2)(ξ(1) - ξ'(q̄)) + (1/2)⟨θ(q_{α,γ})⟩` (`wGuerraTrace_tree_le`, (14.79)).

`FiniteGibbs/GaussianFieldProd`: a Gaussian field transports along any map of probability spaces
(`GaussianField.compMeasurable`), two fields on `P` and `Q` live on `P ⊗ Q` through the
projections and are independent there (`prodLeft`, `prodRight`, `prodLeft_indepFun_prodRight`),
and every positive semidefinite matrix is the kernel of the canonical field `id` under `N(0, S)`
(`GaussianField.ofMultivariateGaussian`) — the model field of a mixed `p`-spin Hamiltonian.

`Parisi/TreeFieldLaw`, `Parisi/TreeField`: **the Gaussian field of the marks** of a truncated
cascade, Talagrand's `H(σ, α) = ∑ᵢ σᵢ ∑_{0 ≤ p ≤ k} z_{i,p,α}` of (14.73). The coordinates the
truncated tree sees — the level-`0` vector and the marks of the truncated nodes, site by site — are
independent real Gaussians (`treeCoords_law`, from `cascadeMarksLaw_map_truncMarks`, the
flattening `infinitePi_map_curry` and `measurePreserving_sumPiEquivProdPi`), the field is their
linear image `treeLin` with adjoint `L† e_x = A x` on Dirac vectors, and `treeField` is a
`GaussianField` on `Σ_N × A` with kernel `(∑ᵢ σᵢ τᵢ) · treeCov α γ`,
`treeCov α γ = v₀ + ∑_{p : α|_{p+1} = γ|_{p+1}} v_p` (`sum_coordVar_treeCoeff`) — Talagrand's
(14.74), `R_{1,2} ∑_{p < (α,γ)} 𝔼 z_p²`, which telescopes to `R_{1,2} ξ'(q_{(α,γ)})` for the
variances (14.72): `Parisi/TreeCov` — the agreeing levels of two branches form an initial segment
(`branchNode_eq_iff_lt_branchLevel`, of length `branchLevel α γ = (α,γ) - 1`), the tree
covariance telescopes to `ξ'(q_{(α,γ)}) - ξ'(q₀)` for the Parisi variances when `ξ'` is
nondecreasing (`treeCov_eq_deriv`), and so **the kernel of the marks field is the tree kernel**
`N R_{στ} ξ'(q_{(α,γ)})` of (14.63) when `ξ'(0) = 0` (`treeFieldKernel_eq_treeKernel`).

`Parisi/GuerraRSB`: **Guerra's interpolation for the truncated tree at fixed weights**
(Lemma 14.4.1 with (14.79) and (14.80), integrated in `t`): on the product of the model law
`N(0, N ξ(R))` with the marks law, with the lifted model Hamiltonian and the marks field as the two
independent fields and the branch weights `u*_α` as weights, `wFreeEnergy_sub_le` gives
`p_N ≤ 𝔼 (1/N) log ∑_α u*_α ∏ᵢ 2cosh(h + z₀ᵢ + ∑ₚ z_{i,p,α}) − (1/N) log ∑_α u*_α + ∫₀¹ b(t) dt`
with `b(t) = 𝔼[(1/2)(ξ(1) − ξ'(q_{k+1})) + (1/2)⟨θ(q_{(α,γ)})⟩_t]` (`guerra_truncated`). The two
endpoints are the factorization of the weighted partition function of the lifted Hamiltonian off
the total weight (`wZ_pullback_fst`) and the Ising site factorization
`∑_σ e^{∑ᵢ σᵢ aᵢ} = ∏ᵢ 2cosh aᵢ` of the marks field (`wZ_ising`, from `treeLin_treeCoords_apply`),
and the bound is continuous in `t`, hence interval integrable. The hypotheses on `ξ` are those of
Talagrand: `ξ'(0) = 0`, `ξ'` nondecreasing along the `q`'s, `ξ` above its tangents on `[-1,1]`
(convexity), and the kernel `N ξ(R)` positive semidefinite.

`Common/Mathlib/Probability/Distributions/Gaussian/PiGaussian`: **a product of real Gaussians is
a multivariate Gaussian with diagonal covariance**, `(⊗ᵢ N(mᵢ, vᵢ)).map toLp =
multivariateGaussian m (diagonal v)` (`map_pi_gaussianReal_eq_multivariateGaussian`, by
characteristic functions), hence a Gaussian measure with covariance operator `diagonal v`
(`inner_covarianceOperator_map_pi_gaussianReal`) — the law of the marks of a finite set of nodes
of a cascade with Gaussian levels.

`Common/Mathlib/Probability/ProductMeasureProd` and `Marking`: **zipping independent families** —
a family of independent pairs `(xᵢ, yᵢ) ∼ μᵢ ⊗ νᵢ` is a pair of independent families,
`⊗ᵢ (μᵢ ⊗ νᵢ) = ((⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)).map zip` (`Measure.infinitePi_prod_eq_map`, for
`Measure.infinitePi` and `Measure.pi`, new for Mathlib), proved on cylinders from the `ℝ≥0∞` Fubini
`lintegral_fintype_prod_eq_prod`; hence **the marking representation**: the position law of a
product piece is a product (`positionLaw_prod`), the sample of a finite Poisson process with
intensity `ν ⊗ η` is the sample with intensity `ν` zipped with i.i.d. marks
(`poissonSampleLaw_prod`), the same for the superposition (`superSampleLaw_prod`), and so
`pdSampleLaw m η = ((pdWeightsLaw m) ⊗ (i.i.d. marks)).map superZip` (`pdSampleLaw_eq_map`):
the weights and the marks of the Poisson–Dirichlet process are independent, as an identity between
measures on the sample space. This is the conditioning on the weights that Guerra's broken
replica-symmetry bound requires.

`CascadeUnzip`: **a cascade is its weights zipped with its marks, and they are independent** —
`cascadeLaw k ms μs = ((cascadeWeightsLaw k ms) ⊗ (cascadeMarksLaw k μs)).map (cascadeZip k)`
(`cascadeLaw_eq_map_cascadeZip`), where the weights `CascadeWeights k` are the unmarked
Poisson–Dirichlet samples of every node of the tree and the marks `CascadeMarks T k` an i.i.d.
array of marks of every node; proved by unzipping every level with the marking representation and
the two-level zip `Measure.infinitePi_infinitePi_prod_eq_map`. `CascadeBranches`: in these
coordinates a **branch** is an address `α : Fin k → ℕ × ℕ`, Talagrand's `u*_α` and
`(z_{1,α}, …, z_{k,α})` are the explicit `branchWeight` (zero for a non-existing branch) and
`branchMarks`, and the cascade sums are genuine sums over branches: `∑_α u*_α G(z_α)` as a `tsum`
(`cascadeSum_cascadeZip`) and the prefix-squares `Q_r = ∑_{α|r = γ|r} u*_α u*_γ G(z_α) G(z_γ)`
(`cascadeSq_cascadeZip`, with the indicator `prefixEq`). This is the form of the cascade Gibbs
averages that a finite truncation of the tree approximates. `CascadeNodeMarks`: **the marks of
the nodes of a cascade form an infinite product** — under `cascadeMarksLaw k μs` the family of all
node marks `(z_{p+1,u})_{⟨p,u⟩}` has law `⊗_{⟨p,u⟩} μs p` (`cascadeMarksLaw_map_nodeMarks`), so
the marks of any finite set of nodes are independent with the laws of their levels; proved by
flattening the nested products with Mathlib's `infinitePi_map_curry`, the new
`Measure.infinitePi_sum_eq_map` (an infinite product over a sum type is a product of infinite
products) and a reindexing of the nodes. The marks along a branch are the node marks at its
prefixes (`branchMarks_eq_nodeMark`): for Gaussian levels this is Talagrand's family
`(z_{i,p,α})` of (14.72)–(14.74). `CascadeTrunc`: the tree truncated to indices `< M` has finitely
many nodes (`TruncNode`), and their marks are independent with the laws of their levels — a finite
`Measure.pi` (`cascadeMarksLaw_map_truncMarks`), by restriction of the infinite product.

`CascadeProduct`: the structure of the recursion that computes `φ(0)` in §14.4 — **homogeneity**
`cascadeRec (C·G) = C · cascadeRec G` (`cascadeRec_const_mul`), **site factorization** (Talagrand's
(14.82)): over product marks and a product function the recursion is the product of the one-site
recursions, `F₁ = ∑_i F_{1,i}` (`cascadeRec_pi`, `parisiRec_sum`, from the `ℝ≥0∞` Fubini
`MeasureTheory.lintegral_fintype_prod_eq_prod`, the companion of Mathlib's Bochner
`integral_fintype_prod_eq_prod`), **absorption of a final level with `m = 1`** (Talagrand's
"incorporation" (14.84)): if the last mark averages `G` by a constant factor, that level
contributes exactly the factor (`cascadeRec_snoc_one`), and the sub-multiplicative bound
`cascadeRec (G ∘ sum) ≤ (∏ C_p) G(0)` by Jensen at every level (`cascadeRec_sum_le`).

`ParisiFunctional`: **the Parisi functional** (Vol. II (14.88)),
`𝒫(m,q) = log 2 + X₀ - (1/2)∑_{p ≤ k+1} m_p (θ(q_{p+1}) - θ(q_p))`, `θ(x) = xξ'(x) - ξ(x)`, with
`X₀ = 𝔼 X₁` computed by the recursion (14.83) `X_p = (1/m_p) log 𝔼_p exp(m_p X_{p+1})` from
`X_{k+2} = log cosh(h + z₀ + ⋯ + z_{k+1})`, `𝔼 z_p² = ξ'(q_{p+1}) - ξ'(q_p)`: the recursion is
`parisiRec` — the cascade recursion of Theorem 14.2.1 — on Gaussian marks
(`parisiRecGauss`, `parisiX₀`, `parisiFunctional`), so the functional is a specialization of the
cascade theory rather than a new object. `𝔼 cosh(a + z) = cosh a · e^{v/2}`
(`integral_cosh_add_gaussianReal`) turns `cascadeRec_snoc_one` into **(14.84)**,
`X₁ = (ξ'(1) - ξ'(q_{k+1}))/2 + X'₁` (`parisiRecGauss_logCosh`), which is what relates the
functional (whose last level has `m_{k+1} = 1`) to the cascades (which need `m_p < 1`). At `k = 0`
the functional is explicit (`parisiFunctional_zero`), and **for the SK profile `ξ = β²x²/2` it is
exactly the replica-symmetric expression** `𝔼 log(2cosh(β√q z + h)) + (β²/4)(1-q)²`
(`parisiFunctional_skCovXi_zero`, `0 ≤ q ≤ 1`): Guerra's replica-symmetric bound of Vol. I,
Theorem 1.3.7, is the case `k = 0` of the Parisi bound (`skFreeEnergyLimit_le_parisiFunctional_zero`).

## Outstanding

Not yet formalized (and deliberately not recorded as `Prop`-valued definitions): the
Dovbysh–Sudakov / Aldous–Hoover representation and Panchenko's ultrametricity theorem; the
two-point identities (13.15)–(13.16) and the remaining identities of Vol. II §14.3 ((14.27),
(14.37), (14.47) with general `U`); Guerra's broken replica-symmetry bound (§14.4) for `k ≥ 1`,
now reachable from Proposition 14.3.3, the Gaussian interpolation, the site factorization, the
Parisi functional, the marking representation and the unzipping of the cascade into weights and
marks, the product law of the node marks, and the weighted comparison bound for a finite family
of branches, the convexity bound (14.79) on the weighted trace, and the Gaussian field of the
marks on `Σ_N × branches` with its tree covariance, identified with the tree kernel
`N R ξ'(q_{(α,γ)})`, and the interpolation bound for the truncated tree at fixed weights
(`guerra_truncated`); what remains is the integration over the cascade weights with the limit
`M → ∞` (monotone convergence of the branch sums), Proposition 14.3.3 for the pair averages, and
`φ(0)` via Theorem 14.2.1 with the site factorization and (14.84); the Parisi formula; Aizenman–Sims–Starr; the Gardner
formula; the Hopfield localization theorems (Vol. I Thm. 4.3.2, Vol. II Thm. 10.3.1) and the
Hopfield limits; the thermodynamic limit for non-convex profiles.
-/

namespace SpinGlass

end SpinGlass
