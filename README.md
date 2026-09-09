# SpinGlass

Lean 4 formalization of Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II.

SK / mixed \(p\)-spin, perceptron/Gardner, Hopfield, Guerra interpolation, cavity, Ghirlanda–Guerra,
Poisson–Dirichlet cascades, Parisi formula.

## Architecture

Two libraries: `Common` (Mathlib gaps — Gaussian IBP/comparison/concentration/scaling,
superadditivity, invariant weak limits, convexity of log-sum-exp, Griffiths' lemma, the module
structure on kernels) and `SpinGlass` (Talagrand). Proved vs statement-layer index:
`SpinGlass.Talagrand.MainResults`.

Finite volume: `EnergySpace α := PiLp 2 (fun _ : α => ℝ)`; `SpinGlass.FiniteGibbs` builds Gibbs
weights, free energy, and replica calculus from `Real.logSumExp`. SK and Hopfield are the models in
code. Vol. I §1.3 for SK is proved (Guerra, concentration, `tendsto_skFreeEnergy`, RS bound in the
limit).

Limit layer (`SpinGlass.Limit`, on the `GibbsMeasure` exchangeability / de Finetti pin):
`Exchangeability` and `AsymptoticGibbs` embed `Config N` into the spin space `ℕ → Bool` and prove
`exists_asymptoticGibbsMeasure`; `ExchangeableArray` and `OverlapArray` carry the overlap array on
the compact `[-1,1]^{ℕ×ℕ}` and prove `exists_asymptoticOverlapArray` — the limit is jointly
(weakly) exchangeable and almost surely a Gram array, which is the Dovbysh–Sudakov hypothesis;
`AsymptoticArrayLaws` is Talagrand Vol. II §15.3 verbatim — `IsUltrametric` (Def. 15.3.2, both
forms), `SatisfiesGhirlandaGuerra` (Def. 15.3.4), their stability under weak limits, Exercise
15.3.5, and the replica-symmetric array as a worked instance of all of it;
`GhirlandaGuerraCondDistrib` turns the identities into a disintegration — Panchenko's (1.2), the
conditional law of the new overlap — and thereby extends them to bounded measurable test functions.

`FiniteGibbs.ParameterDerivative` and `FiniteGibbs.FluctuationIntegral` are the parameter calculus
of the free energy: `nΦ'(x) = -⟨V⟩`, `nΦ''(x) = ⟨(V-⟨V⟩)²⟩`, and Talagrand Vol. II (12.9) —
the Gibbs fluctuation of the energy, integrated over the parameter, is the increment of `p'`.
`FreeEnergyConvexity` closes the convexity half of Vol. I §1.3: the free energy is convex in the
Hamiltonian, hence in `β`, Griffiths' lemma (`Common.Mathlib.Analysis.Convex.GriffithsLemma`,
`GriffithsMean`) turns `tendsto_skFreeEnergy` into convergence of `∂p_N/∂β` at almost every `β`,
and (12.9) holds for SK. `FiniteGibbs.DisorderDerivative` supplies the one Gaussian integration by
parts that removes the Hamiltonian: `∂p_n/∂β = (β/n)𝔼(⟨c(σ,σ)⟩ − ⟨c₁₂⟩)`, i.e. Talagrand's
Lemma 1.3.11 `∂p_N/∂β = (β/2)(1 − 𝔼⟨R₁₂²⟩)` — so `lim_N 𝔼⟨R₁₂²⟩` exists at a.e. `β`.
`FiniteGibbs.SelfAveraging` closes Vol. II Theorem 12.1.1 for SK: three Cauchy–Schwarz steps turn
(12.9) into `∫_a^b 𝔼⟨|H/N − ⟨H/N⟩|⟩ dβ ≤ √((b−a)b/2N)`; `FiniteGibbs.DerivSelfAveraging` adds the
disorder half via Griffiths-in-mean and a monotone-shift telescoping, and
`intervalIntegral_skTotalEnergy_fluctuation_le` is Theorem 12.1.1 for SK, explicit and `O(N^{-1/4})`
at `δ = N^{-1/4}`: **the energy per site self-averages**. `SKGhirlandaGuerra` composes that with the
sharp `L¹` Ghirlanda–Guerra error bound: `exists_beta_abs_skGhirlandaGuerra_error_le` gives, in
every window of inverse temperatures, a `β` at which the SK Ghirlanda–Guerra combination is
`O(N^{-1/4})` — exact at finite volume, no perturbation added. The whole §12.1–12.2 chain lives in
`GaussFieldFluctuation` for an arbitrary PSD covariance with constant diagonal `D` and
`|S| ≤ D` — every mixed `p`-spin model — and SK is the instance `S = skCovMatrix N 1`, `D = N/2`.
`MixedPSpin` makes that instantiation explicit for `ξ(r) = ∑ₚ aₚrᵖ` with `aₚ ≥ 0` (Talagrand's
realizability criterion, Vol. II (14.57)): `D = Nξ(1)`, so `D/N = ξ(1)` and every bound is uniform
in the volume. `GaussFieldFluctuation` also carries the *Markov* form of Theorem 12.1.1 — the set
of inverse temperatures where the fluctuation is large has small Lebesgue measure — resting on
`Common.Mathlib.MeasureTheory.Integral.IntervalMarkov` (Markov's inequality for a set and for an
interval integral, a Mathlib gap).

`Limit.OverlapArrayBracket` and `Limit.GhirlandaGuerraFinite` close the gap between the two
languages Talagrand uses for the Ghirlanda–Guerra identities. The **fresh-replica identity**
(`FiniteGibbs.gibbs_average_n_det_mul_sum_gibbs_pmf`) puts the "new replica" term and the "old
replica" terms in one replica space; the **dictionary**
(`integral_overlapArrayLaw_comp_take`, for any injective indexing of replica labels) identifies
integrals against the overlap array law with finite Gibbs brackets; and the **translation**
(`ghirlandaGuerraCombination_eq_overlapArrayLaw`) shows that the Ghirlanda–Guerra combination of
the finite replica calculus is `nκ` times the defect in Talagrand's Definition 15.3.4, Eq. (15.40),
for any Hamiltonian law with covariance kernel `κ φ(R_{στ})`. Composed with Theorem 12.1.1,
`exists_beta_abs_mixedPSpinGhirlandaGuerra_defect_le` gives, for every mixed `p`-spin model and
every window of inverse temperatures, a `β` at which the defect in (15.40) at the model's own
profile `φ = ξ` is `O(N^{-1/4})` — an explicit finite-volume rate, no perturbation added.

The identities at *individual monomial* test functions need the same defect identity applied to a
single `p`-spin **component** of a mixed Hamiltonian, and that generalisation is now carried out
once, at the level of the finite replica calculus: the cavity identity holds in an arbitrary
direction and with an arbitrary component field `σ ↦ ⟪H, w σ⟫` inside the bracket
(`FiniteGibbs.integral_gibbs_average_n_det_inner_mul`); the Ghirlanda–Guerra combination is defined
for an arbitrary kernel (`ghirlandaGuerraCombinationOf`, with the Hamiltonian's own case as its
specialisation); `ghirlandaGuerra_defect_of` identifies the combination of a cross-covariance
kernel with the component–observable covariance; the sharp `L¹` bound
`abs_integral_gibbs_average_field_mul_sub_le_integral_abs` holds for an arbitrary field with no
Gaussian hypothesis at all; and `ghirlandaGuerra_error_of_le_integral_abs` bounds the combination of
a component's kernel by that component's mean absolute fluctuation.
`Common.Mathlib.Analysis.InnerProductSpace.PositiveRange` supplies the algebraic prerequisite —
**Douglas' lemma** in finite dimensions, `0 ≤ T ≤ S ⟹ range T ≤ range S`, in operator and matrix
form — and `exists_directions_covKernel_eq` turns it into the construction: every positive
semidefinite kernel dominated by the disorder's own covariance *is* the cross kernel of a component
of the disorder. For a mixed `p`-spin model that produces the component whose kernel is a single
monomial (`exists_directions_covKernel_monomial`), and
`abs_ghirlandaGuerra_defect_monomial_le` then bounds the defect in Definition 15.3.4 at
`φ(r) = rᵖ` by `‖g‖/(n aₚ N)` times the mean absolute fluctuation of that component field. Since
monomial test functions suffice (`satisfiesGhirlandaGuerra_of_monomial`), the identities at every
continuous test function are reduced to the self-averaging of one explicit field.

The cavity layer no longer assumes that the Hamiltonian *is* the Gaussian vector: it is stated for
a Hamiltonian which is a continuous linear image `A x` of an abstract Gaussian vector
(`FiniteGibbs.integral_inner_mul_gibbs_average_n_det_comp`), resting on the first-order Gaussian
integration by parts along a linear substitution
(`Common.Mathlib.Probability.Distributions.Gaussian_IBP_LinearImage`, a Mathlib gap); the old
statements are corollaries at `A = id`. The same holds with a *component field*
`σ ↦ ⟪x, w σ⟫` inside the bracket
(`FiniteGibbs.integral_gibbs_average_n_det_inner_mul_comp`), the kernel being the
cross-covariance `Cov(⟪x, w σ⟫, (A x) τ)` — which for `Ω = E × E`, `A (x,y) = x + t y`,
`w σ = (0, e_σ)` is `t` times the second block's covariance, with the constant diagonal §12.1
requires. Two more Mathlib gaps support the construction of
independent components: the covariance *operator* of a centered `multivariateGaussian` is
multiplication by its matrix (`MultivariateCovariance`), and the sum of two independent centered
multivariate Gaussians is the centered multivariate Gaussian with the summed covariance
(`MultivariateSum`). Consequently `map_add_smul_prod_gaussField_overlapCovMatrix` shows that the
interpolating field of two independent mixed `p`-spin disorders is again a mixed `p`-spin disorder,
with profile `A + t²B` — so the family through the model at `t = 1` has an overlap-driven covariance
with nonnegative coefficients at every `t`, and differentiating in `t` differentiates in a single
`p`-spin coupling.

`MixedPSpinComponent` closes the first half of that programme: `exists_gaussianDisorder_pair_indepFun`
produces a pair of independent centered Gaussian disorders with *arbitrary* prescribed positive
semidefinite kernels (the SK/reference pair is now a two-line corollary), `pairAffine` is the
interpolation `(x, y) ↦ x + t y` — affine in the Hamiltonian, hence a convex path —
`crossKernel_pairAffine_std_basis_right` computes the cross kernel of the second block as `t K₂`,
and `abs_integral_gibbs_average_component_le` is **Talagrand's Lemma 12.1.4 for a component**:
`|𝔼⟨H_B⟩| ≤ 2|t| M₂`, so the mean `p`-spin energy per site is bounded by `2|t| aₚ` uniformly in the
volume. `covarianceOperator_map_std_basis_eq_crossKernel` identifies a linear-image Hamiltonian's
*own* kernel as the cross kernel at the adjoint directions — no adjoint appears in statement or
proof — and `covarianceOperator_map_pairAffine_std_basis` reads off the interpolated Hamiltonian's
kernel as `K₁ + t²K₂`, which for a mixed `p`-spin model is `N(ξ − (1−t²)aₚrᵖ)(R)`: overlap-driven
with nonnegative coefficients at every `t`, so the §12.1 hypotheses hold along the whole path. All the linear-image cavity identities are stated for the *affine* Hamiltonian `A x + c`, so
the external field costs nothing.

Both halves of §12.1 now run along that interpolation:
`integral_abs_free_energy_density_pairAffine_sub_mean_le` is the free-energy concentration
(Gaussian Poincaré on the pair space, evaluated with `covarianceOperator_map_pairAffine_std_basis`
— no identification of the interpolated law needed), and
`intervalIntegral_component_fluctuation_le` is **Theorem 12.1.1 for a component**: three explicit
terms, `O(N^{-1/2}) + O(δ) + O(N^{-1/2}/δ)`, hence `O(N^{-1/4})` at `δ = N^{-1/4}`. **The `p`-spin
component self-averages.**

The composition is then carried out: the sharp `L¹` bound now allows the Hamiltonian and the tested
field to be *separate* functions of the disorder (`abs_integral_gibbs_average_field_mul_sub_le_integral_abs'`,
with no Gaussian hypothesis at all), `ghirlandaGuerra_defect_of_comp` and
`ghirlandaGuerra_error_of_comp_le_integral_abs` give the component defect identity and error bound
for a linear-image Hamiltonian, `abs_ghirlandaGuerraCombinationOf_component_le` shows the error is
`B N` times exactly the quantity Theorem 12.1.1 controls, and
`exists_coupling_abs_ghirlandaGuerraCombinationOf_component_le` composes the two with the mean
value theorem: **at some coupling in every window, the Ghirlanda–Guerra combination of the
`p`-spin component's kernel is `O(N^{3/4})`, so the defect in (15.40) at `φ(r) = rᵖ` is
`O(N^{-1/4})`.** No new definition is needed for the pair setting —
`ghirlandaGuerraCombinationOf` at the pushforward law of the Hamiltonian *is* the pair-setting
combination, so the whole §15.3 translation applies verbatim.

`MixedPSpinComponentGG` closes the chain. The Mathlib gap on the way is filled in general:
`ProbabilityTheory.IsGaussian.eq_multivariateGaussian` says every Gaussian measure on a Euclidean
space is `multivariateGaussian μ[id] (covMatrix μ)` — no hypotheses — with `covMatrix` Mathlib's
`LinearMap.toMatrix₂` of `covarianceBilin` in the standard basis (positive semidefinite by
`posSemidef_covMatrix`), built on `ContinuousLinearMap.ext_basis₂`, the continuous
`LinearMap.ext_basis`. Hence `map_pairAffine_disorderPairLaw`: the law of `H_A + t H_B` *is* the
centered Gaussian field with kernel `K₁ + t²K₂`. `exists_coupling_abs_ghirlandaGuerra_defect_component_le`
is the identity at the profile of a component with an explicit rate, and
`exists_coupling_abs_ghirlandaGuerra_defect_mixedPSpin_le` is the **mixed `p`-spin capstone of
§12.2**: for every mixed `p`-spin model, external field, and window `[a,b] ⊂ (0,∞)`, at some
`x ∈ [a,b]` the model with its `p`-th coefficient rescaled by `x²` — the canonical field
`gaussField N (overlapCovMatrix N ξₓ)`, no coupling space in the statement — satisfies the
Ghirlanda–Guerra identity at `φ(r) = rᵖ` up to an explicit `O(N^{-1/4})`;
`exists_coupling_abs_ghirlandaGuerra_defect_split_le` is the same for any split `ξ = A + B` at
`φ = B`.

`MultiComponent` and `MixedPSpinPerturbation` are **Talagrand's Theorem 12.2.2 at finite volume**
(the extended Ghirlanda–Guerra identities). The Mathlib gaps filled on the way:
`multivariateGaussian_map_sum_smul_pi` (a linear combination of independent centered multivariate
Gaussians is the centered Gaussian with the combined covariance, under `Measure.pi`),
`multivariateGaussian_zero`, `Fin.insertNth_eq_update`, and the continuity of the
energy-fluctuation functionals in a Hamiltonian parameter ranging over any first-countable space
(`continuous_integral_totalFluct_param`). On top of them: the canonical carrier `familyLaw` of a
finite family of independent Gaussian disorders, with the pair `(∑_{i≠s} cᵢωᵢ, ωₛ)` as independent
`GaussianDisorder`s (`familyRest`, `familyCoord`); the perturbed Hamiltonian `familyHam` and the
fluctuation functional `familyFluct` of each component, continuous in the couplings; Theorem
12.1.1 for one component uniformly in the others (`intervalIntegral_familyFluct_update_le`); the
defect bound `abs_ghirlandaGuerra_defect_family_le`; Fubini over the box of couplings
(`setIntegral_familyFluct_le`) and the mean value principle (`exists_couplings_familyFluct_le`);
and the capstone `exists_couplings_abs_ghirlandaGuerra_defect_family_le`: **couplings
`β ∈ [a,b]^{m+1}` at which the perturbed model satisfies the Ghirlanda–Guerra identity at every
component profile simultaneously, for every test function, with an explicit rate.**
`exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le` is the mixed `p`-spin
instance: perturbing by `wₛ² N Rˢ⁺¹` the perturbed model is the mixed `p`-spin model with profile
`ξ(r) + ∑ₛ (βₛwₛ)² rˢ⁺¹`, and the identities hold at all monomials `r, …, rᵐ⁺¹` at once. The family is
finite, the window sits in `(0,∞)`, and the couplings are exhibited rather than averaged over —
exactly what the limit consumes.

`Limit.GhirlandaGuerraLimit` and `MixedPSpinLimit` pass to the limit. `ggDefect` is the defect in
Talagrand's (15.40), continuous in the law (`continuous_ggDefect`), and the identities are its
vanishing (`satisfiesGhirlandaGuerra_iff_ggDefect`); `satisfiesGhirlandaGuerra_of_tendsto_ggDefect`
is the passage from approximate to exact identities, and `exists_subseq_tendsto_satisfiesGhirlandaGuerra`
extracts, from any sequence of exchangeable Gram array laws with vanishing monomial defects, a
convergent subsequence whose limit satisfies the identities. `mixedPSpinArrayLaw N ξ h` is the
annealed overlap-array law of the mixed `p`-spin model, and
**`exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin`** is the capstone of §12.2: for every
mixed `p`-spin model and every admissible scaling `(m_N, c_N, δ_N)`, couplings `β_N` exist such that
along a subsequence the perturbed models (profile `ξ(r) + ∑ₛ (β_{N,s}c_N)² rˢ⁺¹`, perturbation
variance `→ 0`) converge in distribution to a jointly exchangeable Gram law **satisfying the
Ghirlanda–Guerra identities**; `…_explicit` fixes the scaling `c_N = N^{-1/16}`, `δ_N = N^{-1/4}`,
`m_N = ⌊N^{1/16}⌋`, leaving no free parameter.

`GaussianPerturbation` is Talagrand's Lemma 12.2.1: `gaussFreeEnergy N S h ≤ gaussFreeEnergy N (S+T) h
≤ gaussFreeEnergy N S h + D/(2N)` for an independent perturbation of variance `≤ D` per
configuration (Jensen for the convex free energy; Jensen for the logarithm and the Gaussian
exponential moment `integral_exp_mul_apply_gaussField`), and
`abs_gaussFreeEnergy_perturbedProfile_sub_le`: the perturbation producing the Ghirlanda–Guerra
identities moves the free energy by at most `(∑ₛ wₛ²)/2 → 0`.

`Limit.PositivityPrinciple`, `Limit.PositivityGG` and `MixedPSpinPositivity` are **Talagrand's
positivity principle** (Vol. II, Theorem 12.3.1): `TendstoGGDefectUniform` is Definition 15.4.1 (the
extended identities asymptotically, uniformly over observables; monomials suffice by
`tendstoGGDefectUniform_of_monomial`); Proposition 12.3.2 is proved for the annealed overlap-array
law of any random Hamiltonian from Gram positivity of weighted configurations
(`bind_overlapArrayLaw_real_negSet_le`); Proposition 12.3.4 is the recursion
`I_{j+1} ≥ ((j+a)/(j+1)) I_j − |defect|` for the ramp observables `negObs`, iterated and compared
with `P_k(a) ≥ e⁻² k^{a-1}`; `tendsto_negMassLaw` is the theorem, `tendsto_real_negLevel_bind`
its Gibbs form at every level, `measure_negOverlap_eq_zero_of_tendsto` the passage to a
distributional limit. The Ghirlanda–Guerra capstone now also delivers the uniform identities along
the perturbed sequence, and `exists_subseq_tendsto_satisfiesGhirlandaGuerra_nonnegOverlap_mixedPSpin`
adds **nonnegative overlaps almost surely** to the limit law's properties.

`MixedPSpinThermodynamicLimit` is **Guerra–Toninelli for every convex mixed `p`-spin model**
(Vol. I Theorem 1.3.9, Vol. II §12.1): superadditivity is proved for an arbitrary pair of kernels
dominated by the non-interacting split kernel, Jensen's inequality supplies the domination for a
profile convex on `[-1,1]`, and Fekete's lemma gives the limit `mixedPSpinFreeEnergyLimit` (the SK
model is the corollary `ξ(r) = β² r²/2`). Lemma 12.2.1 then shows the Ghirlanda–Guerra perturbation
of the capstone has the same free-energy limit.

`FiniteGibbs/PointwiseFluctuation` and `MixedPSpinDifferentiability` are **Panchenko's Theorem
12.1.3 and the second half of Theorem 12.1.10**: energy self-averaging at a *fixed* temperature,
proved from Lemmas 12.1.7–12.1.9 (the monotone sandwich `ψ ∓ 4p'`, a point of the window with
small `p''`, Griffiths in mean, and the convex-analysis lemma
`ConvexOn.exists_eventually_deriv_sub_deriv_le`). For every even mixed `p`-spin model with external
field, the Ghirlanda–Guerra defect of the model's own profile vanishes at every `β ≠ 0` where the
limiting free energy is differentiable, hence at almost every `β`, with no perturbation and no
window average.

`Common/Mathlib/Probability/PointProcess` is a **Poisson point process theory** Mathlib lacks:
finite-intensity processes as a Poisson number of i.i.d. positions, **any s-finite intensity** by
superposition of Mathlib's `sfiniteSeq` on `Measure.infinitePi` (`poissonPointProcess`, a measure on
`Measure E`), the Laplace functional and void probabilities in `HasLaw` form, Talagrand's stable
intensity `u^{-m-1} du` with its scaling and moment integrals, and the marked **Poisson–Dirichlet**
process with the Laplace transform of `∑ u_α v(g_α)`, its explicit moments of order `m' < m`
((13.8)–(13.9)), its tails, `𝔼|log S| < ∞`, and Talagrand's identity (13.10) / Theorem 13.1.5 via
Frullani's integral (Vol. II §13.1). On top of it, the **Poisson–Dirichlet cascades** of Vol. II
§14.2 by recursion on the number of levels: Proposition 14.2.2 (the moments of a cascade sum, with
an explicit constant, unconditionally in `ℝ≥0∞`) and **Theorem 14.2.1**
`𝔼 log ∑_α v_α exp F(α) = F₁` with Talagrand's recursion (14.5), under the single hypothesis
`𝔼 exp F < ∞`. The **Mecke formula** `𝔼 ∑_{x∈N} f(x,N) = ∫ 𝔼 f(x, N+δ_x) dΛ(x)` for any s-finite
intensity (from the invariance of infinite products under resampling one coordinate, new for
Mathlib), and through it **Theorem 13.1.6**: the identities (13.13), (13.14) and
`𝔼 ∑ v_α² = 1 - m`, with the Gamma-function constant `m c_m = Γ(1-m)`; and for the cascades
**Proposition 14.3.3**, `𝔼⟨1_{(α,γ)=r}⟩ = m_r − m_{r−1}`, by induction on the levels from a
general-exponent (13.14), with no differentiation in Talagrand's parameter. Guerra's
interpolation derivative and comparison bound now hold on an arbitrary finite state space with an
arbitrary fixed vector (`FiniteGibbs/GaussianInterpolation`), the form Lemma 14.4.1 needs. The
cascade recursion factorizes over independent sites (Talagrand's (14.82)) and absorbs a final
level with `m = 1` as a constant (his (14.84)) (`CascadeProduct`, with the `ℝ≥0∞` Fubini
`lintegral_fintype_prod_eq_prod`), and the **Parisi functional** (14.88) is defined as that
recursion on Gaussian marks (`ParisiFunctional`): at `k = 0` it is explicit, and for the SK
profile it is exactly the replica-symmetric expression of Guerra's bound — Vol. I, Theorem 1.3.7
is the case `k = 0` of the Parisi bound (`skFreeEnergyLimit_le_parisiFunctional_zero`). The
Poisson–Dirichlet process is now built from an explicit product decomposition of its intensity
(`stableSeq`, `pdSeq`), and **zipping independent families** (`⊗ᵢ (μᵢ ⊗ νᵢ)` is the image of
`(⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)`, `Common/Mathlib/Probability/ProductMeasureProd`, new for Mathlib) gives the
**marking representation** (`Marking`): the marked sample is the weights sample zipped with an
independent i.i.d. array of marks, an identity between measures on the sample space; unzipping
every level, **a cascade is its weights zipped with its marks, independent of each other**
(`CascadeUnzip`), and the cascade sums and prefix-squares of §14.3 are explicit sums over branch
addresses (`CascadeBranches`), while the marks of all nodes of the tree form an infinite product
`⊗ μ_p` (`CascadeNodeMarks`, via a new `infinitePi`-over-a-sum-type lemma). Guerra's comparison
bound now also comes with a `t`-dependent bound on the derivative (by the fundamental theorem of
calculus), Gaussian fields pull back along maps of state spaces, and the bound holds for
**weighted free energies** `(1/n) log ∑_x w_x e^{-H x}` with nonnegative weights
(`FiniteGibbs/WeightedInterpolation`) — Lemma 14.4.1 for a finite family of branches, with the
convexity bound (14.79) on the trace of the model kernel against a tree kernel
(`Parisi/TreeTrace`), and a product of real Gaussians is identified with a diagonal multivariate
Gaussian (`Gaussian/PiGaussian`); the marks of a truncated cascade with Gaussian levels form a
Gaussian field on `Σ_N × branches` with the tree covariance of (14.74) (`Parisi/TreeField`), and
Guerra's interpolation bound holds for the truncated tree at fixed weights, with both endpoints
computed — Lemma 14.4.1 with (14.79)–(14.80) (`Parisi/GuerraRSB`, `guerra_truncated`).

Still to discharge (there is no statement layer of undischarged `Prop`s): Panchenko's
ultrametricity theorem (Talagrand's Research Problem 15.3.7), the Dovbysh–Sudakov representation,
the two-point identities (13.15)–(13.16) and the remaining identities of §14.3, Guerra's
broken-RSB bound (§14.4) for `k ≥ 1` (the integration over the cascade weights with the
truncation limit, Proposition 14.3.3 for the pair averages and `φ(0)` remain), the Parisi equality, Gardner,
and the Hopfield localization theorems and limits.

## Build

Lean / Mathlib `v4.34.0-rc2`. Lake dependencies: [Mathlib](https://github.com/leanprover-community/mathlib4) and
[`GibbsMeasure`](https://github.com/matteo-ax/GibbsMeasure) (`8a158f0`).

```bash
lake exe cache get
lake build
```

## Acknowledgements

Cameron–Martin code in `Common/Mathlib/Probability/Distributions/Gaussian/` is adapted from Rémy
Degenne’s mathlib4 PRs
[#26291](https://github.com/leanprover-community/mathlib4/pull/26291),
[#30582](https://github.com/leanprover-community/mathlib4/pull/30582), and
[#27608](https://github.com/leanprover-community/mathlib4/pull/27608).
Fernique is in Mathlib ([#24430](https://github.com/leanprover-community/mathlib4/pull/24430)).

## References

- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II (Springer, 2010/2011).
- M. Talagrand, [The Parisi formula](https://annals.math.princeton.edu/2006/163-1/p04),
  *Ann. of Math.* **163** (2006), 221–263. [doi:10.4007/annals.2006.163.221](https://doi.org/10.4007/annals.2006.163.221)
- D. Panchenko, [The Parisi ultrametricity conjecture](https://annals.math.princeton.edu/2013/177-1/p08),
  *Ann. of Math.* **177** (2013), 383–393. [doi:10.4007/annals.2013.177.1.8](https://doi.org/10.4007/annals.2013.177.1.8)

## Cite

```bibtex
@software{Cipollina_SpinGlass_2026,
  author = {Cipollina, Matteo},
  title  = {{SpinGlass}: a {Lean} 4 formalization of {Talagrand}'s
            {Mean Field Models for Spin Glasses}},
  year   = {2026},
  url    = {https://github.com/or4nge19/SpinGlass},
  note   = {Cameron--Martin layer adapted from R\'{e}my Degenne,
            mathlib4 PR 26291}
}
```
