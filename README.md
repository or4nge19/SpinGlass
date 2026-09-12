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
`𝔼 exp F < ∞`. The **Mecke equation** `𝔼 ∑_{x∈N} f(x,N) = ∫ 𝔼 f(x, N+δ_x) dΛ(x)` for any s-finite
intensity, in its fundamental **reduced** (Palm) form `𝔼 ∑_{x∈N} g(x, N∖x) = ∫ 𝔼 g(x,N) dΛ(x)`
(deleting a point of a sample is again a sample), its off-diagonal bivariate iterate
`𝔼 ∑_{x≠y∈N} f(x,y,N) = ∫∫ 𝔼 f(x,y,N+δ_x+δ_y)`, and `𝔼 N^{(2)} = Λ ⊗ Λ` for the second factorial
measure (all new for Mathlib); through them **Theorem 13.1.6** in full, (13.13)–(13.17), with
(13.15) `𝔼 (∑_{α≠γ} v_α v_γ U_α W_γ)/(∑ v_α V_α)² = m 𝔼[U V^{m-1}] 𝔼[W V^{m-1}]/(𝔼 V^m)²` needing
no finiteness of `U, W`, and the constant `m c_m = Γ(1-m)`; and for the cascades
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

The tree is then untruncated and the weights integrated out, giving **Guerra's broken
replica-symmetry bound**, Vol. II Theorem 14.4.3: `p_N ≤ 𝒫_k(m, q)`
(`Parisi/GuerraParisi`, `mixedPSpinFreeEnergy_le_parisiFunctional`), for every `N`, every number
of levels `k`, every `0 = q₀ ≤ ⋯ ≤ q_{k+2} = 1` and every `0 < m₁ < ⋯ < m_k < 1`, hence, by continuity of `𝒫_k`
in the exponents, every nondecreasing `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`
(`mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone`). Along the way:
the marks along a fixed branch are the product `μ₁ ⊗ ⋯ ⊗ μ_k` (`CascadeBranchLaw`, from a new
marginal-of-an-infinite-product lemma), the prefix-squares satisfy `Q_r ≤ S²` on every sample
(from a new general fact — for a counting measure `∫ fg dN ≤ (∫ f dN)(∫ g dN)`, i.e. `‖·‖₂ ≤ ‖·‖₁`,
`MeasureTheory/Integral/LintegralCounting`), the truncated pair fractions converge to the cascade
ones, `φ(0)` is computed by Theorem 14.2.1 with the site factorization and the absorption (14.84),
the bound is computed by Proposition 14.3.3, and Abel summation collapses the two into the Parisi
functional. The hypotheses are weaker than the reference — only the supporting-line inequality
for `ξ` on the range used (a new Mathlib-level lemma, `Analysis/Convex/TangentLine`) and the
monotonicity of `ξ'` along `q` — with the textbook form as a corollary
(`mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn`); for the SK model it reads
`p_N(β, h) ≤ 𝒫_k(m, q)` at every level `k` (`skFreeEnergy_le_parisiFunctional`), and at `k = 0`
it is Guerra's replica-symmetric bound of Vol. I, Theorem 1.3.7, now at finite `N`.

Optimizing over the parameters gives the **upper half of the Parisi formula** (14.93):
`inf 𝒫_k(m, q)` is defined as the infimum of the values of the functional at admissible
parameters (`Parisi/ParisiInf`, `parisiInf`), `p_N ≤ inf 𝒫` at every `N`, and — composing with
Guerra–Toninelli superadditivity, since the bound does not depend on `N` — `lim_N p_N ≤ inf 𝒫`,
for the SK model included (`skFreeEnergyLimit_le_parisiInf`). Talagrand's second form of the
functional (14.403) is also available (`parisiFunctional_eq_theta_sum`), from a new general
telescoped **summation by parts** valid in any ring.

**§14.6, the bound for coupled copies, is complete through Proposition 14.6.3.** Talagrand's
(14.147) — the constrained free energy `(1/N) 𝔼 log ∑_{R_{1,2}=u} e^{-H_N(σ¹)-H_N(σ²)-H⁰}`, or
rather its recursion in the marks of `H⁰`, is at most
`2 log 2 + Y₀(λ) − λu − (1/2)∑_{ℓ,ℓ'}∑_p n_p(θ(ρ^{ℓ,ℓ'}_{p+1}) − θ(ρ^{ℓ,ℓ'}_p))` — is proved for
every nondecreasing `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1` and *free* top values `ρ_{κ+1}`
(`Parisi/CoupledParisi`, `coupled_bound'` for strictly increasing exponents,
`coupled_bound'_of_monotone` in general). The two-dimensional scheme runs on one site-tree cascade over `Fin N × J` with
per-level factors, the interpolating field on some columns and the external field `H⁰` on the
complementary ones, independent by the block independence of `Measure.pi`
(`Parisi/PairTreeFieldIndep`); Lemma 14.6.1 holds with an independent random external field
(`Parisi/CoupledInterpolation`); the level bound is the generic level-bound law of
Proposition 14.3.3 shared with Guerra's bound (`Parisi/LevelBoundLaw`); the tree is untruncated at
fixed weights of positive finite mass (`Parisi/CoupledFixedWeights`, with the exponential moments
of the disorder, `FiniteGibbs/GaussianFieldExpMoment`); and both endpoints are evaluated by
Theorem 14.2.1 conditionally on the disorder and the root marks, from the joint integrability of
`log ∑_α v_α G_θ(z_α)` in the weights, the parameter and the marks — Jensen along the branch chosen
by the weights (`Parisi/CascadeLogIntegrable`). Talagrand's diagonal (14.137) omits the term
`α = γ`: the bound proved is the correct one, stronger by `(θ(1) + θ(u))(1 − n_κ)`, and leaving
`ρ_{κ+1}` free absorbs exactly the level `n_{κ+1} = 1` of his Proposition 14.6.3, with no
continuity argument in the `n_p`. The endpoint `Y₀` factorizes over the sites along the currying
`(Fin N × J → ℝ) ≃ (Fin N → J → ℝ)` (`Parisi/CoupledSite`), Proposition 14.6.3 is the
specialization to Talagrand's coupling (14.155)–(14.158) with a sign `η = ±1`, with the level sum
(14.152) and the constrained free energy (14.149) as the left-hand side (`Parisi/CoupledProp`), and
at `λ = 0` its right-hand side is exactly `2𝒫_k(m, q)`: `Y₀(0) = 2X₀` from the raw-coordinate
identity of Lemma 14.3.6(a), while the diagonal defect at `q_{k+1}` and the absorbed level (14.84)
combine into the last term of the functional (`Parisi/CoupledLambdaZero`,
`constrainedFreeEnergy_le_two_parisiFunctional`).

The **`λ`-dependence of `Y₀`** rests on two new general pieces. Talagrand's tilted averages
`𝔼(W₁ ⋯ W_k A)` of §14.3 are the integrals against a genuine probability measure, the product law
of the marks with density `W₁(z₁) ⋯ W_k(z₁, …, z_k)` (`cascadeTiltMeasure`, a `withDensity` of
`Measure.pi`; `Common/…/CascadeTiltMeasure`), so that signed functions can be averaged and
Talagrand's nesting `𝔼_p(W_p 𝔼_{p+1}(⋯))` is a Fubini statement. Against it, **the derivative of the
Parisi recursion in a parameter is the tilted average of the derivative**,
`d/dλ F₁(λ) = 𝔼(W₁ ⋯ W_k ∂_λ F_λ)` (`hasDerivAt_parisiRec`, `Common/…/CascadeDeriv`), for terminal
functions with a bounded `λ`-derivative satisfying (14.4) at the point — Talagrand's
`Y'_p = 𝔼_p(W_p Y'_{p+1})` of (14.185) and (14.215), iterated over the levels, proved by
differentiation under the integral sign level by level. Consequently `Y₀(λ)` is differentiable
with `Y₀'(λ) = 𝔼_{y₀} 𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})` and `|Y₀'(λ)| ≤ 1`, from Talagrand's inequality
`|ch A ch B sh λ + sh A sh B ch λ| ≤ ch A ch B ch λ + sh A sh B sh λ` (`Parisi/CoupledDeriv`,
`hasDerivAt_pairSiteY₀`, `abs_pairSiteY₀'_le_one`). Proposition 14.6.3 itself no longer needs `ξ`
even when `η = 1`: only `ξ'(η x) = η ξ'(x)` and `θ(η x) = θ(x)` enter, so odd `p`-spin models at
`u ≥ 0` are covered.

**The recursion as a function of the exponents** (`PointProcess/CascadeExponent`,
`PointProcess/CascadeJensenLower`): `F₁` is nondecreasing in each `m_p` (Lyapunov's inequality
level by level, `cascadeRec_mono_exponent`) and continuous on `(0,1]^k` under (14.4)
(`continuousOn_cascadeRec`: dominated convergence level by level, Jensen's bound as the
dominating function, and the joint continuity of `x^y` on `ℝ≥0∞ × ℝ` away from `(0,0)`, `(∞,0)`,
`ENNReal.continuousAt_rpow`, absent from Mathlib). The two-sided Jensen bound
`𝔼F ≤ F₁ ≤ log 𝔼 e^F` (`integral_le_parisiRec`, from Jensen for `log`,
`integral_log_le_log_integral`, also absent) is uniform in the exponents, so `𝔼_θ log F₁(θ)` is
integrable and continuous in the exponents with no strict monotonicity
(`integrable_log_cascadeRec`, `continuousOn_integral_log_cascadeRec`), and Talagrand's density
argument after (14.145) is the general `le_of_forall_strictMono_le`. Hence (14.147),
Proposition 14.6.3 and its `λ = 0` form, and Guerra's bound (14.90) hold for every nondecreasing
`0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1` (`coupled_bound'_of_monotone`, `coupled_bound_coupling`,
`constrainedFreeEnergy_le_two_parisiFunctional`,
`mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone`); a level with exponent `n₁ = 0` is a plain
expectation, a merging statement rather than a limit.

**Lemma 14.6.5, `0 ≤ Y₀''(λ) ≤ 1`** (`Parisi/CoupledSecondDeriv`): through Theorem 14.2.1,
`Y₀(λ)` is the expectation over the root marks and the cascade of `log ∑_α v_α exp Y_{κ+1}(λ, ζ_α)`,
and `exp Y_{κ+1}(λ) = (e^λ ch(ζ¹+ζ²) + e^{−λ} ch(ζ¹−ζ²))/2`, so by linearity of the cascade sum (a
new general fact, `PointProcess/CascadeLinear`) `S(λ) = ∑_α v_α exp Y_{κ+1} = (e^λ P + e^{−λ} M)/2`
with `P, M` independent of `λ`: `S'' = S`, `|S'| ≤ S`, `(log S)'' = 1 − ((log S)')² ∈ [0, 1]`.
Two dominated differentiations with constant bounds give `Y₀'' = 1 − 𝔼(S'/S)²`
(`hasDerivAt_pairSiteY₀'`, `pairSiteY₀''_nonneg`, `pairSiteY₀''_le_one`; the tilted-average
`Y₀'` and the cascade `Y₀'` agree by uniqueness of derivatives). Hence `Y₀` is convex and
`Y₀ − λ²/2` concave, first for strictly increasing exponents, then for nondecreasing ones as
pointwise limits (convexity passes to limits, `Analysis/Convex/Limit`), and the tangent-line
inequalities `Y₀(0) + λY₀'(0) ≤ Y₀(λ) ≤ Y₀(0) + λY₀'(0) + λ²/2` (`taylor_le_pairSiteY₀`,
`pairSiteY₀_le_taylor`) hold for every `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1`; the joint (14.4)
`𝔼_{y₀}𝔼_y exp Y_{κ+1} < ∞` is computed from the four exponentials of (14.142).

**The operators `T_{m,v}` of §14.7** (`Gaussian/HeatSemigroup`, `Gaussian/ColeHopf`,
`PointProcess/CascadeColeHopf`): Talagrand's `T_{m,v}A(x) = (1/m) log 𝔼 exp mA(x + g√v)` is the
Cole–Hopf transform of the Gaussian heat semigroup `P_v H(x) = 𝔼 H(x + g√v)`, so the general
object is the heat semigroup on functions of exponential growth. It is built once, in full
generality: `P_v` preserves `Cⁿ` and commutes with `d/dx`
(`iteratedDeriv_integral_comp_add_gaussianReal`), `(x, v) ↦ P_v H(x)` is jointly continuous, and
*every* `x`-derivative again solves the heat equation, `∂_v ∂ₓⁱ P_v H = ½ ∂ₓ^{i+2} P_v H`
(`hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var`, with its one-sided form at
`v = 0`) — so the mixed partials of the flow need no Clairaut argument. The master statement is a
chain rule along a curve `v ↦ (y(v), σ(v))` for a *time-dependent* integrand
(`hasDerivAt_integral_curve_gaussianReal`), proved by dominated differentiation plus Gaussian
integration by parts (Stein's lemma for functions of exponential growth, a new
`GaussianIntegrationByParts` entry); Talagrand's (14.197)–(14.199), (14.202)–(14.203), the
semigroup property (14.195), the Lipschitz bound (14.271) — proved for `m > 0` by monotonicity of
exponential averages, with no differentiability at all (`abs_coleHopf_sub_le_of_lipschitz`) — and
the exponent derivative `∂_m T_{m,v}A` are corollaries. **Lemma 14.7.3**, `∂_v (T_{m',a−v} ∘
T_{m,v})A = ((m − m')/2) 𝔼(B'(Z)²R)`, holds for every `m'`, the case `m' = 0` (where `R = 1`)
being the time-dependent chain rule applied to `v ↦ B(·, v)` and the case `m' ≠ 0` the same
computation inside a tilt. Finally the two sides of the theory are identified: the Parisi
recursion with Gaussian marks *is* the iterated Cole–Hopf transform,
`parisiRec = T_{m₁,v₁} ⋯ T_{m_k,v_k}(G)` (Talagrand's (14.190)–(14.191),
`parisiRec_gaussian_comp_add_sum`), so his (14.215)/(14.217) — the derivative of `A₁` in a
parameter of the terminal function is the tilted average `𝔼(W₁ ⋯ W_k ∂_λ G_λ)` — is the cascade
differentiation formula `hasDerivAt_parisiRec` read through that identification
(`hasDerivAt_coleHopfIterate`). That formula is proved in **local** form
(`hasDerivAt_parisiRec_ball`, `hasDerivAt_coleHopfIterate_ball`): the parameter need only range
over a ball and no joint measurability in it is required, which is what the applications have —
an overlap `q_r`, a variance split — since the families are differentiable only on an interval.
Composing it with Lemma 14.7.3 gives **(14.219)–(14.220)** in operator form
(`hasDerivAt_coleHopfIterate_split`): the derivative of `A₁` in the split point `v` of an
innermost pair of levels `T_{m',a−v} ∘ T_{m,v}` is `𝔼(W₁ ⋯ W_{r−1} ((m − m')/2) A_r'(ζ_r)²)`.
The level structure itself is packaged associatively as an iterate along a *list* of levels
(`coleHopfIterateList`, `coleHopfIterateList_append`), so the levels split anywhere and
Talagrand's two merging mechanisms are one-liners: a zero-variance level drops (`T_{m,0} = id`)
and two adjacent levels with equal exponents merge by the semigroup property — his (14.233) and
(14.237). Beyond the derivatives, `T_{m,v}` is developed as an *operator*: monotone in the
function, commuting with constants and translations, hence (for every exponent, with no
differentiability) Lipschitz-preserving, a contraction for the sup norm, and strongly continuous
in the variance with modulus `coleHopfModulus m L v = T_{m,v}(L|·|)(0)`, which vanishes with the
variance. The same contraction passes to the iterate, so Talagrand's `S(v, m)` of (14.235) — the
`X₀` of the split configuration, whose `v`-derivative is (14.219)–(14.220) after the outermost
`z₀`-average (`hasDerivAt_integral_coleHopfIterate_split`) — is continuous in the split point
right down to the degenerate split `v = 0`
(`continuousAt_integral_coleHopfIterate_split`), which is what will let `U(v)` be recovered from
its derivative by the fundamental theorem of calculus with no Clairaut argument.

The weights `W_p = (R_{p+1}/R_p)^{m_p}` of (14.22) through which all of §14.3 is expressed, their
defining property `𝔼_p W_p = 1`, and the tilted averages `𝔼(W₁ ⋯ W_k A)` of (14.24)–(14.26) are in
place (`CascadeTilt`), an average against a probability measure that reduces to the plain product
average when the recursion is run on a constant. On top of them, **Talagrand's identity
(14.26)–(14.27)** `𝔼⟨A/G⟩ = 𝔼(W₁ ⋯ W_k (A/G))` (`CascadeGibbs`), proved not by differentiating the
recursion but through a new **one-insertion moment of a cascade**, itself an induction from a new
one-level Poisson–Dirichlet identity that generalizes both the `a = 0` identity and the moment
formula of §13.1. Throughout, the hypothesis on `G = exp F` is exactly Talagrand's (14.4),
`𝔼 exp F < ∞`, and not boundedness — which matters, since the interpolating free energies to which
§14.5 applies these identities are unbounded.

The **second-order identities of §14.3** — (14.32), (14.33), Proposition 14.3.2 (14.37) and
**Theorem 14.3.5** (14.47) — are now proved (`CascadeSecondMoment`, `CascadePair`), all as the
case `a = 0` of statements with a free exponent. Theorem 14.3.5 is the version for a general
function of the *pair* of mark sequences along two branches, against the coupled tilted average
over two copies of the marks that agree below level `r` and are independent above it; Talagrand
polarizes from the product case and then approximates, whereas here the induction runs directly
for a general function, so no approximation argument is needed, and his (14.42) — the square of a
conditional expectation as an expectation over two independent copies — becomes a consequence of
the definitions.

**Lemma 14.3.6 and Corollary 14.3.7** close the section. The coupled construction of two copies
of the marks turns out to be an *ordinary* cascade on the pair mark space, whose mark law is the
diagonal below level `r` and the product above it, and whose parameters are the halved sequence
(14.48). Lemma 14.3.6 then says that the recursion of `F̂ = F¹ + F²` is the square of the
recursion of `F`, and the coupled tilting weights are the single weight below level `r` and the
product of the two weights above it. Corollary 14.3.7 follows: the coupled tilted average is the
tilted average of that ordinary cascade, so (14.27) applies to it and rewrites the right-hand
side of Theorem 14.3.5 as a cascade Gibbs average. That is the entry point of §14.5. The exponent has to be free because at the higher levels of the cascade the
sub-partition functions enter with the power `m_p`. The proof is an induction on the number of
levels from a new **one-level identity with two insertions**,
`𝔼 (∑ u A)² (∑ u V)^{a-2} = K₀(a) (∫ A V^{m-1})² + K₂(a) ∫ A² V^{m-2}`, whose two constants are,
relative to the moment `𝔼 (∑ u V)^a`, the complementary weights `(m-a)/(1-a)` and `(1-m)/(1-a)`.
That identity in turn needed two general tools, both new: the **bivariate Mecke equation**
(second-order Palm formula) for a Poisson point process, splitting a double sum over the points
into its off-diagonal and diagonal parts, derived from the one-point formula applied twice — in a
form stated at the level of the sample, which needs no measurability hypothesis beyond that of the
integrand, because the inner integrals are taken against counting measures (at the level of
`Measure E` the corresponding hypothesis is not available at all, the identity kernel not being
s-finite); and
the first-order **Palm–Campbell transform** of the Poisson–Dirichlet intensity, which converts
each of the two inserted points of the off-diagonal term into a first-order factor. The
off-diagonal term is proved for a general function of the *pair* of inserted marks, where it is
an integral against the product of two copies of the first-order Palm measure — the form Theorem
14.3.5 will need.

Still to discharge (there is no statement layer of undischarged `Prop`s): the **lower half** of
the Parisi formula. Talagrand's route to it stays inside Chapter 14 and does *not* need
Chapter 15; Panchenko's ultrametricity (§15.6) and the Dovbysh–Sudakov representation (§15.9)
are needed for the structure theory of Chapter 15 and give an alternative route via
Aizenman–Sims–Starr (§15.8). Done on that route: Theorem 13.1.6, all of §14.3 through
Corollary 14.3.7, and all of §14.6 through Proposition 14.6.3 — (14.147) for nondecreasing
`0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1` with free top values `ρ_{κ+1}`, its specialization to the coupling
(14.155)–(14.158) with the extra field of (14.160), and the identification of its right-hand side
at `λ = 0` with `2𝒫_k(m, q)`, so that the constrained pair pressure at `u = q_τ ≥ 0` is at most
`2𝒫_k(m, q)` at every `N`; and, from the derivative of the recursion in a parameter, `Y₀(λ)` is
differentiable with `|Y₀'| ≤ 1`, and Lemma 14.6.5, `0 ≤ Y₀'' ≤ 1`, gives the two-sided tangent
bound `Y₀(0) + λY₀'(0) ≤ Y₀(λ) ≤ Y₀(0) + λY₀'(0) + λ²/2` used by the main estimate. Of §14.7,
the operator layer is in place: the heat semigroup and its PDE, `T_{m,v}` with (14.195)–(14.203),
Lemma 14.7.3 for every `m'`, the identification of the Parisi recursion with the iterated
Cole–Hopf transform (14.190)–(14.191), and the differentiation formula (14.215)/(14.217). Next:
the formula `Y₀'(0) = 𝔼(W₁ ⋯ W_{τ-1} D'_τ(ζ_τ)²)` of Proposition 14.6.4 (for `η = −1`, i.e.
`u < 0`, Talagrand only has `Y₀ ≤ 2X₀`, his Proposition 14.8.6), then (14.219)–(14.222) and
Proposition 14.7.5, Lemma 14.7.4 with `Φ(m, u)`, `U(v)` and `f(u)`, Theorem 14.5.7 (the mass of
the window `R_{1,2} = u`), and the main estimate of §14.8–§14.10. Also open: Theorem 14.4.4 (`ξ` convex on `ℝ⁺`
only), the extension of (14.90) to `0 ≤ m₁ ≤ ⋯ ≤ m_k ≤ 1`, the Parisi measures of §14.11, Gardner,
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
