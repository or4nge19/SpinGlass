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

Cascades, `Parisi.T`, and the finite-volume GG defect/error are scaffolding toward the Vol. II
capstones. Still to discharge: the self-averaging of a disorder component (§12.1 run along the
interpolation above), and with it the identities at all monomial test functions in the limit;
Panchenko's ultrametricity theorem (Talagrand's Research Problem 15.3.7), the Dovbysh–Sudakov
representation, the Parisi equality, broken-RSB Guerra, Gardner and the Hopfield limits.

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
