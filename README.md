# SpinGlass

This repository contains two Lean 4 libraries:

- `SpinGlass`: finite-volume mean-field spin glass calculus (Talagrand, Vol. I–II).
- `GibbsMeasure`: DLR specifications and infinite-volume Gibbs measures (Georgii; Talagrand,
  Vol. II). See the original repository at https://github.com/james18lpc/GibbsMeasure and `GibbsMeasure/README.md`.

## Overview

Finite-volume thermodynamic functionals depend only on a finite configuration space `α` and a
Hamiltonian `H : α → ℝ`. In `SpinGlass.FiniteGibbs` the basic objects are:

- `Z H := ∑ σ : α, Real.exp (-H σ)` (partition function),
- `gibbs_pmf H σ := Real.exp (-H σ) / Z H` (Gibbs weight),
- `free_energy_density n H := (1 / (n : ℝ)) * Real.log (Z H)`
  (free energy density; explicit scaling `n : ℕ`).

The folder `SpinGlass/FiniteGibbs/*` develops the Fréchet calculus of `F_n` in the Hilbert space
`EnergySpace α := PiLp 2 (fun _ : α => ℝ)` and exports it for subsequent instantiations
(`Config N`, cascades, …).

Gaussian integration by parts is used through an intrinsic Cameron–Martin interface
(`ProbabilityTheory.IsGaussian μ`), with the Hilbert/covariance-operator formulation as the
main entry point for interpolation arguments.

## Design choices

- Finite-volume calculus is developed once (configuration-agnostic) in `SpinGlass.FiniteGibbs`.
- Gaussian analysis is phrased intrinsically in terms of laws (`ProbabilityTheory.IsGaussian`) and
  growth hypotheses; integrability is discharged via Fernique-type lemmas.
- Random Hamiltonians are specified via covariance identities on the canonical basis, so that
  comparison/interpolation statements are kernel-level.
- Interpolation arguments are stratified into dominated differentiation, Gaussian IBP, and a
  finite-dimensional algebraic layer (trace/Hessian identities).

## Entry points

- `import SpinGlass` re-exports the full development (and currently also imports `GibbsMeasure`).
- For the finite-configuration calculus: `import SpinGlass.FiniteGibbs`.
- For the Guerra interpolation pipeline: `import SpinGlass.GuerraPipeline`.
- For the DLR/specification library: `import GibbsMeasure`.

Gaussian analysis entry points:

- Banach/Cameron–Martin API:
  `import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinAPI`.
- Hilbert-space IBP (covariance operator):
  `import Common.Mathlib.Probability.Distributions.Gaussian_IBP_HilbertAPI`.
- One-dimensional corollaries for `gaussianReal`:
  `import Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts`.

## Library map

### Configuration-agnostic finite Gibbs calculus (`SpinGlass.FiniteGibbs`)

Namespace: `SpinGlass.FiniteGibbs`. Files:

- `SpinGlass/FiniteGibbs.lean`
- `SpinGlass/FiniteGibbs/Calculus.lean`
- `SpinGlass/FiniteGibbs/Integrability.lean`
- `SpinGlass/FiniteGibbs/GibbsMeasure.lean`

- `SpinGlass/FiniteGibbs.lean`:
  partition function `FiniteGibbs.Z`, Gibbs weights `FiniteGibbs.gibbs_pmf`,
  free energy density `FiniteGibbs.free_energy_density`, Fréchet derivatives,
  Hessian/covariance identity, and `FiniteGibbs.trace_formula`.
- `SpinGlass/FiniteGibbs/Calculus.lean`:
  `ContDiff` regularity, chain rule, and derivative/Lipschitz bounds.
- `SpinGlass/FiniteGibbs/Integrability.lean`:
  integrability of `free_energy_density` under Gaussian pushforward laws.
- `SpinGlass/FiniteGibbs/GibbsMeasure.lean`:
  the atomic probability measure `FiniteGibbs.gibbsMeasure` and its integral lemmas.

### SK model and Guerra interpolation (finite `N`)

- `SpinGlass/Defs.lean`:
  specialization to `Config N := Fin N → Bool`, overlaps and covariance kernels,
  trace computations, and the algebraic core identity of Guerra’s bound.
- `SpinGlass/Calculus.lean`:
  specialization of the `FiniteGibbs` calculus to `Config N`
  (smoothness, Hessian = covariance).
- `SpinGlass/SKModel.lean`:
  Gaussian disorder structures `SKDisorder` and `SimpleDisorder`,
  the product disorder space `DisorderSpace`, and the intrinsic law `disorderPairLaw`.
- `SpinGlass/GuerraInterpolation.lean`:
  dominated differentiation for the expected free energy along the smart path.
- `SpinGlass/GuerraIBP.lean`:
  Gaussian IBP rewrite of the derivative value on `disorderPairLaw`.
- `SpinGlass/GuerraTrace.lean`:
  conversion of the IBP expression to Talagrand’s trace/Hessian form.
- `SpinGlass/GuerraPipeline.lean`:
  a packaged `HasDerivAt` theorem combining the previous steps.
- `SpinGlass/Replicas.lean`:
  replica calculus and reusable IBP lemmas on `disorderPairLaw` in polynomial-growth form.

### Hopfield

- `SpinGlass/Hopfield.lean`:
  finite-volume Hopfield Hamiltonian and Hubbard–Stratonovich linearization.
- `SpinGlass/HopfieldFixedPoint.lean`:
  existence and a canonical choice of a fixed point of `m ↦ tanh (β m + h)`.

### Gaussian/Cameron–Martin toolkit (local Mathlib extensions)

- `Common/Mathlib/Probability/Distributions/Gaussian/CameronMartinAPI.lean`:
  public API for Cameron–Martin theorem, Fernique integrability, and IBP.
- `Common/Mathlib/Probability/Distributions/Gaussian_IBP_HilbertAPI.lean`:
  Hilbert-space IBP in covariance-operator form.
- `Common/Mathlib/Probability/Distributions/GaussianIntegrationByParts.lean`:
  one-dimensional Gaussian IBP corollaries.

### `GibbsMeasure` (DLR / infinite volume)

See `GibbsMeasure/README.md` for entry points and a file map.

## Selected results (as Lean declarations)

- Finite Gibbs calculus:
  `SpinGlass.FiniteGibbs.fderiv_free_energy_density_apply`,
  `SpinGlass.FiniteGibbs.hessian_free_energy_fderiv_eq_hessian_free_energy`,
  `SpinGlass.FiniteGibbs.trace_formula`.
- Hilbert-space Gaussian IBP:
  `ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth`.
- Guerra pipeline (derivative in trace/Hessian form):
  `SpinGlass.hasDerivAt_guerraPhi_eq_trace_integral`.
- SK trace computations and algebraic core:
  `SpinGlass.trace_sk`, `SpinGlass.trace_simple`,
  `SpinGlass.guerra_derivative_bound_algebra_core`.
- Hopfield prerequisites:
  `SpinGlass.hubbardStratonovich_hopfield`,
  `SpinGlass.hopfield_mStar_eq_tanh`.

## Planned developments

Targets and intended formal statements are tracked in `Notes/Vol1##.md`, `Notes/Vol2##.md`,
and indexed in `SpinGlass/Talagrand/MainResults.lean`. Near-term goals include:

- Guerra–Toninelli: existence of the thermodynamic limit of the quenched free energy.
- Concentration and replica identities (Ghirlanda–Guerra, etc.) in the intrinsic Gaussian
  framework.
- Parisi functional and comparison theorems in a covariance-first formulation.
- Hopfield localization and related main theorems (Talagrand; Bovier–Gayrard).

## Build

Toolchain: see `lean-toolchain`.

```bash
lake build
# or:
lake build SpinGlass
lake build GibbsMeasure
```
