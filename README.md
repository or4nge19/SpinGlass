# SpinGlass

Lean 4 formalization of Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II. Mathlib-grade:
canonical statements, no extra hypotheses, no local trivializations, no `sorry`.

Thermodynamic objects are finite-volume Gibbs calculus and replica/overlap laws (Parisi, GG, cascades),
not DLR specifications.

## Scope

**In.** SK / mixed \(p\)-spin, perceptron/Gardner, Hopfield, Guerra interpolation, cavity, GG,
Poisson–Dirichlet cascades, Parisi formula. Vol. I models are instances of the Vol. II
Gaussian-process / covariance language.

**Out.** Lattice DLR/Georgii, 4D triviality / random currents, arithmetic models, extra Lake pins.
DLR: [`or4nge19/GibbsMeasure@mc3`](https://github.com/or4nge19/GibbsMeasure/tree/mc3) (not a
dependency). 4D: `Annals` branch if needed.

Plans: `Notes/Vol1##.md`, `Notes/Vol2##.md`. Index: `SpinGlass.Talagrand.MainResults`.
Book extracts are local and gitignored (`.axiomatic/`).

## Architecture

On a finite type `α`, Hamiltonians live in `EnergySpace α := PiLp 2 (fun _ : α => ℝ)`:

- `Z H := ∑ σ, Real.exp (-H σ)`
- `gibbs_pmf H σ := Real.exp (-H σ) / Z H`
- `free_energy_density n H := n⁻¹ * Real.log (Z H)`

`SpinGlass.FiniteGibbs` develops Fréchet calculus once (Hessian = covariance). SK, Hopfield, mixed
\(p\)-spin instantiate it. Gaussians are intrinsic (`IsGaussian`) via Cameron–Martin / covariance
IBP in `Common.Mathlib.Probability.Distributions.Gaussian.*`.

## Entry points

| Import | Content |
|---|---|
| `SpinGlass` | full library |
| `SpinGlass.FiniteGibbs` | finite Gibbs calculus |
| `SpinGlass.GuerraPipeline` | smart path → IBP → trace/Hessian |
| `SpinGlass.Talagrand.MainResults` | theorem index |
| `*.Gaussian.CameronMartinAPI` | Cameron–Martin / Fernique / IBP |
| `*.Gaussian_IBP_HilbertAPI` | Hilbert covariance IBP |

## Build

Lean / Mathlib `v4.34.0-rc2`. Mathlib is the only Lake dependency.

```bash
lake exe cache get
lake build
```

## References

M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II.
