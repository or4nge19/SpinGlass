# SpinGlass

Lean 4 formalization of Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II. Mathlib-grade:
canonical statements, no extra hypotheses, no local trivializations, no `sorry`.

Thermodynamic objects are finite-volume Gibbs calculus and replica/overlap laws (Parisi, GG, cascades),
not DLR specifications.

## Scope

SK / mixed \(p\)-spin, perceptron/Gardner, Hopfield, Guerra interpolation, cavity, GG,
Poisson–Dirichlet cascades, Parisi formula. Vol. I models are instances of the Vol. II
Gaussian-process / covariance language.

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

## Acknowledgements

Cameron–Martin in `Common/Mathlib/Probability/Distributions/Gaussian/` is adapted from Rémy
Degenne’s mathlib4 PRs
[#26291](https://github.com/leanprover-community/mathlib4/pull/26291) (open as of 2026-01),
[#30582](https://github.com/leanprover-community/mathlib4/pull/30582), and
[#27608](https://github.com/leanprover-community/mathlib4/pull/27608).
Fernique is in Mathlib ([#24430](https://github.com/leanprover-community/mathlib4/pull/24430)).

## References

Primary mathematical sources:

- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II (Springer, 2010/2011).
- M. Talagrand, [The Parisi formula](https://annals.math.princeton.edu/2006/163-1/p04),
  *Annals of Mathematics* **163** (2006), 221–263.
  [doi:10.4007/annals.2006.163.221](https://doi.org/10.4007/annals.2006.163.221)
- D. Panchenko, [The Parisi ultrametricity conjecture](https://annals.math.princeton.edu/2013/177-1/p08),
  *Annals of Mathematics* **177** (2013), 383–393.
  [doi:10.4007/annals.2013.177.1.8](https://doi.org/10.4007/annals.2013.177.1.8)

## How to cite

Please cite this repository as:

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
