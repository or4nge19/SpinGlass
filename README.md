# SpinGlass

Lean 4 formalization of Talagrand, *Mean Field Models for Spin Glasses*, Vol. I–II.

SK / mixed \(p\)-spin, perceptron/Gardner, Hopfield, Guerra interpolation, cavity, Ghirlanda–Guerra,
Poisson–Dirichlet cascades, Parisi formula.

## Architecture

On a finite type `α`, `EnergySpace α := PiLp 2 (fun _ : α => ℝ)` carries Hamiltonians; Gibbs weights,
free energy, and replica measures are built from `Real.logSumExp` / softmax. `SpinGlass.FiniteGibbs`
is the shared calculus layer; SK, Hopfield, and mixed \(p\)-spin are instances. Gaussian IBP and
comparison live in `Common.Mathlib.Probability.Distributions.Gaussian.*`.

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
