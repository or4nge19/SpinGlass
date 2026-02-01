# GibbsMeasure

Lean 4 development of **DLR specifications and Gibbs measures** in the sense of Georgii (with the aim of supporting the formalization of Talagrand, Vol. 2).

This is an **independent library** inside this repository (`[[lean_lib]] name = "GibbsMeasure"` in `lakefile.toml`), alongside the finite-volume mean-field calculus developed in `SpinGlass/`.

## Entry points

- `GibbsMeasure/Specification.lean`: core definitions of **specifications** (`Specification`) and the Gibbs/DLR fixed-point notion (`Specification.IsGibbsMeasure`), plus basic structure classes such as `Specification.IsProper` and `Specification.IsMarkov`.
- `GibbsMeasure/Specification/Structure.lean`: “state-space” layer for Georgii Ch. 7 style structure theory, e.g. the Gibbs state space `GP γ` and the tail σ-algebra.
- `GibbsMeasure/Specification/ErgodicDecomposition.lean`, `GibbsMeasure/Specification/ChoquetLaw.lean`: law-level / Choquet-style statements for tail disintegrations and extremality vs tail-triviality (developed with countable cores to avoid unmotivated topological hypotheses).

## Library map (high level)

- **Topology / configuration spaces**
  - `GibbsMeasure/Topology/ConfigurationSpace.lean`, `.../LocalConvergence.lean`
- **Prerequisites (kernels, conditional expectation, cylinder σ-algebras, filtrations)**
  - `GibbsMeasure/Prereqs/CylinderEvents.lean`
  - `GibbsMeasure/Prereqs/Kernel/*` (conditional expectation kernels, proper kernels, Feller kernels)
  - `GibbsMeasure/Prereqs/LebesgueCondExp.lean`
  - `GibbsMeasure/Prereqs/Filtration/Consistent.lean`
- **Specifications and Gibbs measures**
  - `GibbsMeasure/Specification.lean` (core definition layer)
  - `GibbsMeasure/Specification/*` (quasilocality, extremality, existence, ergodic/Choquet structure)
- **Potentials (interaction representation)**
  - `GibbsMeasure/Potential.lean`
- **Examples**
  - `GibbsMeasure/SpinGlass.lean` (example: SK-style potential on a finite set of vertices)

## “Mathlib” shim folder

`GibbsMeasure/Mathlib/` contains `.lean` files that patch/extend Mathlib APIs needed by the library (similar to `SpinGlass/Mathlib/README.md`).

## Build

Toolchain: see the repo’s `lean-toolchain`.

From the repository root:

```bash
lake build GibbsMeasure
```

## Importing

In a Lean file within this repo:

```lean
import GibbsMeasure.Specification
-- or finer-grained imports, e.g.
import GibbsMeasure.Specification.Structure
```

