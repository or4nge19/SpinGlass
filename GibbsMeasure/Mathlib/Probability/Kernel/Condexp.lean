import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional expectation kernel: public re-exports

This file is a small shim around Mathlib's `Mathlib.Probability.Kernel.Condexp`.

It exists so the GibbsMeasure development can import a *stable* local entry-point for the
regular conditional distribution kernel (`ProbabilityTheory.condExpKernel`) and its core
identities (composition with `trim`, agreement with `condExp`, ...).
-/

open scoped ProbabilityTheory

export ProbabilityTheory
  (condExpKernel
    condExpKernel_comp_trim
    measurable_condExpKernel
    stronglyMeasurable_condExpKernel
    condExpKernel_ae_eq_condExp
    condExpKernel_ae_eq_trim_condExp
    condExp_ae_eq_integral_condExpKernel)

