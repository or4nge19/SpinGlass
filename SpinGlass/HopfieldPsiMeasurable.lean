import SpinGlass.Hopfield

/-!
# Hopfield `ψ`: basic measurability lemmas

These are small prerequisites for later “Vol II style” arguments where Hopfield laws are expressed
via densities involving `Real.exp (hopfieldPsi …)`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N M : ℕ}

@[fun_prop] lemma measurable_hopfieldEtaDot (Ξ : Patterns N M) (i : Fin N) :
    Measurable (hopfieldEtaDot (N := N) (M := M) Ξ i) := by
  -- finite sum of measurable coordinate maps
  classical
  unfold hopfieldEtaDot
  -- each summand is `z ↦ const * z k`
  fun_prop

@[fun_prop] lemma measurable_hopfieldPsi (β h : ℝ) (Ξ : Patterns N M) :
    Measurable (hopfieldPsi (N := N) (M := M) β h Ξ) := by
  classical
  -- unfold and use closure of measurability under +, *, finite sums and compositions
  unfold hopfieldPsi
  have hnorm : Measurable (finVecNormSq M) := measurable_finVecNormSq (M := M)
  have hlogcosh :
      ∀ i : Fin N,
        Measurable fun z : Fin M → ℝ =>
          Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)) := by
    intro i
    have hη : Measurable (hopfieldEtaDot (N := N) (M := M) Ξ i) :=
      measurable_hopfieldEtaDot (N := N) (M := M) Ξ i
    fun_prop [hη]
  -- now a finite sum of the `logcosh` terms
  have hsum :
      Measurable fun z : Fin M → ℝ =>
        ∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)) := by
    simpa using (Finset.measurable_sum (s := (Finset.univ : Finset (Fin N))) (by
      intro i _hi
      simpa using hlogcosh i))
  -- assemble
  fun_prop [hnorm, hsum]

@[fun_prop] lemma measurable_exp_hopfieldPsi (β h : ℝ) (Ξ : Patterns N M) :
    Measurable fun z : Fin M → ℝ => Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := by
  have hψ : Measurable (hopfieldPsi (N := N) (M := M) β h Ξ) := measurable_hopfieldPsi (N := N) (M := M) (β := β) (h := h) Ξ
  fun_prop [hψ]

end SpinGlass

