import SpinGlass.Papers.Triviality4D.RandomCurrentSwitching

/-!
# Random current consequences (finite volume)

This file records paper-facing corollaries of the finite-volume switching lemma, in the real-weight
setup (`weightReal`, `ZReal`).

In particular, we package the RHS of the switching lemma as a *normalized weight ratio* (a
“probability” once one shows the denominator is nonzero and weights are nonnegative).
-/

open scoped BigOperators Topology

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/--
Normalized weight ratio of a total-current event `S` under the **pair** current law with sources
`(A,B)`:
\[
\frac{\sum_{∂n_1=A,∂n_2=B} w(n_1)w(n_2)\,\mathbf 1_{(n_1+n_2)\in S}}
     {Z_A Z_B}.
\]

This is a definition-level object: without additional hypotheses, it is not yet a genuine probability.
-/
noncomputable def PPairReal
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ)) : ℝ :=
  (∑' p : Current (V := V) Λ × Current (V := V) Λ,
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
        S.indicator
          (fun _n =>
            weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2)
          (p.1 + p.2)
      else 0) /
    (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B)

/--
Switching lemma, packaged as a normalized weight ratio: the total-current event `ℱ_B` (existence of a
`B`-sourced subcurrent) under sources `(AΔB, ∅)` has weight ratio
\[
\frac{Z_A Z_B}{Z_{A\Delta B} Z_{\emptyset}}.
\]
-/
theorem PPairReal_hasSubCurrent_eq_ZReal_ratio
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    PPairReal (V := V) (Λ := Λ) β J (symmDiff A B) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}
      =
      (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) /
        (ZReal (V := V) (Λ := Λ) β J (symmDiff A B) *
          ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
  classical
  -- rewrite the numerator using `switchingLemma_ZReal_mul`
  have hn :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
              (fun _n =>
                weightReal (V := V) (Λ := Λ) β J p.1 *
                  weightReal (V := V) (Λ := Λ) β J p.2)
              (p.1 + p.2)
          else 0)
        =
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B := by
    simpa using
      (switchingLemma_ZReal_mul (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)).symm
  -- now it is just rewriting the definition
  simp [PPairReal, hn]

end RandomCurrent

end SpinGlass.Papers.Triviality4D

