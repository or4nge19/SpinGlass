import SpinGlass.Papers.Triviality4D.RandomCurrentSwitching
import SpinGlass.Papers.Triviality4D.RandomCurrentConnectivity

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

/-! ## (orgaf) Correlation ratio as a pair-current event -/

/--
Paper equation (orgaf) in finite volume, in definition-level form:
\[
\frac{\langle \sigma_A\rangle_{\Lambda,\beta}\,\langle \sigma_B\rangle_{\Lambda,\beta}}
     {\langle \sigma_{A\Delta B}\rangle_{\Lambda,\beta}}
= \mathbf P_{\Lambda,\beta}^{A\Delta B,\varnothing}\big[\n_1+\n_2\in \mathcal F_B\big].
\]

Here the RHS is the normalized weight ratio `PPairReal` applied to the event
`HasSubCurrent n B` (existence of a `B`-sourced subcurrent of the total current).
-/
theorem isingCorr_mul_isingCorr_div_isingCorr_symmDiff_eq_PPairReal_hasSubCurrent
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    (isingCorr (V := V) (Λ := Λ) β J A * isingCorr (V := V) (Λ := Λ) β J B) /
        isingCorr (V := V) (Λ := Λ) β J (symmDiff A B)
      =
      PPairReal (V := V) (Λ := Λ) β J (symmDiff A B) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B} := by
  -- rewrite both sides in terms of `ZReal`, then simplify
  have hA :
      isingCorr (V := V) (Λ := Λ) β J A =
        ZReal (V := V) (Λ := Λ) β J A / ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) A
  have hB :
      isingCorr (V := V) (Λ := Λ) β J B =
        ZReal (V := V) (Λ := Λ) β J B / ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) B
  have hAB :
      isingCorr (V := V) (Λ := Λ) β J (symmDiff A B) =
        ZReal (V := V) (Λ := Λ) β J (symmDiff A B) /
          ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) (symmDiff A B)
  -- compare with the switching lemma ratio packaged as `PPairReal`
  have hPP :
      PPairReal (V := V) (Λ := Λ) β J (symmDiff A B) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}
        =
        (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) /
          (ZReal (V := V) (Λ := Λ) β J (symmDiff A B) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) :=
    (PPairReal_hasSubCurrent_eq_ZReal_ratio (V := V) (Λ := Λ) (β := β) (J := J) A B)
  -- now it is just commutative-field algebra (valid even if denominators are zero)
  -- We rewrite the LHS ratio into the same `ZReal` ratio as `hPP`.
  -- (Use `mul_div_mul_comm` to factor the product of divisions.)
  calc
    (isingCorr (V := V) (Λ := Λ) β J A * isingCorr (V := V) (Λ := Λ) β J B) /
        isingCorr (V := V) (Λ := Λ) β J (symmDiff A B)
        =
        ((ZReal (V := V) (Λ := Λ) β J A / ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) *
            (ZReal (V := V) (Λ := Λ) β J B / ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)))) /
          (ZReal (V := V) (Λ := Λ) β J (symmDiff A B) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
          simp [hA, hB, hAB]
    _ = (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) /
          (ZReal (V := V) (Λ := Λ) β J (symmDiff A B) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
          -- Pure algebra in a commutative field, valid without nonzero assumptions since `inv 0 = 0`.
          set ZA : ℝ := ZReal (V := V) (Λ := Λ) β J A
          set ZB : ℝ := ZReal (V := V) (Λ := Λ) β J B
          set Z0 : ℝ := ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
          set ZAB : ℝ := ZReal (V := V) (Λ := Λ) β J (symmDiff A B)
          have hnum : (ZA / Z0) * (ZB / Z0) = (ZA * ZB) / (Z0 * Z0) := by
            simpa using (mul_div_mul_comm ZA ZB Z0 Z0).symm
          have hden : (Z0 * Z0) / Z0 = Z0 := by
            -- `(Z0 * Z0) / Z0 = Z0 * Z0 * Z0⁻¹ = Z0`
            simpa [div_eq_mul_inv, mul_assoc] using (mul_self_mul_inv (a := Z0))
          -- rearrange the nested divisions, then collapse `(Z0 * Z0) / Z0` and use `div_div`
          calc
            ((ZA / Z0) * (ZB / Z0)) / (ZAB / Z0)
                = ((ZA * ZB) / (Z0 * Z0)) / (ZAB / Z0) := by
                    simp [hnum]
            _ = (ZA * ZB) / ZAB / ((Z0 * Z0) / Z0) := by
                    simpa using (div_div_div_comm (a := ZA * ZB) (b := Z0 * Z0) (c := ZAB) (d := Z0))
            _ = (ZA * ZB) / ZAB / Z0 := by
                    simp [hden]
            _ = (ZA * ZB) / (ZAB * Z0) := by
                    simpa using (div_div (a := ZA * ZB) (b := ZAB) (c := Z0))
    _ = PPairReal (V := V) (Λ := Λ) β J (symmDiff A B) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B} := by
          exact hPP.symm

/-! ## Two-point connectivity under sourceless pair law -/

/--
For distinct vertices `x ≠ y`, the event `Connected n x y` for the **total** current under two
independent sourceless currents has normalized weight ratio equal to the square of the two-point
correlation.

This is the classical “random current connectivity” identity
\[
 \langle \sigma_x\sigma_y\rangle^2 = \mathbb P^{\varnothing,\varnothing}(x \leftrightarrow y),
\]
with `PPairReal` as the definition-level normalized ratio and `Connected` taken in the trace graph of
the total current.
-/
theorem PPairReal_connected_eq_isingCorr_sq
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ} (hxy : x ≠ y) :
    PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y}
      =
      (isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) ^ 2 := by
  classical
  -- use switching lemma with `A = B = {x,y}` and rewrite `HasSubCurrent` as connectivity
  have hPP :
      PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ))}
        =
        (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) /
          (ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
    simpa using
      (PPairReal_hasSubCurrent_eq_ZReal_ratio (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, y} : Finset (↥Λ))) (B := ({x, y} : Finset (↥Λ))))
  -- rewrite the event using `HasSubCurrent {x,y} ↔ Connected x y`
  have hSet :
      ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ))}) =
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y} := by
    ext n
    simpa using
      (hasSubCurrent_pair_iff_connected (V := V) (Λ := Λ) n (hxy := hxy))
  -- combine with the random-current representation `⟨σ_{x}σ_{y}⟩ = Z_{xy} / Z_∅`
  have hCorr :
      isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) =
        ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
          ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, y} : Finset (↥Λ))
  -- finish by rewriting and simplifying powers
  calc
    PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y}
        =
        PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ))} := by
          simp [hSet.symm]
    _ = (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) /
          (ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := hPP
    _ = (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) *
          (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
          simp [mul_div_mul_comm]
    _ = (isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) ^ 2 := by
          -- `pow_two` turns `t ^ 2` into `t * t`
          simp [hCorr, pow_two]

end RandomCurrent

end SpinGlass.Papers.Triviality4D

