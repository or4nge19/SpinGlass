/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.GuerraParisi

/-!
# The infimum of the Parisi functional, and the upper half of the Parisi formula

Talagrand's **Parisi formula** (Vol. II, (14.93)) reads

`lim_{N → ∞} p_N = inf 𝒫_k(m, q)`,

the infimum being over all numbers of levels `k`, all `0 < m₁ < ⋯ < m_k < 1` and all
`0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`.

This file defines the right-hand side — `parisiInf`, the infimum of the set `parisiSet` of values
of the Parisi functional at admissible parameters — and proves the half of the formula that
follows from Guerra's broken replica-symmetry bound: `p_N ≤ inf 𝒫` at every finite `N`
(`mixedPSpinFreeEnergy_le_parisiInf`), hence in the thermodynamic limit
(`mixedPSpinFreeEnergyLimit_le_parisiInf`), and in particular for the Sherrington–Kirkpatrick
model (`skFreeEnergy_le_parisiInf`, `skFreeEnergyLimit_le_parisiInf`).

The reverse inequality is Talagrand's §14.5–§14.10 (or the Aizenman–Sims–Starr scheme of §15.8
together with Panchenko's ultrametricity), and is not yet formalized.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### Admissible parameters -/

/-- **The values of the Parisi functional at admissible parameters**: `0 < m₁ < ⋯ < m_k < 1`
(Talagrand's (14.69)) and a nondecreasing `q₁ ≤ ⋯ ≤ q_{k+1}` in `[0, 1]` (his (14.70), the
endpoints `q₀ = 0` and `q_{k+2} = 1` being built into `qExt`). -/
def parisiSet (ξ : ℝ → ℝ) (h : ℝ) : Set ℝ :=
  {y | ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      StrictMono ms ∧ (∀ i, 0 < ms i) ∧ (∀ i, ms i < 1) ∧
      Monotone qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1 ∧ y = parisiFunctional ξ h ms qs}

/-- **The right-hand side of the Parisi formula** (Talagrand Vol. II, (14.93)):
`inf 𝒫_k(m, q)` over all `k`, `m` and `q`. -/
def parisiInf (ξ : ℝ → ℝ) (h : ℝ) : ℝ := sInf (parisiSet ξ h)

lemma parisiFunctional_mem_parisiSet (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) :
    parisiFunctional ξ h ms qs ∈ parisiSet ξ h :=
  ⟨k, ms, qs, hsm, hpos, hlt, hqmono, hq0, hq1, rfl⟩

/-- The replica-symmetric parameters `k = 0`, `q₁ = 0` are admissible, so the set is nonempty. -/
lemma parisiSet_nonempty (ξ : ℝ → ℝ) (h : ℝ) : (parisiSet ξ h).Nonempty := by
  refine ⟨parisiFunctional ξ h (![] : Fin 0 → ℝ) ![0],
    parisiFunctional_mem_parisiSet ξ h (fun a _ _ => a.elim0) (fun i => i.elim0)
      (fun i => i.elim0) ?_ (by simp) (by simp)⟩
  intro a b _
  fin_cases a
  fin_cases b
  simp

/-- The infimum is attained as a lower bound of every admissible value. -/
lemma parisiInf_le (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hbdd : BddBelow (parisiSet ξ h)) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) :
    parisiInf ξ h ≤ parisiFunctional ξ h ms qs :=
  csInf_le hbdd (parisiFunctional_mem_parisiSet ξ h hsm hpos hlt hqmono hq0 hq1)

/-! ### The upper half of the Parisi formula -/

/-- **Guerra's bound, optimized over the parameters**: `p_N ≤ inf 𝒫_k(m, q)` at every finite `N`.
This is Talagrand Vol. II, Theorem 14.4.3 together with (14.93). -/
theorem mixedPSpinFreeEnergy_le_parisiInf (N : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiInf ξ h := by
  refine le_csInf (parisiSet_nonempty ξ h) ?_
  rintro y ⟨k, ms, qs, hsm, hpos, hlt, hqmono, hq0, hq1, rfl⟩
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN ξ hS hconv hdiff h0 qs
    hqmono hq0 hq1 ms hsm hpos hlt h

/-- Consequently the set of admissible values is bounded below. -/
lemma bddBelow_parisiSet {ξ : ℝ → ℝ} (hS : (overlapCovMatrix 1 ξ).PosSemidef)
    (hconv : ConvexOn ℝ univ ξ) (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (h : ℝ) :
    BddBelow (parisiSet ξ h) := by
  refine ⟨mixedPSpinFreeEnergy 1 ξ h, ?_⟩
  rintro y ⟨k, ms, qs, hsm, hpos, hlt, hqmono, hq0, hq1, rfl⟩
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn 1 k one_pos ξ hS hconv hdiff h0 qs
    hqmono hq0 hq1 ms hsm hpos hlt h

/-- **The upper half of the Parisi formula** (Talagrand Vol. II, (14.93)):
`lim_N p_N ≤ inf 𝒫_k(m, q)`. -/
theorem mixedPSpinFreeEnergyLimit_le_parisiInf {ξ : ℝ → ℝ}
    (hξ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ) (hPSD : ∀ N, (overlapCovMatrix N ξ).PosSemidef)
    (hconv : ConvexOn ℝ univ ξ) (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (h : ℝ) :
    mixedPSpinFreeEnergyLimit hξ hPSD h ≤ parisiInf ξ h := by
  refine le_csInf (parisiSet_nonempty ξ h) ?_
  rintro y ⟨k, ms, qs, hsm, hpos, hlt, hqmono, hq0, hq1, rfl⟩
  refine le_of_tendsto (tendsto_mixedPSpinFreeEnergy hξ hPSD h) ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN ξ (hPSD N) hconv hdiff h0 qs
    hqmono hq0 hq1 ms hsm hpos hlt h

/-! ### The Sherrington–Kirkpatrick model -/

/-- Guerra's bound for the SK model, optimized over the Parisi parameters. -/
theorem skFreeEnergy_le_parisiInf (N : ℕ) (hN : 0 < N) (β h : ℝ) :
    skFreeEnergy N β h ≤ parisiInf (skCovXi β) h := by
  change mixedPSpinFreeEnergy N (skCovXi β) h ≤ _
  exact mixedPSpinFreeEnergy_le_parisiInf N hN (skCovXi β) (posSemidef_skCovMatrix N β)
    (convexOn_univ_skCovXi β) (differentiable_skCovXi β) (deriv_skCovXi_zero β) h

/-- **The upper half of the Parisi formula for the SK model**:
`lim_N p_N(β, h) ≤ inf 𝒫_k(m, q)`. -/
theorem skFreeEnergyLimit_le_parisiInf (β h : ℝ) :
    skFreeEnergyLimit β h ≤ parisiInf (skCovXi β) h := by
  rw [skFreeEnergyLimit_eq_mixedPSpinFreeEnergyLimit β h]
  exact mixedPSpinFreeEnergyLimit_le_parisiInf _ _ (convexOn_univ_skCovXi β)
    (differentiable_skCovXi β) (deriv_skCovXi_zero β) h

end

end SpinGlass
