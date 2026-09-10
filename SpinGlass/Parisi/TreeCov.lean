/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.TreeField

/-!
# The tree covariance telescopes to `ξ'(q_{(α,γ)})`

Talagrand, Vol. II, (14.74): two branches `α, γ` agree on their first `(α,γ) - 1` levels, and
`∑_{p < (α,γ)} 𝔼 z_p² = ξ'(q_{(α,γ)})` for the variances `𝔼 z_p² = ξ'(q_{p+1}) - ξ'(q_p)` of
(14.72), since `q₀ = 0` and `ξ'(0) = 0`. Here the number of agreeing levels is `branchLevel α γ`
(the agreeing levels form an initial segment, `branchNode_eq_iff_lt_branchLevel`), and
`treeCov_eq_deriv` is the telescoping identity for the variances `parisiVar`, exact when `ξ'` is
nondecreasing on `[0,1]` and `q` is nondecreasing. Hence the kernel of the marks field is the tree
kernel `N R_{στ} ξ'(q_{(α,γ)})` (`treeFieldKernel_eq_treeKernel`).
-/

open Finset
open scoped BigOperators NNReal

namespace SpinGlass

noncomputable section

variable {N k M : ℕ}

omit N in
/-- Agreement of two branches at level `p` means agreement at every level `≤ p`. -/
lemma branchNode_eq_iff' (α γ : TruncBranch k M) (p : Fin k) :
    branchNode k M α p = branchNode k M γ p ↔ ∀ i : Fin k, i ≤ p → α i = γ i := by
  rw [branchNode_eq_iff]
  constructor
  · intro h i hi
    have := congrFun h ⟨i.val, by omega⟩
    simpa using this
  · intro h
    funext i
    exact h ⟨i.val, by omega⟩ (Fin.mk_le_mk.2 (by omega))

/-- The number of levels on which two branches agree, `(α, γ) - 1` in Talagrand's notation. -/
def branchLevel (α γ : TruncBranch k M) : ℕ :=
  (univ.filter fun p : Fin k => branchNode k M α p = branchNode k M γ p).card

omit N in
lemma branchLevel_le (α γ : TruncBranch k M) : branchLevel α γ ≤ k :=
  (card_le_univ _).trans (by simp)

omit N in
/-- The agreeing levels form an initial segment. -/
lemma branchNode_eq_iff_lt_branchLevel (α γ : TruncBranch k M) (p : Fin k) :
    branchNode k M α p = branchNode k M γ p ↔ p.val < branchLevel α γ := by
  classical
  set S := univ.filter fun p : Fin k => branchNode k M α p = branchNode k M γ p with hS
  have hdown : ∀ p q : Fin k, q ≤ p → p ∈ S → q ∈ S := by
    intro p q hqp hp
    simp only [hS, mem_filter, mem_univ, true_and] at hp ⊢
    rw [branchNode_eq_iff'] at hp ⊢
    exact fun i hi => hp i (hi.trans hqp)
  have hmem : p ∈ S ↔ branchNode k M α p = branchNode k M γ p := by simp [hS]
  rw [← hmem]
  show p ∈ S ↔ p.val < S.card
  constructor
  · intro hp
    have hsub : Iic p ⊆ S := fun q hq => hdown p q (mem_Iic.1 hq) hp
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hp
    by_contra hnot
    have hsub : S ⊆ Iio p := by
      intro q hq
      rw [mem_Iio]
      by_contra hle
      exact hnot (hdown q p (not_lt.1 hle) hq)
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

omit N in
lemma branchLevel_self (α : TruncBranch k M) : branchLevel α α = k := by
  unfold branchLevel
  simp

/-! ### The telescoping identity -/

/-- The tree covariance for the Parisi variances telescopes:
`v₀ + ∑_{p < (α,γ)-1} v_p = ξ'(q_{(α,γ)}) - ξ'(q₀)`, when the variances are exact. -/
theorem treeCov_eq_deriv (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (α γ : TruncBranch k M) :
    treeCov k M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)) α γ
      = deriv ξ (qExt qs (branchLevel α γ + 1)) - deriv ξ (qExt qs 0) := by
  classical
  unfold treeCov
  have hvar : ∀ r, r ≤ k + 1 → (parisiVar ξ qs r : ℝ)
      = deriv ξ (qExt qs (r + 1)) - deriv ξ (qExt qs r) := by
    intro r hr
    unfold parisiVar
    exact Real.coe_toNNReal _ (sub_nonneg.2 (hmono r hr))
  simp_rw [branchNode_eq_iff_lt_branchLevel]
  have hlev := branchLevel_le α γ
  rw [hvar 0 (by omega)]
  have hsum : (∑ p : Fin k, if p.val < branchLevel α γ then (parisiVar ξ qs (p.val + 1) : ℝ) else 0)
      = ∑ i ∈ range (branchLevel α γ), (parisiVar ξ qs (i + 1) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < branchLevel α γ
      then (parisiVar ξ qs (i + 1) : ℝ) else 0) k, ← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [hsum]
  have hterm : ∀ i ∈ range (branchLevel α γ), (parisiVar ξ qs (i + 1) : ℝ)
      = deriv ξ (qExt qs (i + 1 + 1)) - deriv ξ (qExt qs (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    exact hvar (i + 1) (by omega)
  rw [sum_congr rfl hterm, sum_range_sub (fun i => deriv ξ (qExt qs (i + 1)))]
  ring

/-- The overlap `(α, γ)` of Talagrand's tree, as a value of `q`: `q_{(α,γ)}`. -/
def treeOverlap (qs : Fin (k + 1) → ℝ) (α γ : TruncBranch k M) : ℝ :=
  qExt qs (branchLevel α γ + 1)

omit N in
lemma treeOverlap_self (qs : Fin (k + 1) → ℝ) (α : TruncBranch k M) :
    treeOverlap qs α α = qs (Fin.last k) := by
  unfold treeOverlap
  rw [branchLevel_self, qExt_succ_of_lt qs (Nat.lt_succ_self k)]
  rfl

/-- **The kernel of the marks field is the tree kernel** `N R_{στ} ξ'(q_{(α,γ)})` when
`ξ'(0) = 0`. -/
theorem treeFieldKernel_eq_treeKernel (hN : 0 < N) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (h0 : deriv ξ 0 = 0) :
    treeFieldKernel N k M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
      = treeKernel N ξ (treeOverlap qs) := by
  funext x y
  unfold treeFieldKernel treeKernel treeOverlap
  rw [treeCov_eq_deriv ξ qs hmono, qExt_zero, h0, sub_zero]
  have hR : (∑ i, isingSpin (x.1 i) * isingSpin (y.1 i)) = (N : ℝ) * overlap N x.1 y.1 := by
    unfold overlap overlapOf spinOf
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  rw [hR]

end

end SpinGlass
