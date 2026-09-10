/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.GuerraRSB

/-!
# Exhausting the branches by the truncated trees

The branches of the tree truncated to indices `< M` (`TruncBranch k M`), as a finite set of
addresses `truncFinset k M ⊆ (Fin k → ℕ × ℕ)`, increase with `M` and exhaust the countable set
of all branches (`exists_subset_truncFinset`). Consequently every sum over the branches of a
nonnegative function is the monotone limit of its truncations (`tendsto_sum_truncFinset`,
`tendsto_sum_truncBranch`) — the form in which the limit `M → ∞` of Guerra's interpolation for
the truncated tree (`guerra_truncated`) is taken.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace SpinGlass

noncomputable section

variable (k M : ℕ)

lemma truncBranchCoe_injective : Function.Injective (truncBranchCoe k M) := by
  intro α β h
  funext i
  have := congrFun h i
  simp only [truncBranchCoe, Prod.mk.injEq] at this
  ext
  · exact_mod_cast this.1
  · exact_mod_cast this.2

/-- The branches of the truncated tree, as a finite set of addresses. -/
def truncFinset : Finset (Fin k → ℕ × ℕ) :=
  Finset.univ.map ⟨truncBranchCoe k M, truncBranchCoe_injective k M⟩

lemma mem_truncFinset_iff (α : Fin k → ℕ × ℕ) :
    α ∈ truncFinset k M ↔ ∀ i, (α i).1 < M ∧ (α i).2 < M := by
  constructor
  · rintro hα
    simp only [truncFinset, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hα
    obtain ⟨β, rfl⟩ := hα
    intro i
    exact ⟨(β i).1.isLt, (β i).2.isLt⟩
  · intro hα
    simp only [truncFinset, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    exact ⟨fun i => (⟨(α i).1, (hα i).1⟩, ⟨(α i).2, (hα i).2⟩), by funext i; rfl⟩

lemma truncFinset_mono {M M' : ℕ} (hM : M ≤ M') : truncFinset k M ⊆ truncFinset k M' := by
  intro α hα
  rw [mem_truncFinset_iff] at hα ⊢
  exact fun i => ⟨lt_of_lt_of_le (hα i).1 hM, lt_of_lt_of_le (hα i).2 hM⟩

/-- Every finite set of branches lies in some truncated tree. -/
lemma exists_subset_truncFinset (s : Finset (Fin k → ℕ × ℕ)) : ∃ M, s ⊆ truncFinset k M := by
  classical
  refine ⟨(s.sup fun α => Finset.univ.sup fun i => max (α i).1 (α i).2) + 1, fun α hα => ?_⟩
  rw [mem_truncFinset_iff]
  intro i
  have h1 : max (α i).1 (α i).2 ≤ s.sup fun α => Finset.univ.sup fun i => max (α i).1 (α i).2 :=
    (Finset.le_sup (f := fun i => max (α i).1 (α i).2) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun α => Finset.univ.sup fun i => max (α i).1 (α i).2) hα)
  constructor
  · omega
  · omega

/-- A sum over the branches is the supremum of its truncations. -/
lemma tsum_eq_iSup_truncFinset (f : (Fin k → ℕ × ℕ) → ℝ≥0∞) :
    ∑' α, f α = ⨆ M, ∑ α ∈ truncFinset k M, f α :=
  ENNReal.tsum_eq_iSup_sum' (truncFinset k) (exists_subset_truncFinset k)

/-- **Monotone convergence of the branch sums.** -/
lemma tendsto_sum_truncFinset (f : (Fin k → ℕ × ℕ) → ℝ≥0∞) :
    Tendsto (fun M => ∑ α ∈ truncFinset k M, f α) atTop (𝓝 (∑' α, f α)) := by
  rw [tsum_eq_iSup_truncFinset]
  exact tendsto_atTop_iSup fun M M' hM => Finset.sum_le_sum_of_subset (truncFinset_mono k hM)

/-- The sum over the branches of the truncated tree is the sum over the truncated finset. -/
lemma sum_truncBranch_eq (f : (Fin k → ℕ × ℕ) → ℝ≥0∞) :
    ∑ α : TruncBranch k M, f (truncBranchCoe k M α) = ∑ α ∈ truncFinset k M, f α := by
  rw [truncFinset, Finset.sum_map]
  rfl

lemma tendsto_sum_truncBranch (f : (Fin k → ℕ × ℕ) → ℝ≥0∞) :
    Tendsto (fun M => ∑ α : TruncBranch k M, f (truncBranchCoe k M α)) atTop (𝓝 (∑' α, f α)) := by
  simp_rw [sum_truncBranch_eq]
  exact tendsto_sum_truncFinset k f

/-- Real form: if the total sum is finite, the real truncated sums converge to it. -/
lemma tendsto_toReal_sum_truncBranch (f : (Fin k → ℕ × ℕ) → ℝ≥0∞) (hf : ∑' α, f α ≠ ∞) :
    Tendsto (fun M => ∑ α : TruncBranch k M, (f (truncBranchCoe k M α)).toReal) atTop
      (𝓝 (∑' α, f α).toReal) := by
  have h := (ENNReal.tendsto_toReal hf).comp (tendsto_sum_truncBranch k f)
  refine h.congr fun M => ?_
  simp only [Function.comp]
  rw [ENNReal.toReal_sum]
  intro α _
  exact ne_top_of_le_ne_top hf (ENNReal.le_tsum _)

end

end SpinGlass
