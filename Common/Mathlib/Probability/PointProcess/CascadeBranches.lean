/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeUnzip
import Common.Mathlib.Probability.PointProcess.CascadeIdentities

/-!
# Cascade sums as sums over branches

In the unzipped representation (`cascadeZip`) of a `k`-level cascade, a **branch** is an address
`α : Fin k → ℕ × ℕ` — at each level the index `(n, j)` of a point of the superposition sample —
and Talagrand's `u*_α = u_{α|1} ⋯ u_{α|k}` and `(z_{1,α}, …, z_{k,α})` are the explicit
functions `branchWeight` (zero for a non-existing branch, i.e. when some `j` exceeds the number of
points) and `branchMarks` of the weights and of the marks. The cascade sums are then genuine sums
over branches:

* `cascadeSum_cascadeZip`: `∑_α u*_α G(z_α)`, a `tsum` over `Fin k → ℕ × ℕ`;
* `cascadeSq_cascadeZip`: the prefix-squares `Q_r = ∑_{α|r = γ|r} u*_α u*_γ G(z_α) G(z_γ)`.

This is the form of the cascade Gibbs averages that a finite truncation of the tree can
approximate (Talagrand, Vol. II, §14.4).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

universe u

variable {T : Type u} [MeasurableSpace T]

/-! ### Branch weights and branch marks -/

/-- The weight `u*_α = ∏_p u_{α|p}` of the branch `α`, zero if the branch does not exist. -/
def branchWeight : (k : ℕ) → CascadeWeights k → (Fin k → ℕ × ℕ) → ℝ≥0∞
  | 0, _, _ => 1
  | k + 1, w, α =>
    (if (α 0).2 < (w.1 (α 0).1).2 then ENNReal.ofReal ((w.1 (α 0).1).1 (α 0).2) else 0)
      * branchWeight k (w.2 (α 0).1 (α 0).2) (Fin.tail α)

/-- The marks `(z_{1,α}, …, z_{k,α})` along the branch `α`. -/
def branchMarks : (k : ℕ) → CascadeMarks T k → (Fin k → ℕ × ℕ) → (Fin k → T)
  | 0, _, _ => Fin.elim0
  | k + 1, z, α => Fin.cons (z.1 (α 0).1 (α 0).2) (branchMarks k (z.2 (α 0).1 (α 0).2) (Fin.tail α))

omit [MeasurableSpace T] in
lemma branchWeight_succ (k : ℕ) (w : CascadeWeights (k + 1)) (nj : ℕ × ℕ) (β : Fin k → ℕ × ℕ) :
    branchWeight (k + 1) w (Fin.cons nj β)
      = (if nj.2 < (w.1 nj.1).2 then ENNReal.ofReal ((w.1 nj.1).1 nj.2) else 0)
        * branchWeight k (w.2 nj.1 nj.2) β := by
  simp [branchWeight]

omit [MeasurableSpace T] in
lemma branchMarks_succ (k : ℕ) (z : CascadeMarks T (k + 1)) (nj : ℕ × ℕ) (β : Fin k → ℕ × ℕ) :
    branchMarks (k + 1) z (Fin.cons nj β)
      = Fin.cons (z.1 nj.1 nj.2) (branchMarks k (z.2 nj.1 nj.2) β) := by
  simp [branchMarks]

/-- A `tsum` over `Fin (k+1) → X` splits as a `tsum` over the first entry and the tail. -/
lemma tsum_fin_succ {k : ℕ} {X : Type*} (f : (Fin (k + 1) → X) → ℝ≥0∞) :
    ∑' α, f α = ∑' (x : X) (β : Fin k → X), f (Fin.cons x β) := by
  rw [← (Fin.consEquiv fun _ => X).tsum_eq, ENNReal.tsum_prod']
  rfl

/-- A `tsum` over `ℕ × ℕ` whose terms vanish beyond the counts is a sum over the points. -/
lemma tsum_nat_prod_ite (c : ℕ → ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑' nj : ℕ × ℕ, (if nj.2 < c nj.1 then g nj.1 nj.2 else 0)
      = ∑' n, ∑ j ∈ Finset.range (c n), g n j := by
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun n => ?_
  rw [tsum_eq_sum (s := Finset.range (c n)) fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    simp [not_lt.2 hj]]
  exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.1 hj]

/-! ### The cascade sum over branches -/

/-- **The cascade sum is a sum over branches**: `∑_α u*_α G(z_{1,α}, …, z_{k,α})`. -/
theorem cascadeSum_cascadeZip : ∀ (k : ℕ) {G : (Fin k → T) → ℝ≥0∞}, Measurable G →
    ∀ (w : CascadeWeights k) (z : CascadeMarks T k),
    cascadeSum k G (cascadeZip k (w, z))
      = ∑' α : Fin k → ℕ × ℕ, branchWeight k w α * G (branchMarks k z α)
  | 0, G, _, w, z => by
    rw [cascadeSum_zero, tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
    simp [branchWeight]
    congr 1
  | k + 1, G, hG, w, z => by
    have hv : Measurable fun p : T × CascadeSpace T k =>
        cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 :=
      measurable_cascadeSum_prod k (G := fun p zs => G (Fin.cons p zs))
        (hG.comp measurable_fin_cons)
    rw [cascadeSum_succ, cascadeZip_succ, pdSum,
      lintegral_superCounting_superZip _ _ (measurable_ofReal_mul hv),
      ← tsum_nat_prod_ite (fun n => (w.1 n).2) (fun n j => ENNReal.ofReal ((w.1 n).1 j)
        * cascadeSum k (fun zs => G (Fin.cons (z.1 n j) zs)) (cascadeZip k (w.2 n j, z.2 n j))),
      tsum_fin_succ]
    refine tsum_congr fun nj => ?_
    simp_rw [branchWeight_succ, branchMarks_succ, mul_assoc, ENNReal.tsum_mul_left]
    split_ifs with h
    · rw [cascadeSum_cascadeZip k (G := fun zs => G (Fin.cons (z.1 nj.1 nj.2) zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
    · rw [zero_mul]

/-! ### The prefix-squares over branches -/

/-- The indicator that two branches of a `k`-level cascade agree on their first `r` levels
(`r ≤ k`), i.e. `1_{(α, γ) ≥ r}` in Talagrand's notation. -/
def prefixEq (k r : ℕ) (α γ : Fin k → ℕ × ℕ) : ℝ≥0∞ :=
  if r ≤ k ∧ ∀ i : Fin k, (i : ℕ) < r → α i = γ i then 1 else 0

omit [MeasurableSpace T] in
lemma prefixEq_zero (k : ℕ) (α γ : Fin k → ℕ × ℕ) : prefixEq k 0 α γ = 1 := by
  simp [prefixEq]

omit [MeasurableSpace T] in
lemma prefixEq_zero_succ (r : ℕ) (α γ : Fin 0 → ℕ × ℕ) : prefixEq 0 (r + 1) α γ = 0 := by
  simp [prefixEq]

omit [MeasurableSpace T] in
lemma prefixEq_succ (k r : ℕ) (nj nj' : ℕ × ℕ) (β δ : Fin k → ℕ × ℕ) :
    prefixEq (k + 1) (r + 1) (Fin.cons nj β) (Fin.cons nj' δ)
      = (if nj' = nj then 1 else 0) * prefixEq k r β δ := by
  have hiff : (r + 1 ≤ k + 1 ∧ ∀ i : Fin (k + 1), (i : ℕ) < r + 1 →
        (Fin.cons nj β : Fin (k + 1) → ℕ × ℕ) i = (Fin.cons nj' δ : Fin (k + 1) → ℕ × ℕ) i)
      ↔ (nj' = nj ∧ (r ≤ k ∧ ∀ i : Fin k, (i : ℕ) < r → β i = δ i)) := by
    constructor
    · rintro ⟨hr, hall⟩
      refine ⟨(by simpa using (hall 0 (by simp)).symm), by omega, fun i hi => ?_⟩
      have := hall i.succ (by simp only [Fin.val_succ]; omega)
      simpa using this
    · rintro ⟨hnj, hr, hall⟩
      refine ⟨by omega, fun i hi => ?_⟩
      induction i using Fin.cases with
      | zero => simp [hnj]
      | succ j =>
        simp only [Fin.cons_succ]
        simp only [Fin.val_succ] at hi
        exact hall j (by omega)
  unfold prefixEq
  rw [if_congr hiff rfl rfl]
  by_cases h : nj' = nj
  · simp [h]
  · simp [h]

/-- **The prefix-squares are sums over pairs of branches**:
`Q_r = ∑_{α|r = γ|r} u*_α u*_γ G(z_α) G(z_γ)`. -/
theorem cascadeSq_cascadeZip : ∀ (k r : ℕ) {G : (Fin k → T) → ℝ≥0∞}, Measurable G →
    ∀ (w : CascadeWeights k) (z : CascadeMarks T k),
    cascadeSq k r G (cascadeZip k (w, z))
      = ∑' α : Fin k → ℕ × ℕ, ∑' γ : Fin k → ℕ × ℕ, prefixEq k r α γ
          * (branchWeight k w α * branchWeight k w γ
            * (G (branchMarks k z α) * G (branchMarks k z γ)))
  | k, 0, G, hG, w, z => by
    rw [cascadeSq_zero, cascadeSum_cascadeZip k hG, ← ENNReal.tsum_mul_right]
    simp_rw [← ENNReal.tsum_mul_left, prefixEq_zero, one_mul]
    exact tsum_congr fun α => tsum_congr fun γ => by ring
  | 0, r + 1, G, _, w, z => by
    rw [cascadeSq_zero_succ]
    simp [prefixEq_zero_succ]
  | k + 1, r + 1, G, hG, w, z => by
    have hv : Measurable fun p : T × CascadeSpace T k =>
        cascadeSq k r (fun zs => G (Fin.cons p.1 zs)) p.2 :=
      measurable_cascadeSq_prod k r (G := fun p zs => G (Fin.cons p zs))
        (hG.comp measurable_fin_cons)
    have hφ : Measurable fun p : ℝ × (T × CascadeSpace T k) =>
        ENNReal.ofReal p.1 * ENNReal.ofReal p.1
          * cascadeSq k r (fun zs => G (Fin.cons p.2.1 zs)) p.2.2 :=
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hv.comp measurable_snd)
    rw [cascadeSq_succ, cascadeZip_succ, lintegral_superCounting_superZip _ _ hφ,
      ← tsum_nat_prod_ite (fun n => (w.1 n).2) (fun n j =>
        ENNReal.ofReal ((w.1 n).1 j) * ENNReal.ofReal ((w.1 n).1 j)
          * cascadeSq k r (fun zs => G (Fin.cons (z.1 n j) zs)) (cascadeZip k (w.2 n j, z.2 n j))),
      tsum_fin_succ]
    refine tsum_congr fun nj => ?_
    -- collapse the inner branch index of `γ`
    have hcol : ∀ β : Fin k → ℕ × ℕ, (∑' γ : Fin (k + 1) → ℕ × ℕ,
        prefixEq (k + 1) (r + 1) (Fin.cons nj β) γ
          * (branchWeight (k + 1) w (Fin.cons nj β) * branchWeight (k + 1) w γ
            * (G (branchMarks (k + 1) z (Fin.cons nj β)) * G (branchMarks (k + 1) z γ))))
        = ∑' δ : Fin k → ℕ × ℕ, prefixEq k r β δ
          * (branchWeight (k + 1) w (Fin.cons nj β) * branchWeight (k + 1) w (Fin.cons nj δ)
            * (G (branchMarks (k + 1) z (Fin.cons nj β))
              * G (branchMarks (k + 1) z (Fin.cons nj δ)))) := by
      intro β
      rw [tsum_fin_succ]
      simp_rw [prefixEq_succ, mul_assoc, ENNReal.tsum_mul_left, ite_mul, one_mul, zero_mul]
      rw [tsum_ite_eq]
    simp_rw [hcol, branchWeight_succ, branchMarks_succ]
    split_ifs with h
    · rw [cascadeSq_cascadeZip k r (G := fun zs => G (Fin.cons (z.1 nj.1 nj.2) zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
      simp_rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun β => tsum_congr fun δ => ?_
      ring
    · simp

end

end ProbabilityTheory
