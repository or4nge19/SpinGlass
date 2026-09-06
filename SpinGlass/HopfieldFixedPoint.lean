import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Hopfield scalar fixed point

Solutions of `m = tanh(β m + h)`. Main: `mStar`. Used in Talagrand’s Hopfield localization.
-/

open scoped Interval

namespace SpinGlass

/-! ## The scalar map `m ↦ tanh(β m + h)` -/

noncomputable def hopfieldTanhMap (β h : ℝ) : ℝ → ℝ :=
  fun m => Real.tanh (β * m + h)

lemma continuous_tanh : Continuous (Real.tanh) := by
  change Continuous (fun x : ℝ => Real.tanh x)
  -- `tanh = sinh / cosh` and `cosh` is never zero.
  have htanh : (fun x : ℝ => Real.tanh x) = fun x : ℝ => Real.sinh x / Real.cosh x := by
    funext x
    simp [Real.tanh_eq_sinh_div_cosh]
  have hcosh : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => ne_of_gt (Real.cosh_pos x)
  simpa [htanh] using
    (Real.continuous_sinh.div Real.continuous_cosh hcosh)

@[continuity] lemma continuous_hopfieldTanhMap (β h : ℝ) : Continuous (hopfieldTanhMap β h) := by
  have hlin : Continuous fun m : ℝ => β * m + h := by
    simpa [hopfieldTanhMap] using (continuous_const.mul continuous_id).add continuous_const
  simpa [hopfieldTanhMap] using (continuous_tanh.comp hlin)

/-! ## Existence of a fixed point in `[-1,1]` -/

theorem exists_fixedPoint_hopfieldTanhMap (β h : ℝ) :
    ∃ m ∈ Set.Icc (-1 : ℝ) 1, m = hopfieldTanhMap β h m := by
  let f : ℝ → ℝ := hopfieldTanhMap β h
  have hf : ContinuousOn f ([[(-1 : ℝ), (1 : ℝ)]]) :=
    (continuous_hopfieldTanhMap β h).continuousOn
  have ha : (-1 : ℝ) ≤ f (-1) := le_of_lt (Real.neg_one_lt_tanh (β * (-1 : ℝ) + h))
  have hb : f 1 ≤ (1 : ℝ) := le_of_lt (Real.tanh_lt_one (β * (1 : ℝ) + h))
  obtain ⟨c, hc, hfix⟩ := exists_mem_uIcc_isFixedPt (a := (-1 : ℝ)) (b := (1 : ℝ)) hf ha hb
  have hcIcc : c ∈ Set.Icc (-1 : ℝ) 1 := by
    have hab : (-1 : ℝ) ≤ (1 : ℝ) := by norm_num
    simpa [Set.uIcc_of_le hab] using hc
  refine ⟨c, hcIcc, ?_⟩
  -- `IsFixedPt f c` is `f c = c`
  simpa [f] using hfix.symm

/-! ## A canonical fixed point: the maximal one in `[-1,1]` -/

/-- Fixed points of `hopfieldTanhMap β h` restricted to the interval `[-1,1]`. -/
def hopfieldFixedPointSet (β h : ℝ) : Set ℝ :=
  { m | m ∈ Set.Icc (-1 : ℝ) 1 ∧ m = hopfieldTanhMap β h m }

lemma hopfieldFixedPointSet_nonempty (β h : ℝ) : (hopfieldFixedPointSet β h).Nonempty := by
  rcases exists_fixedPoint_hopfieldTanhMap (β := β) (h := h) with ⟨m, hmIcc, hm⟩
  exact ⟨m, ⟨hmIcc, hm⟩⟩

lemma bddAbove_hopfieldFixedPointSet (β h : ℝ) : BddAbove (hopfieldFixedPointSet β h) := by
  refine ⟨(1 : ℝ), ?_⟩
  intro m hm
  exact hm.1.2

lemma isClosed_hopfieldFixedPointSet (β h : ℝ) : IsClosed (hopfieldFixedPointSet β h) := by
  have hIcc : IsClosed (Set.Icc (-1 : ℝ) 1) := isClosed_Icc
  have htanh : Continuous fun m : ℝ => hopfieldTanhMap β h m := continuous_hopfieldTanhMap β h
  have hEq : IsClosed {m : ℝ | m = hopfieldTanhMap β h m} :=
    isClosed_eq continuous_id htanh
  -- package the set as an intersection of closed sets
  have :
      hopfieldFixedPointSet β h
        =
        (Set.Icc (-1 : ℝ) 1) ∩ {m : ℝ | m = hopfieldTanhMap β h m} := by
    ext m
    simp [hopfieldFixedPointSet, and_assoc, and_comm]
  simpa [this] using hIcc.inter hEq

/-- The maximal fixed point in `[-1,1]` (Talagrand’s `m*`, as a canonical choice). -/
noncomputable def hopfield_mStar (β h : ℝ) : ℝ :=
  sSup (hopfieldFixedPointSet β h)

lemma hopfield_mStar_mem (β h : ℝ) : hopfield_mStar β h ∈ hopfieldFixedPointSet β h := by
  have hclosed : IsClosed (hopfieldFixedPointSet β h) := isClosed_hopfieldFixedPointSet β h
  have hne : (hopfieldFixedPointSet β h).Nonempty := hopfieldFixedPointSet_nonempty β h
  have hbdd : BddAbove (hopfieldFixedPointSet β h) := bddAbove_hopfieldFixedPointSet β h
  simpa [hopfield_mStar] using hclosed.csSup_mem hne hbdd

lemma hopfield_mStar_mem_Icc (β h : ℝ) : hopfield_mStar β h ∈ Set.Icc (-1 : ℝ) 1 :=
  (hopfield_mStar_mem β h).1

lemma hopfield_mStar_eq_tanh (β h : ℝ) :
    hopfield_mStar β h = hopfieldTanhMap β h (hopfield_mStar β h) :=
  (hopfield_mStar_mem β h).2

end SpinGlass

