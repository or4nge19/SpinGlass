import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic

/-!
# Basic geometry of the lattice `ℤ^d`

This file provides reusable definitions and lemmas for working with `ℤ^d` as functions
`Fin d → ℤ`, including:
- standard basis vectors,
- nearest-neighbor relation,
- finite boxes `Λ_L := [-L,L]^d ∩ ℤ^d`,
- annuli/boundaries,
- the `ℓ∞`-distance and a basic “pairwise separation” predicate for quadruples.
-/

namespace SpinGlass

namespace Lattice

namespace Zd

/-- The integer lattice `ℤ^d`, represented as `Fin d → ℤ`. -/
abbrev ZLattice (d : ℕ) : Type := Fin d → ℤ

/-- The 4D integer lattice `ℤ^4`. -/
abbrev Z4 : Type := ZLattice 4

/--
The standard basis vector `e_i ∈ ℤ^d`.

Implementation note: this is just `Pi.single i (1 : ℤ)` (so we reuse Mathlib's `Pi.single` API).
-/
abbrev stdBasis {d : ℕ} (i : Fin d) : ZLattice d := Pi.single i (1 : ℤ)

/-- The (finite) set of nearest-neighbors of `x` in `ℤ^d` (cardinality `2d`). -/
noncomputable def neighbors (d : ℕ) (x : ZLattice d) : Finset (ZLattice d) :=
  (Finset.univ : Finset (Fin d)).biUnion fun i =>
    ({x + stdBasis i, x - stdBasis i} : Finset (ZLattice d))

/-- The nearest-neighbor relation on `ℤ^d`. -/
def IsNN (d : ℕ) (x y : ZLattice d) : Prop :=
  y ∈ neighbors d x

lemma mem_neighbors_iff {d : ℕ} {x y : ZLattice d} :
    y ∈ neighbors d x ↔ ∃ i : Fin d, y = x + stdBasis i ∨ y = x - stdBasis i := by
  simp [neighbors]

lemma IsNN_iff {d : ℕ} {x y : ZLattice d} :
    IsNN d x y ↔ ∃ i : Fin d, y = x + stdBasis i ∨ y = x - stdBasis i := by
  simp [IsNN, mem_neighbors_iff]

lemma IsNN_symm {d : ℕ} {x y : ZLattice d} : IsNN d x y → IsNN d y x := by
  intro hxy
  rcases (IsNN_iff (d := d) (x := x) (y := y)).1 hxy with ⟨i, rfl | rfl⟩
  · refine (IsNN_iff (d := d) (x := x + stdBasis i) (y := x)).2 ?_
    refine ⟨i, Or.inr ?_⟩
    simp [stdBasis]
  · refine (IsNN_iff (d := d) (x := x - stdBasis i) (y := x)).2 ?_
    refine ⟨i, Or.inl ?_⟩
    simp [stdBasis]

/-! ### Core API: nearest-neighbor relation -/

lemma IsNN_comm {d : ℕ} {x y : ZLattice d} : IsNN d x y ↔ IsNN d y x :=
  ⟨IsNN_symm (d := d), IsNN_symm (d := d)⟩

lemma IsNN_irrefl {d : ℕ} (x : ZLattice d) : ¬ IsNN d x x := by
  intro hxx
  rcases (IsNN_iff (d := d) (x := x) (y := x)).1 hxx with ⟨i, h | h⟩
  · have hi : (x i : ℤ) = (x i : ℤ) + 1 := by
      simpa [stdBasis] using congrArg (fun f : ZLattice d => f i) h
    have : (0 : ℤ) = 1 := by
      have h' := congrArg (fun z : ℤ => z - x i) hi
      simp [sub_eq_add_neg, add_left_comm, add_comm] at h'
    exact zero_ne_one this
  · have hi : (x i : ℤ) = (x i : ℤ) - 1 := by
      simpa [stdBasis] using congrArg (fun f : ZLattice d => f i) h
    have h0 : (0 : ℤ) = -1 := by
      have h' := congrArg (fun z : ℤ => z - x i) hi
      simp [sub_eq_add_neg, add_left_comm, add_comm] at h'
    exact (show (0 : ℤ) ≠ -1 by decide) h0

lemma IsNN.ne {d : ℕ} {x y : ZLattice d} (hxy : IsNN d x y) : x ≠ y := by
  intro h
  subst h
  exact IsNN_irrefl (d := d) x hxy

/-- The (finite) set `Λ_L := [-L,L]^d ∩ ℤ^d`, as a `Finset`. -/
noncomputable def box (d : ℕ) (L : ℕ) : Finset (ZLattice d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))

/-- The annulus `Ann(k,n) := Λ_n \ Λ_{k-1}`. -/
noncomputable def ann (d : ℕ) (k n : ℕ) : Finset (ZLattice d) :=
  box d n \ box d (k - 1)

/-- The boundary `∂Λ_n := Ann(n,n)`. -/
noncomputable def boundary (d : ℕ) (n : ℕ) : Finset (ZLattice d) :=
  ann d n n

/-- ℓ∞-distance on `ℤ^d`: `max_i |x_i - y_i|`. -/
noncomputable def distInf (d : ℕ) (x y : ZLattice d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun i => Int.natAbs (x i - y i)

/--
Pairwise separation condition used in the 4D-triviality paper:
all mutual `ℓ∞`-distances between `x,y,z,t` are larger than `L`.
-/
def pairwiseFar (d : ℕ) (L : ℕ) (x y z t : ZLattice d) : Prop :=
  L < distInf d x y ∧ L < distInf d x z ∧ L < distInf d x t ∧
  L < distInf d y z ∧ L < distInf d y t ∧
  L < distInf d z t

/-!
### boxes/annuli

-/

@[simp]
lemma mem_box_iff {d : ℕ} {L : ℕ} {x : ZLattice d} :
    x ∈ box d L ↔ ∀ i : Fin d, x i ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) := by
  simp [box]

@[simp]
lemma box_zero (d : ℕ) : box d 0 = ({0} : Finset (ZLattice d)) := by
  simpa [box, Finset.Icc_self] using (Fintype.piFinset_singleton (f := (0 : ZLattice d)))

@[simp]
lemma zero_mem_box (d : ℕ) (L : ℕ) : (0 : ZLattice d) ∈ box d L := by
  refine (mem_box_iff (d := d) (L := L) (x := (0 : ZLattice d))).2 ?_
  intro i
  have h0L : (0 : ℤ) ≤ (L : ℤ) := by exact_mod_cast (Nat.zero_le L)
  have hneg : (-(L : ℤ)) ≤ (0 : ℤ) := by
    exact neg_nonpos.2 h0L
  exact (Finset.mem_Icc.2 ⟨hneg, h0L⟩)

lemma box_nonempty (d : ℕ) (L : ℕ) : (box d L).Nonempty :=
  ⟨0, zero_mem_box d L⟩

lemma mem_ann_iff {d : ℕ} {k n : ℕ} {x : ZLattice d} :
    x ∈ ann d k n ↔ x ∈ box d n ∧ x ∉ box d (k - 1) := by
  simp [ann]

lemma mem_boundary_iff {d : ℕ} {n : ℕ} {x : ZLattice d} :
    x ∈ boundary d n ↔ x ∈ box d n ∧ x ∉ box d (n - 1) := by
  simp [boundary, ann]

lemma ann_subset_box {d k n : ℕ} : ann d k n ⊆ box d n := by
  intro x hx
  exact (mem_ann_iff (d := d) (k := k) (n := n) (x := x)).1 hx |>.1

lemma boundary_subset_box {d n : ℕ} : boundary d n ⊆ box d n := by
  intro x hx
  exact (mem_boundary_iff (d := d) (n := n) (x := x)).1 hx |>.1

lemma box_mono {d L L' : ℕ} (h : L ≤ L') : box d L ⊆ box d L' := by
  intro x hx
  have hx' : ∀ i : Fin d, x i ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) :=
    (mem_box_iff (d := d) (L := L)).1 hx
  refine (mem_box_iff (d := d) (L := L')).2 ?_
  intro i
  have hi : x i ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) := hx' i
  have hx_ge : (-(L : ℤ)) ≤ x i := (Finset.mem_Icc.1 hi).1
  have hx_le : x i ≤ (L : ℤ) := (Finset.mem_Icc.1 hi).2
  have hL : (L : ℤ) ≤ (L' : ℤ) := by exact_mod_cast h
  have hx_le' : x i ≤ (L' : ℤ) := le_trans hx_le hL
  have hx_ge' : (-(L' : ℤ)) ≤ x i := by
    have hneg : (-(L' : ℤ)) ≤ (-(L : ℤ)) := (neg_le_neg_iff).2 hL
    exact le_trans hneg hx_ge
  exact (Finset.mem_Icc.2 ⟨hx_ge', hx_le'⟩)

/-! ### ℓ∞-distance -/

@[simp]
lemma distInf_self (d : ℕ) (x : ZLattice d) : distInf d x x = 0 := by
  unfold distInf
  simpa using (Finset.sup_bot (s := (Finset.univ : Finset (Fin d))) (α := ℕ))

lemma distInf_comm (d : ℕ) (x y : ZLattice d) : distInf d x y = distInf d y x := by
  unfold distInf
  refine Finset.sup_congr rfl ?_
  intro i _hi
  have h :
      Int.natAbs (x i - y i) = Int.natAbs (-(x i - y i)) := by
    simpa using (Int.natAbs_neg (x i - y i)).symm
  simpa [neg_sub] using h

lemma natAbs_sub_le_distInf {d : ℕ} (x y : ZLattice d) (i : Fin d) :
    Int.natAbs (x i - y i) ≤ distInf d x y := by
  unfold distInf
  exact Finset.le_sup (s := (Finset.univ : Finset (Fin d)))
    (f := fun j => Int.natAbs (x j - y j)) (b := i) (by simp)

lemma distInf_le_iff {d : ℕ} (x y : ZLattice d) (n : ℕ) :
    distInf d x y ≤ n ↔ ∀ i : Fin d, Int.natAbs (x i - y i) ≤ n := by
  unfold distInf
  simp [Finset.sup_le_iff]

lemma distInf_eq_zero_iff {d : ℕ} (x y : ZLattice d) : distInf d x y = 0 ↔ x = y := by
  constructor
  · intro h
    ext i
    have hi0 : Int.natAbs (x i - y i) ≤ 0 := by
      have := (distInf_le_iff (d := d) x y 0).1 (by simp [h])
      simpa using this i
    have hi0' : Int.natAbs (x i - y i) = 0 := Nat.eq_zero_of_le_zero hi0
    have : x i - y i = 0 := by
      simpa using (Int.natAbs_eq_zero.1 hi0')
    exact sub_eq_zero.1 this
  · intro h
    simp [h]

/-! ### Pairwise separation -/

lemma pairwiseFar.xy {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d x y := h.1
lemma pairwiseFar.xz {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d x z := h.2.1
lemma pairwiseFar.xt {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d x t := h.2.2.1
lemma pairwiseFar.yz {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d y z := h.2.2.2.1
lemma pairwiseFar.yt {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d y t := h.2.2.2.2.1
lemma pairwiseFar.zt {d : ℕ} {L : ℕ} {x y z t : ZLattice d} (h : pairwiseFar d L x y z t) :
    L < distInf d z t := h.2.2.2.2.2

lemma pairwiseFar.mono {d : ℕ} {L L' : ℕ} {x y z t : ZLattice d} (hLL' : L ≤ L') :
    pairwiseFar d L' x y z t → pairwiseFar d L x y z t := by
  intro h
  refine ⟨lt_of_le_of_lt hLL' h.xy, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hLL' h.xz
  · exact lt_of_le_of_lt hLL' h.xt
  · exact lt_of_le_of_lt hLL' h.yz
  · exact lt_of_le_of_lt hLL' h.yt
  · exact lt_of_le_of_lt hLL' h.zt

end Zd

end Lattice

end SpinGlass
