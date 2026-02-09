import SpinGlass.Papers.Triviality4D.RandomCurrent
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Random current connectivity ↔ subcurrent event (finite volume)

This file proves the deterministic equivalence, for two-point sets `{x,y}`,
between:

- connectivity of `x` and `y` in the trace graph of a current `n`, and
- existence of a subcurrent `m ≤ n` with sources `{x,y}` (`HasSubCurrent n {x,y}`).

This aims to model the paper event `ℱ_{xy}`.
-/

open scoped BigOperators

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-! ## The trace graph as a `SimpleGraph` -/

/-- The trace graph of a current: adjacency is `Adj n`. -/
def traceGraph (n : Current (V := V) Λ) : SimpleGraph (↥Λ) where
  Adj x y := Adj (V := V) (Λ := Λ) n x y
  symm := by
    intro x y h
    exact (Adj_comm (V := V) (Λ := Λ) n (x := x) (y := y)).1 h
  loopless := by
    intro x h
    rcases h with ⟨hxx, _⟩
    exact hxx rfl

@[simp] lemma traceGraph_adj (n : Current (V := V) Λ) (x y : ↥Λ) :
    (traceGraph (V := V) (Λ := Λ) n).Adj x y ↔ Adj (V := V) (Λ := Λ) n x y :=
  Iff.rfl

@[simp] lemma traceGraph_reachable_iff_connected (n : Current (V := V) Λ) (x y : ↥Λ) :
    (traceGraph (V := V) (Λ := Λ) n).Reachable x y ↔ Connected (V := V) (Λ := Λ) n x y := by
  simpa [Connected, traceGraph] using
    (SimpleGraph.reachable_iff_reflTransGen (G := traceGraph (V := V) (Λ := Λ) n) x y)

/-! ## Currents induced by walks -/

/-- The unit current supported on a single edge. -/
def unitCurrent {Λ : Finset V} (e₀ : Edge (V := V) Λ) : Current (V := V) Λ :=
  fun e => if e = e₀ then 1 else 0

lemma sources_unitCurrent_edge {x y : ↥Λ} (hxy : x ≠ y) :
    sources (V := V) (Λ := Λ) (unitCurrent (V := V) (Λ := Λ) (edge (V := V) (Λ := Λ) x y hxy))
      = ({x, y} : Finset (↥Λ)) := by
  let e₀ : Edge (V := V) Λ := edge (V := V) (Λ := Λ) x y hxy
  ext z
  have hsum :
      (∑ e : Edge (V := V) Λ,
          if z ∈ (e.1 : Sym2 (↥Λ)) then if e = e₀ then 1 else 0 else 0) =
        (if z ∈ (e₀.1 : Sym2 (↥Λ)) then 1 else 0) := by
    have hintegrand :
        (fun e : Edge (V := V) Λ =>
            if z ∈ (e.1 : Sym2 (↥Λ)) then (if e = e₀ then 1 else 0) else 0) =
          (fun e : Edge (V := V) Λ =>
            if e = e₀ then (if z ∈ (e₀.1 : Sym2 (↥Λ)) then 1 else 0) else 0) := by
      funext e
      by_cases he : e = e₀ <;> simp [he]
    simp [hintegrand]
  simp [sources, IsSource, degree, unitCurrent, e₀, hsum]
  by_cases hz : z = x ∨ z = y <;> simp [hz, e₀, edge, Sym2.mem_iff]

/--
The current obtained by summing unit-currents along the edges of a walk in the trace graph.

It counts each traversed edge with multiplicity (hence is a genuine `Current`).
-/
noncomputable def currentOfWalk (n : Current (V := V) Λ) {x y : ↥Λ}
    (w : (traceGraph (V := V) (Λ := Λ) n).Walk x y) : Current (V := V) Λ := by
  refine
    (match w with
    | .nil => 0
    | .cons hab p =>
        unitCurrent (V := V) (Λ := Λ) (edge (V := V) (Λ := Λ) _ _ hab.choose) +
          currentOfWalk n p)

lemma sources_currentOfWalk (n : Current (V := V) Λ) {x y : ↥Λ}
    (w : (traceGraph (V := V) (Λ := Λ) n).Walk x y) :
    sources (V := V) (Λ := Λ) (currentOfWalk (V := V) (Λ := Λ) n w)
      = (if x = y then (∅ : Finset (↥Λ)) else ({x, y} : Finset (↥Λ))) := by
  induction w with
  | nil =>
      ext z
      simp [currentOfWalk, sources, IsSource, degree]
  | cons hab p ih =>
      rename_i u v z
      have huv : u ≠ v := hab.choose
      simp [currentOfWalk, sources_add,
        sources_unitCurrent_edge (V := V) (Λ := Λ) (x := u) (y := v) huv, ih]
      by_cases hvz : v = z
      · subst hvz
        simp [huv]
      · by_cases huz : u = z
        · subst huz
          have hvu : v ≠ u := by simpa using hvz
          simp [Finset.pair_comm, hvu]
        · have hvu : v ≠ u := huv.symm
          have hzu : z ≠ u := by simpa [eq_comm] using huz
          have hzv : z ≠ v := by simpa [eq_comm] using hvz
          ext t
          by_cases htu : t = u <;> by_cases htv : t = v <;> by_cases htz : t = z <;>
            simp [Finset.mem_symmDiff, htu, htv, htz, hvz, huz, huv, hvu, hzu, hzv]

lemma currentOfWalk_apply (n : Current (V := V) Λ) {x y : ↥Λ}
    (w : (traceGraph (V := V) (Λ := Λ) n).Walk x y) (e : Edge (V := V) Λ) :
    currentOfWalk (V := V) (Λ := Λ) n w e = w.edges.count e.1 := by
  induction w with
  | nil =>
      simp [currentOfWalk]
  | cons hab p ih =>
      rename_i u v z
      let e₀ : Edge (V := V) Λ := edge (V := V) (Λ := Λ) u v hab.choose
      have heq : e.1 = s(u, v) ↔ e = e₀ := by
        simpa [e₀, edge] using (Subtype.ext_iff (a1 := e) (a2 := e₀)).symm
      by_cases h : e.1 = s(u, v)
      · have h' : e = e₀ := (heq.1 h)
        have ih₀ : currentOfWalk (V := V) (Λ := Λ) n p e₀ = p.edges.count e₀.1 := by
          simpa [h'] using ih
        simp [currentOfWalk, unitCurrent, e₀, ih₀, List.count_cons, h, h', Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
        simp [edge]
      · have h' : e ≠ e₀ := by
          intro hEq
          exact h ((heq.2 hEq))
        have hs : ¬ s(u, v) = (e.1 : Sym2 (↥Λ)) := by
          simpa [eq_comm] using h
        simp [currentOfWalk, unitCurrent, e₀, ih, h, h', hs]

lemma n_pos_of_mem_walk_edges (n : Current (V := V) Λ) {x y : ↥Λ}
    (w : (traceGraph (V := V) (Λ := Λ) n).Walk x y) {e : Edge (V := V) Λ} (he : e.1 ∈ w.edges) :
    0 < n e := by
  have heEdgeSet : e.1 ∈ (traceGraph (V := V) (Λ := Λ) n).edgeSet :=
    w.edges_subset_edgeSet he
  have hadj :
      (traceGraph (V := V) (Λ := Λ) n).Adj (e.1.out.1) (e.1.out.2) := by
    have : s(e.1.out.1, e.1.out.2) ∈ (traceGraph (V := V) (Λ := Λ) n).edgeSet := by
      simpa [Sym2.mk, e.1.out_eq] using heEdgeSet
    exact (SimpleGraph.mem_edgeSet (G := traceGraph (V := V) (Λ := Λ) n) (v := e.1.out.1) (w := e.1.out.2)).1 this
  rcases (traceGraph_adj (V := V) (Λ := Λ) n (e.1.out.1) (e.1.out.2)).1 hadj with ⟨hne, hpos⟩
  have heq : edge (V := V) (Λ := Λ) (e.1.out.1) (e.1.out.2) hne = e := by
    apply Subtype.ext
    simp [edge, Sym2.mk, e.1.out_eq]
  simpa [heq] using hpos

lemma currentOfWalk_le_of_isTrail (n : Current (V := V) Λ) {x y : ↥Λ}
    (w : (traceGraph (V := V) (Λ := Λ) n).Walk x y) (hw : w.IsTrail) :
    CurrentLE (V := V) (Λ := Λ) (currentOfWalk (V := V) (Λ := Λ) n w) n := by
  intro e
  by_cases he : e.1 ∈ w.edges
  · have hcount : w.edges.count e.1 = 1 :=
      SimpleGraph.Walk.IsTrail.count_edges_eq_one (G := traceGraph (V := V) (Λ := Λ) n) (h := hw) he
    have hpos : 0 < n e := n_pos_of_mem_walk_edges (V := V) (Λ := Λ) n w he
    have : currentOfWalk (V := V) (Λ := Λ) n w e = 1 := by
      simp [currentOfWalk_apply (V := V) (Λ := Λ) n w e, hcount]
    simpa [this] using (Nat.succ_le_iff.2 hpos)
  · have hcount : w.edges.count e.1 = 0 := by
      simpa using (List.count_eq_zero_of_not_mem he)
    have : currentOfWalk (V := V) (Λ := Λ) n w e = 0 := by
      simp [currentOfWalk_apply (V := V) (Λ := Λ) n w e, hcount]
    simp [this]

/-! ## Two-point event `HasSubCurrent` ↔ connectivity -/

theorem hasSubCurrent_pair_of_connected
    (n : Current (V := V) Λ) {x y : ↥Λ} (hxy : x ≠ y) (hconn : Connected (V := V) (Λ := Λ) n x y) :
    HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ)) := by
  have hreach : (traceGraph (V := V) (Λ := Λ) n).Reachable x y :=
    (traceGraph_reachable_iff_connected (V := V) (Λ := Λ) n x y).2 hconn
  rcases (SimpleGraph.Reachable.exists_isPath (G := traceGraph (V := V) (Λ := Λ) n) hreach) with ⟨w, hwpath⟩
  refine ⟨currentOfWalk (V := V) (Λ := Λ) n w, ?_, ?_⟩
  · exact currentOfWalk_le_of_isTrail (V := V) (Λ := Λ) n w hwpath.isTrail
  · have : sources (V := V) (Λ := Λ) (currentOfWalk (V := V) (Λ := Λ) n w) = ({x, y} : Finset (↥Λ)) := by
      simpa [hxy] using (sources_currentOfWalk (V := V) (Λ := Λ) n w)
    simp [this]

/-!
The reverse implication (subcurrent with sources `{x,y}` implies connectivity) uses a parity argument:
the number of sources inside any trace cluster is even.
-/

noncomputable def clusterFinset (n : Current (V := V) Λ) (x : ↥Λ) : Finset (↥Λ) := by
  classical
  exact (Finset.univ.filter fun y => Connected (V := V) (Λ := Λ) n x y)

lemma mem_clusterFinset_iff (n : Current (V := V) Λ) (x y : ↥Λ) :
    y ∈ clusterFinset (V := V) (Λ := Λ) n x ↔ Connected (V := V) (Λ := Λ) n x y := by
  simp [clusterFinset]

lemma clusterFinset_closed_of_adj (n : Current (V := V) Λ) {x u v : ↥Λ}
    (hu : u ∈ clusterFinset (V := V) (Λ := Λ) n x) (h : Adj (V := V) (Λ := Λ) n u v) :
    v ∈ clusterFinset (V := V) (Λ := Λ) n x := by
  have hxu : Connected (V := V) (Λ := Λ) n x u := (mem_clusterFinset_iff (V := V) (Λ := Λ) n x u).1 hu
  have huv : Connected (V := V) (Λ := Λ) n u v := Relation.ReflTransGen.single h
  have hxv : Connected (V := V) (Λ := Λ) n x v := Connected.trans (V := V) (Λ := Λ) n hxu huv
  exact (mem_clusterFinset_iff (V := V) (Λ := Λ) n x v).2 hxv

lemma edge_zero_of_boundary_clusterFinset
    (n : Current (V := V) Λ) {x : ↥Λ} {e : Edge (V := V) Λ}
    (h1 : e.1.out.1 ∈ clusterFinset (V := V) (Λ := Λ) n x)
    (h2 : e.1.out.2 ∉ clusterFinset (V := V) (Λ := Λ) n x) :
    n e = 0 := by
  by_contra hne0
  have hpos : 0 < n e := Nat.pos_of_ne_zero hne0
  have hne : (e.1.out.1 : ↥Λ) ≠ e.1.out.2 := by
    intro hEq
    have : Sym2.IsDiag (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) :=
      (Sym2.mk_isDiag_iff (x := e.1.out.1) (y := e.1.out.2)).2 hEq
    have : Sym2.IsDiag (e.1 : Sym2 (↥Λ)) := by
      simpa [Sym2.mk, e.1.out_eq] using this
    exact e.2 this
  have hadj : Adj (V := V) (Λ := Λ) n e.1.out.1 e.1.out.2 := by
    refine ⟨hne, ?_⟩
    have heq : edge (V := V) (Λ := Λ) e.1.out.1 e.1.out.2 hne = e := by
      apply Subtype.ext
      simp [edge, Sym2.mk, e.1.out_eq]
    simpa [heq] using hpos
  have : e.1.out.2 ∈ clusterFinset (V := V) (Λ := Λ) n x :=
    clusterFinset_closed_of_adj (V := V) (Λ := Λ) n (x := x) (u := e.1.out.1) (v := e.1.out.2) h1 hadj
  exact h2 this

lemma edge_zero_of_boundary_clusterFinset_rev
    (n : Current (V := V) Λ) {x : ↥Λ} {e : Edge (V := V) Λ}
    (h1 : e.1.out.2 ∈ clusterFinset (V := V) (Λ := Λ) n x)
    (h2 : e.1.out.1 ∉ clusterFinset (V := V) (Λ := Λ) n x) :
    n e = 0 := by
  by_contra hne0
  have hpos : 0 < n e := Nat.pos_of_ne_zero hne0
  have hne : (e.1.out.1 : ↥Λ) ≠ e.1.out.2 := by
    intro hEq
    have : Sym2.IsDiag (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) :=
      (Sym2.mk_isDiag_iff (x := e.1.out.1) (y := e.1.out.2)).2 hEq
    have : Sym2.IsDiag (e.1 : Sym2 (↥Λ)) := by
      simpa [Sym2.mk, e.1.out_eq] using this
    exact e.2 this
  have hadj12 : Adj (V := V) (Λ := Λ) n e.1.out.1 e.1.out.2 := by
    refine ⟨hne, ?_⟩
    have heq : edge (V := V) (Λ := Λ) e.1.out.1 e.1.out.2 hne = e := by
      apply Subtype.ext
      simp [edge, Sym2.mk, e.1.out_eq]
    simpa [heq] using hpos
  have hadj21 : Adj (V := V) (Λ := Λ) n e.1.out.2 e.1.out.1 :=
    (Adj_comm (V := V) (Λ := Λ) n (x := e.1.out.1) (y := e.1.out.2)).1 hadj12
  have : e.1.out.1 ∈ clusterFinset (V := V) (Λ := Λ) n x :=
    clusterFinset_closed_of_adj (V := V) (Λ := Λ) n (x := x) (u := e.1.out.2) (v := e.1.out.1) h1 hadj21
  exact h2 this

lemma even_sum_degree_clusterFinset (n : Current (V := V) Λ) (x : ↥Λ) :
    Even (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x, degree (V := V) n y) := by
  have hswap :
      (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x, ∑ e : Edge (V := V) Λ,
          if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)
        =
        ∑ e : Edge (V := V) Λ, ∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
          if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0 := by
    simpa using
      (Finset.sum_comm (s := clusterFinset (V := V) (Λ := Λ) n x)
        (t := (Finset.univ : Finset (Edge (V := V) Λ)))
        (f := fun y e => if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
  have hEvenEdge :
      ∀ e : Edge (V := V) Λ,
        Even (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
          if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
    intro e
    by_cases hmem1 : e.1.out.1 ∈ clusterFinset (V := V) (Λ := Λ) n x
    · by_cases hmem2 : e.1.out.2 ∈ clusterFinset (V := V) (Λ := Λ) n x
      · refine ⟨n e, ?_⟩
        have : (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
            if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)
              = 2 * n e := by
          let p : ↥Λ → Prop := fun y => y ∈ (e.1 : Sym2 (↥Λ))
          have hfilter :
              (clusterFinset (V := V) (Λ := Λ) n x).filter p =
                (e.1 : Sym2 (↥Λ)).toFinset := by
            ext y
            constructor
            · intro hy
              have hy' : p y := (Finset.mem_filter.1 hy).2
              simpa [p, Sym2.mem_toFinset] using hy'
            · intro hy
              have hy' : y ∈ (e.1 : Sym2 (↥Λ)) := by
                simpa [Sym2.mem_toFinset] using hy
              have hyCluster : y ∈ clusterFinset (V := V) (Λ := Λ) n x := by
                have : y = e.1.out.1 ∨ y = e.1.out.2 := by
                  have hyOut : y ∈ (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) := by
                    simpa [e.1.out_eq] using hy'
                  exact (Sym2.mem_iff (a := y) (b := e.1.out.1) (c := e.1.out.2)).1 hyOut
                cases this with
                | inl hy1 => simpa [hy1] using hmem1
                | inr hy2 => simpa [hy2] using hmem2
              exact Finset.mem_filter.2 ⟨hyCluster, by simpa [p] using hy'⟩
          calc
            (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x, if p y then n e else 0)
                = ∑ y ∈ (clusterFinset (V := V) (Λ := Λ) n x).filter p, n e := by
                      simpa [p] using
                        (Finset.sum_filter (s := clusterFinset (V := V) (Λ := Λ) n x)
                          (f := fun _y : ↥Λ => n e) (p := p)).symm
            _ = ∑ y ∈ (e.1 : Sym2 (↥Λ)).toFinset, n e := by
                      simp [hfilter]
            _ = ((e.1 : Sym2 (↥Λ)).toFinset.card) * n e := by simp
            _ = 2 * n e := by
                      simpa using
                        congrArg (fun k => k * n e)
                          (Sym2.card_toFinset_of_not_isDiag (z := (e.1 : Sym2 (↥Λ))) e.2)
        simp [two_mul, this]
      · have hzero : n e = 0 :=
          edge_zero_of_boundary_clusterFinset (V := V) (Λ := Λ) n (x := x) (e := e) hmem1 hmem2
        simp [hzero]
    · by_cases hmem2 : e.1.out.2 ∈ clusterFinset (V := V) (Λ := Λ) n x
      · have hzero : n e = 0 :=
          edge_zero_of_boundary_clusterFinset_rev (V := V) (Λ := Λ) n (x := x) (e := e) hmem2 hmem1
        simp [hzero]
      · have hsum0 :
            (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
              if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro y hy
          have hyne : y ∉ (e.1 : Sym2 (↥Λ)) := by
            intro hyEdge
            have : y = e.1.out.1 ∨ y = e.1.out.2 := by
              have hyOut : y ∈ (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) := by
                simpa [e.1.out_eq] using hyEdge
              exact (Sym2.mem_iff (a := y) (b := e.1.out.1) (c := e.1.out.2)).1 hyOut
            cases this with
            | inl hy1 => exact hmem1 (by simpa [hy1] using hy)
            | inr hy2 => exact hmem2 (by simpa [hy2] using hy)
          simp [hyne]
        simp [hsum0]
  have hEven :
      Even (∑ e : Edge (V := V) Λ, ∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
        if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
    have :
        Even (∑ e ∈ (Finset.univ : Finset (Edge (V := V) Λ)),
          ∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
            if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
      refine Finset.induction_on (Finset.univ : Finset (Edge (V := V) Λ)) ?_ ?_
      · simp
      · intro e s he hs
        have heven : Even (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
            if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := hEvenEdge e
        simpa [Finset.sum_insert, he] using (Even.add heven hs)
    simpa using this
  have : (∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x, degree (V := V) n y)
      =
      ∑ e : Edge (V := V) Λ, ∑ y ∈ clusterFinset (V := V) (Λ := Λ) n x,
        if y ∈ (e.1 : Sym2 (↥Λ)) then n e else 0 := by
    simp [degree, hswap]
  simpa [this] using hEven

theorem connected_of_sources_eq_pair
    (n : Current (V := V) Λ) {x y : ↥Λ} (hxy : x ≠ y)
    (hs : sources (V := V) (Λ := Λ) n = ({x, y} : Finset (↥Λ))) :
    Connected (V := V) (Λ := Λ) n x y := by
  classical
  by_contra hconn
  set S : Finset (↥Λ) := clusterFinset (V := V) (Λ := Λ) n x with hS
  have hxS : x ∈ S := by
    simpa [S, clusterFinset] using (Connected.refl (V := V) (Λ := Λ) n x)
  have hyS : y ∉ S := by
    have : ¬ Connected (V := V) (Λ := Λ) n x y := hconn
    simpa [S, clusterFinset] using this
  have hEvenSum : Even (∑ z ∈ S, degree (V := V) n z) :=
    even_sum_degree_clusterFinset (V := V) (Λ := Λ) n x
  have hEvenSourcesInS :
      Even ((S.filter fun z : ↥Λ => Odd (degree (V := V) n z)).card) :=
    (Finset.even_sum_iff_even_card_odd (s := S) (f := fun z : ↥Λ => degree (V := V) n z)).1 hEvenSum
  have hfilterSources :
      S.filter (fun z : ↥Λ => Odd (degree (V := V) n z)) =
        sources (V := V) (Λ := Λ) n ∩ S := by
    ext z
    simp [sources, IsSource, and_comm]
  have h1 : (sources (V := V) (Λ := Λ) n ∩ S) = ({x} : Finset (↥Λ)) := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ sources (V := V) (Λ := Λ) n ∧ z ∈ S :=
        (Finset.mem_inter.1 hz)
      have hzsrc : z = x ∨ z = y := by
        simpa [hs] using hz'.1
      cases hzsrc with
      | inl hzx =>
          simpa [hzx] using (by simp : z ∈ ({x} : Finset (↥Λ)))
      | inr hzy =>
          exfalso
          exact hyS (by simpa [hzy] using hz'.2)
    · intro hz
      have hz' : z = x := by simpa using hz
      refine (Finset.mem_inter.2 ?_)
      refine ⟨?_, ?_⟩
      · have hxsrc : x ∈ sources (V := V) (Λ := Λ) n := by
          simp [hs]
        simpa [hz'] using hxsrc
      · simpa [hz'] using hxS
  have hEvenInter : Even ((sources (V := V) (Λ := Λ) n ∩ S).card) := by
    simpa [hfilterSources] using hEvenSourcesInS
  -- but the set has cardinality `1`
  have : Even (1 : ℕ) := by
    simp [h1] at hEvenInter
  simp at this

theorem connected_of_hasSubCurrent_pair
    (n : Current (V := V) Λ) {x y : ↥Λ} (hxy : x ≠ y)
    (h : HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ))) :
    Connected (V := V) (Λ := Λ) n x y := by
  rcases h with ⟨m, hmn, hmSources⟩
  have hmConn : Connected (V := V) (Λ := Λ) m x y :=
    connected_of_sources_eq_pair (V := V) (Λ := Λ) m (hxy := hxy) (hs := hmSources)
  exact Connected.mono (V := V) (Λ := Λ) hmn hmConn

theorem hasSubCurrent_pair_iff_connected
    (n : Current (V := V) Λ) {x y : ↥Λ} (hxy : x ≠ y) :
    HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ)) ↔
      Connected (V := V) (Λ := Λ) n x y := by
  constructor
  · intro h
    exact connected_of_hasSubCurrent_pair (V := V) (Λ := Λ) n (hxy := hxy) h
  · intro h
    exact hasSubCurrent_pair_of_connected (V := V) (Λ := Λ) n (hxy := hxy) h

end RandomCurrent

end SpinGlass.Papers.Triviality4D
