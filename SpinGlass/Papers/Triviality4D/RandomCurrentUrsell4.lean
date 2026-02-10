import SpinGlass.Papers.Triviality4D.RandomCurrentRepresentation
import SpinGlass.Papers.Triviality4D.RandomCurrentConsequences

/-!
# Ursell-4 identity via random currents (finite volume)

This file formalizes Eq. `(U4)` from `4D_triviality_June_2021_final.tex` in finite volume.

The key inputs are:
- the random-current representation `isingCorr = ZReal / ZReal ∅`,
- the switching lemma,
- the deterministic equivalence `HasSubCurrent {x,y} ↔ Connected x y`,
- the parity fact: each trace-cluster contains an even number of sources.

We state the identity using `PPairReal`, i.e. as a normalized weight ratio (a genuine probability
only after positivity / nonzero normalizations are established).
-/

open scoped BigOperators

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-- Finite-volume Ursell four-point function, defined in terms of `isingCorr`. -/
noncomputable def isingUrsell4
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (x y z t : ↥Λ) : ℝ :=
  isingCorr (V := V) (Λ := Λ) β J ({x, y, z, t} : Finset (↥Λ))
    - (isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ))
        + isingCorr (V := V) (Λ := Λ) β J ({x, z} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({y, t} : Finset (↥Λ))
        + isingCorr (V := V) (Λ := Λ) β J ({x, t} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({y, z} : Finset (↥Λ)))

/-!
## Deterministic 4-source pairing identity

On a current with sources `{x,y,z,t}`, the sum of the three “pairing indicators”
`[z~t] + [y~t] + [y~z]` equals `1` if the sources split into two components, and `3` if they all lie
in one component. This is encoded as the real identity below.
-/

noncomputable def ind (P : Prop) : ℝ := by
  classical
  exact (if P then (1 : ℝ) else 0)

lemma ind_and (P Q : Prop) : ind (P ∧ Q) = ind P * ind Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ind, hP, hQ]

lemma indicator_const_eq_ind_mul {α : Type*} (S : Set α) (r : ℝ) (a : α) :
    S.indicator (fun _x : α => r) a = ind (a ∈ S) * r := by
  classical
  by_cases ha : a ∈ S <;> simp [Set.indicator, ind, ha]

lemma indicator_hasSubCurrent_pair_eq_ind_connected_mul
    {u v : ↥Λ} (huv : u ≠ v) (g : Current (V := V) Λ → ℝ) (n : Current (V := V) Λ) :
    ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({u, v} : Finset (↥Λ))}).indicator g n
      =
      ind (Connected (V := V) (Λ := Λ) n u v) * g n := by
  have hIff :=
    hasSubCurrent_pair_iff_connected (V := V) (Λ := Λ) (n := n) (x := u) (y := v) (hxy := huv)
  by_cases hsub : HasSubCurrent (V := V) (Λ := Λ) n ({u, v} : Finset (↥Λ))
  · have hconn : Connected (V := V) (Λ := Λ) n u v := hIff.1 hsub
    simp [Set.indicator, ind, hsub, hconn]
  · have hconn : ¬ Connected (V := V) (Λ := Λ) n u v := by
      intro hconn
      exact hsub (hIff.2 hconn)
    simp [Set.indicator, ind, hsub, hconn]

abbrev fourSources (x y z t : ↥Λ) : Finset (↥Λ) :=
  ({x, y, z, t} : Finset (↥Λ))

lemma symmDiff_pairXY_pairZT_eq_fourSources
    {x y z t : ↥Λ} (hxz : x ≠ z) (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) :
    symmDiff ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ)) = fourSources (V := V) (Λ := Λ) x y z t := by
  have hdis : Disjoint ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ)) := by
    refine Finset.disjoint_left.2 ?_
    intro u huXY huZT
    have hu : u = x ∨ u = y := by simpa using huXY
    have hu' : u = z ∨ u = t := by simpa using huZT
    rcases hu with rfl | rfl
    · rcases hu' with rfl | rfl
      · exact hxz rfl
      · exact hxt rfl
    · rcases hu' with rfl | rfl
      · exact hyz rfl
      · exact hyt rfl
  have hunion :
      ({x, y} : Finset (↥Λ)) ∪ ({z, t} : Finset (↥Λ)) = ({x, y, z, t} : Finset (↥Λ)) := by
    ext u
    simp [or_left_comm, or_comm]
  calc
    symmDiff ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
        = ({x, y} : Finset (↥Λ)) ∪ ({z, t} : Finset (↥Λ)) := by
            simpa using (Finset.symmDiff_eq_union hdis)
    _ = ({x, y, z, t} : Finset (↥Λ)) := hunion

lemma symmDiff_pairXZ_pairYT_eq_fourSources
    {x y z t : ↥Λ} (hxy : x ≠ y) (hxt : x ≠ t) (hyz : y ≠ z) (hzt : z ≠ t) :
    symmDiff ({x, z} : Finset (↥Λ)) ({y, t} : Finset (↥Λ)) = fourSources (V := V) (Λ := Λ) x y z t := by
  have hdis : Disjoint ({x, z} : Finset (↥Λ)) ({y, t} : Finset (↥Λ)) := by
    refine Finset.disjoint_left.2 ?_
    intro u huXZ huYT
    have hu : u = x ∨ u = z := by simpa using huXZ
    have hu' : u = y ∨ u = t := by simpa using huYT
    rcases hu with rfl | rfl
    · rcases hu' with rfl | rfl
      · exact hxy rfl
      · exact hxt rfl
    · rcases hu' with rfl | rfl
      · exact hyz rfl
      · exact hzt rfl
  have hunion :
      ({x, z} : Finset (↥Λ)) ∪ ({y, t} : Finset (↥Λ)) = ({x, y, z, t} : Finset (↥Λ)) := by
    ext u
    simp [or_left_comm, or_comm]
  calc
    symmDiff ({x, z} : Finset (↥Λ)) ({y, t} : Finset (↥Λ))
        = ({x, z} : Finset (↥Λ)) ∪ ({y, t} : Finset (↥Λ)) := by
            simpa using (Finset.symmDiff_eq_union hdis)
    _ = ({x, y, z, t} : Finset (↥Λ)) := hunion

lemma symmDiff_pairXT_pairYZ_eq_fourSources
    {x y z t : ↥Λ} (hxy : x ≠ y) (hxz : x ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) :
    symmDiff ({x, t} : Finset (↥Λ)) ({y, z} : Finset (↥Λ)) = fourSources (V := V) (Λ := Λ) x y z t := by
  have hdis : Disjoint ({x, t} : Finset (↥Λ)) ({y, z} : Finset (↥Λ)) := by
    refine Finset.disjoint_left.2 ?_
    intro u huXT huYZ
    have hu : u = x ∨ u = t := by simpa using huXT
    have hu' : u = y ∨ u = z := by simpa using huYZ
    rcases hu with rfl | rfl
    · rcases hu' with rfl | rfl
      · exact hxy rfl
      · exact hxz rfl
    · rcases hu' with rfl | rfl
      · exact hyt rfl
      · exact hzt rfl
  have hunion :
      ({x, t} : Finset (↥Λ)) ∪ ({y, z} : Finset (↥Λ)) = ({x, y, z, t} : Finset (↥Λ)) := by
    ext u
    simp [or_left_comm]
  calc
    symmDiff ({x, t} : Finset (↥Λ)) ({y, z} : Finset (↥Λ))
        = ({x, t} : Finset (↥Λ)) ∪ ({y, z} : Finset (↥Λ)) := by
            simpa using (Finset.symmDiff_eq_union hdis)
    _ = ({x, y, z, t} : Finset (↥Λ)) := hunion

/-!
### Switching lemma + connectivity indicator for pair sources

This is a reusable repackaging of `switchingLemma_ZReal_mul`: when `B = {u,v}` is a pair, the event
`HasSubCurrent _ B` is equivalent to `Connected _ u v`, so the RHS becomes a sum with an explicit
indicator `ind (Connected _ u v)`.
-/

theorem switchingLemma_ZReal_mul_pair_eq_tsum_ind_connected
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) {u v : ↥Λ} (huv : u ≠ v) :
    ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ))
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A ({u, v} : Finset (↥Λ)) ∧
            sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0) := by
  have h :=
    switchingLemma_ZReal_mul (V := V) (Λ := Λ) (β := β) (J := J) (A := A)
      (B := ({u, v} : Finset (↥Λ)))
  refine h.trans ?_
  refine tsum_congr ?_
  intro p
  by_cases hsrc :
      sources (V := V) p.1 = symmDiff A ({u, v} : Finset (↥Λ)) ∧
        sources (V := V) p.2 = (∅ : Finset (↥Λ))
  · have hind :
        ({n : Current (V := V) Λ |
              HasSubCurrent (V := V) (Λ := Λ) n ({u, v} : Finset (↥Λ))}).indicator
            (fun _n : Current (V := V) Λ =>
              weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
          =
          ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
            (weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2) := by
      simpa [mul_assoc] using
        (indicator_hasSubCurrent_pair_eq_ind_connected_mul (V := V) (Λ := Λ) (u := u) (v := v)
          (huv := huv)
          (g := fun _n : Current (V := V) Λ =>
            weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2)
          (n := (p.1 + p.2)))
    simp [hsrc, hind, mul_assoc, mul_left_comm, mul_comm]
  · simp [hsrc]

theorem switchingLemma_pair_ind_connected_eq_tsum_ind_and
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) {u v x z : ↥Λ}
    (huv : u ≠ v) :
    (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = ({u, v} : Finset (↥Λ)) then
          ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0)
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A ({u, v} : Finset (↥Λ)) ∧
            sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0) := by
  have hF : ∀ n : Current (V := V) Λ, ‖ind (Connected (V := V) (Λ := Λ) n x z)‖ ≤ (1 : ℝ) := by
    intro n
    by_cases hxz' : Connected (V := V) (Λ := Λ) n x z <;> simp [ind, hxz']
  have h :=
    switchingLemma (V := V) (Λ := Λ) (β := β) (J := J)
      (A := A) (B := ({u, v} : Finset (↥Λ)))
      (F := fun n : Current (V := V) Λ => ind (Connected (V := V) (Λ := Λ) n x z))
      (C := (1 : ℝ)) hF
  refine h.trans ?_
  refine tsum_congr ?_
  intro p
  by_cases hsrc :
      sources (V := V) p.1 = symmDiff A ({u, v} : Finset (↥Λ)) ∧
        sources (V := V) p.2 = (∅ : Finset (↥Λ))
  · have hind :
        ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({u, v} : Finset (↥Λ))}).indicator
            (fun n : Current (V := V) Λ =>
              ind (Connected (V := V) (Λ := Λ) n x z) *
                (weightReal (V := V) (Λ := Λ) β J p.1 *
                  weightReal (V := V) (Λ := Λ) β J p.2))
            (p.1 + p.2)
          =
          ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) *
                (weightReal (V := V) (Λ := Λ) β J p.1 *
                  weightReal (V := V) (Λ := Λ) β J p.2)) := by
      simpa using
        (indicator_hasSubCurrent_pair_eq_ind_connected_mul (V := V) (Λ := Λ) (u := u) (v := v)
          (huv := huv)
          (g := fun n : Current (V := V) Λ =>
            ind (Connected (V := V) (Λ := Λ) n x z) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2))
          (n := (p.1 + p.2)))
    have hind' :
        ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
            (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2))
          =
          ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2) := by
      simp [ind_and, mul_assoc, mul_left_comm, mul_comm]
    simp [hsrc, hind, hind', mul_assoc]
  · simp [hsrc]

/-!
### Helper lemmas for multi-point connectivity

These lemmas factor out small but frequently recurring pieces used in the multi-point
connectivity identities and bounds of Appendix Proposition `prop:3`.
-/

lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  by_cases hP : P
  · have hQ : Q := h.mp hP
    simp [ind, hP, hQ]
  · have hQ : ¬ Q := by
      intro hQ
      exact hP (h.mpr hQ)
    simp [ind, hP, hQ]

lemma symmDiff_pair_pair_eq_pair
    {x y u : ↥Λ} (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u) :
    symmDiff ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ)) = ({x, y} : Finset (↥Λ)) := by
  ext w
  by_cases hwx : w = x
  · subst hwx
    simp [Finset.mem_symmDiff, hxu, hxy]
  by_cases hwy : w = y
  · subst hwy
    simp [Finset.mem_symmDiff, hyu, hwx]
  by_cases hwu : w = u
  · subst w
    have hux : u ≠ x := by simpa [eq_comm] using hxu
    have huy : u ≠ y := by simpa [eq_comm] using hyu
    simp [Finset.mem_symmDiff, hux, huy]
  · simp [Finset.mem_symmDiff, hwx, hwy, hwu]

lemma connected_and_connected_iff_of_sources_eq_pair
    (n : Current (V := V) Λ) {x y u v : ↥Λ}
    (hs : sources (V := V) n = ({x, y} : Finset (↥Λ))) :
    (Connected (V := V) (Λ := Λ) n u v ∧ Connected (V := V) (Λ := Λ) n u y)
      ↔
      (Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v) := by
  have hxy_conn : Connected (V := V) (Λ := Λ) n x y :=
    connected_of_sources_eq_pair (V := V) (Λ := Λ) n (hs := hs)
  constructor
  · intro h
    have hxu : Connected (V := V) (Λ := Λ) n x u :=
      Connected.trans (V := V) (Λ := Λ) n hxy_conn
        (Connected.symm (V := V) (Λ := Λ) n h.2)
    have hxv : Connected (V := V) (Λ := Λ) n x v :=
      Connected.trans (V := V) (Λ := Λ) n hxu h.1
    exact ⟨hxu, hxv⟩
  · intro h
    have huy : Connected (V := V) (Λ := Λ) n u y :=
      Connected.trans (V := V) (Λ := Λ) n
        (Connected.symm (V := V) (Λ := Λ) n h.1) hxy_conn
    have huv : Connected (V := V) (Λ := Λ) n u v :=
      Connected.trans (V := V) (Λ := Λ) n
        (Connected.symm (V := V) (Λ := Λ) n h.1) h.2
    exact ⟨huv, huy⟩

lemma ind_connected_and_connected_eq_of_sources_eq_pair
    (n : Current (V := V) Λ) {x y u v : ↥Λ}
    (hs : sources (V := V) n = ({x, y} : Finset (↥Λ))) :
    ind (Connected (V := V) (Λ := Λ) n u v ∧ Connected (V := V) (Λ := Λ) n u y)
      =
      ind (Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v) := by
  exact ind_congr (connected_and_connected_iff_of_sources_eq_pair (V := V) (Λ := Λ) n
    (x := x) (y := y) (u := u) (v := v) hs)

lemma PPairReal_eq_tsum_ind_mul
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ)) :
    PPairReal (V := V) (Λ := Λ) β J A B S
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
            ind ((p.1 + p.2) ∈ S) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0) /
        (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) := by
  unfold PPairReal
  congr 1
  refine tsum_congr ?_
  intro p
  by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
  · simp [hcond, indicator_const_eq_ind_mul]
  · simp [hcond]

lemma PPairReal_eq_tsum_ind_mul_setOf
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (P : Current (V := V) Λ → Prop) :
    PPairReal (V := V) (Λ := Λ) β J A B {n : Current (V := V) Λ | P n}
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
            ind (P (p.1 + p.2)) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0) /
        (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) := by
  simp [PPairReal_eq_tsum_ind_mul]

/-
## Multi-point connectivity probability (Appendix Proposition `prop:3`)

The proof of the “two-step” bound (Eq. `(prop3b)` in the TeX) starts from a switching-lemma identity
which rewrites the event “`u` and `v` are both connected to the source `x`” under sources `{x,y}` as
the product of:
1) the one-point connection probability of `u` to `x` under sources `{x,y}` (Eq. `(prop2b)`), and
2) a connection probability under sources `{x,u}` and `{u,y}`.

We formalize that algebraic switching step here.
-/

/--
Switching-lemma decomposition of a two-point source-cluster event:
under sources `{x,y}` and `∅`, the event that **both** `u` and `v` are connected to `x` has
normalized weight ratio equal to the “bridge” ratio from `(prop2b)` times a connection probability
under sources `{x,u}` and `{u,y}`.

This matches the first step in the proof of Appendix Proposition `prop:3`, Eq. `(prop3b)`.
-/
theorem PPairReal_connected_and_connected_eq_isingCorr_mul_isingCorr_div_mul_PPairReal_connected
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y u v : ↥Λ}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hZxy : ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0)
    (hZxu : ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ≠ 0)
    (hZuy : ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) ≠ 0) :
    PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ |
          Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v}
      =
      ((isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) *
        PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := by
  have hsymm :
      symmDiff ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ)) = ({x, y} : Finset (↥Λ)) :=
    symmDiff_pair_pair_eq_pair (V := V) (Λ := Λ) (x := x) (y := y) (u := u) hxy hxu hyu
  have hswitch :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, u} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = ({u, y} : Finset (↥Λ)) then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0)
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) u y) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0) := by
    have hswitch0 :
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if sources (V := V) p.1 = ({x, u} : Finset (↥Λ)) ∧
                sources (V := V) p.2 = ({u, y} : Finset (↥Λ)) then
              ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
                  weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2
            else 0)
          =
          (∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
                sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
              ind
                    (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v ∧
                      Connected (V := V) (Λ := Λ) (p.1 + p.2) u y) *
                  weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2
            else 0) := by
      simpa [hsymm] using
        (switchingLemma_pair_ind_connected_eq_tsum_ind_and (V := V) (Λ := Λ) (β := β) (J := J)
          (A := ({x, u} : Finset (↥Λ))) (u := u) (v := y) (x := u) (z := v) hyu.symm)
    simpa [mul_assoc] using hswitch0
  have hconjSum :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) u y) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0)
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) x u ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) x v) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0) := by
    refine tsum_congr ?_
    intro p
    by_cases hsrc :
        sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
          sources (V := V) p.2 = (∅ : Finset (↥Λ))
    · have hsources_total : sources (V := V) (p.1 + p.2) = ({x, y} : Finset (↥Λ)) := by
        have hp2 : sources (V := V) p.2 = (∅ : Finset (↥Λ)) := hsrc.2
        have hp1 : sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) := hsrc.1
        simp [sources_add, hp1, hp2]
      have hind :
          ind
              (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v ∧
                Connected (V := V) (Λ := Λ) (p.1 + p.2) u y)
            =
            ind
              (Connected (V := V) (Λ := Λ) (p.1 + p.2) x u ∧
                Connected (V := V) (Λ := Λ) (p.1 + p.2) x v) :=
        ind_connected_and_connected_eq_of_sources_eq_pair (V := V) (Λ := Λ) (n := (p.1 + p.2))
          (x := x) (y := y) (u := u) (v := v) hsources_total
      simp [hsrc, hind]
    · simp [hsrc]
  have hNumEq :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            ind
                (Connected (V := V) (Λ := Λ) (p.1 + p.2) x u ∧
                  Connected (V := V) (Λ := Λ) (p.1 + p.2) x v) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0)
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, u} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = ({u, y} : Finset (↥Λ)) then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) u v) *
              (weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
          else 0) := by
    exact hconjSum.symm.trans hswitch.symm
  have hZ0 : ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 :=
    ne_of_gt (ZReal_empty_pos (V := V) (Λ := Λ) (β := β) (J := J))
  have hDenT :
      ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
          ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) ≠ 0 :=
    mul_ne_zero hZxu hZuy
  have hDenS :
      ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 :=
    mul_ne_zero hZxy hZ0
  have hratioZ :
      ((isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)))
        =
        (ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ))) /
          (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) := by
    have hyufin : ({y, u} : Finset (↥Λ)) = ({u, y} : Finset (↥Λ)) := by
      ext w; simp [or_comm]
    have hxu' :
        isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) =
          ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
      isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, u} : Finset (↥Λ))
    have hyu' :
        isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ)) =
          ZReal (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ)) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
      isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({y, u} : Finset (↥Λ))
    have hxy' :
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) =
          ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
      isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, y} : Finset (↥Λ))
    rw [hxu', hyu', hxy']
    simp [hyufin]
    have hxy_div :
        (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
              ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) ≠ 0 :=
      div_ne_zero hZxy hZ0
    field_simp [hZ0, hZxy, hZxu, hZuy, hxy_div]
  rw [PPairReal_eq_tsum_ind_mul_setOf (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, y} : Finset (↥Λ))) (B := (∅ : Finset (↥Λ)))
        (P := fun n : Current (V := V) Λ =>
          Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v)]
  rw [PPairReal_eq_tsum_ind_mul_setOf (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, u} : Finset (↥Λ))) (B := ({u, y} : Finset (↥Λ)))
        (P := fun n : Current (V := V) Λ => Connected (V := V) (Λ := Λ) n u v)]
  rw [hNumEq, hratioZ]
  field_simp [hDenS, hDenT]

/--
Paper Appendix Proposition `prop:3`, inequality `(prop3b)` in finite volume, **assuming** the auxiliary
bound `(imp)` on the intermediate two-current law.

This isolates the switching-lemma algebra (proved above) from the monotonicity input used in the paper
to prove `(imp)`.
-/
theorem PPairReal_connected_and_connected_le_twoStep_of_imp
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y u v : ↥Λ}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxv : x ≠ v) (hyv : y ≠ v) (huv : u ≠ v)
    (hZxy : ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0)
    (hZxu : ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ≠ 0)
    (hZuy : ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) ≠ 0)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (himp :
        PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          ≤
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            - PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}) :
    PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ |
          Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v}
      ≤
      (isingCorr (V := V) (Λ := Λ) β J ({x, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))
        +
      (isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({v, y} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  set r : ℝ :=
      ((isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) with hr
  have heq :
      PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ |
            Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v}
        =
        r *
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := by
    simpa [r, hr] using
      (PPairReal_connected_and_connected_eq_isingCorr_mul_isingCorr_div_mul_PPairReal_connected
          (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y) (u := u) (v := v)
          hxy hxu hyu hZxy hZxu hZuy)
  have hnonneg_empty :
      0 ≤
        PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} :=
    PPairReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J)
      (A := (∅ : Finset (↥Λ))) (B := (∅ : Finset (↥Λ)))
      {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} hβJ
  have hle_imp' :
      PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
        ≤
        PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := by
    have hsub :
        (PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
              + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
              -
              PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v})
          ≤
          (PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}) := by
        exact sub_le_self _ hnonneg_empty
    exact le_trans himp hsub
  have hr_mem :
      r ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [r, hr, mul_comm, mul_left_comm, mul_assoc] using
      (isingCorr_mul_isingCorr_div_isingCorr_pair_mem_Icc_of_nonneg (V := V) (Λ := Λ)
        (β := β) (J := J) (x := x) (y := y) (u := u) hxy hxu hyu hβJ)
  have hr_nonneg : 0 ≤ r := (Set.mem_Icc.mp hr_mem).1
  have hmul :
      r *
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
        ≤
        r *
          (PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}) :=
    mul_le_mul_of_nonneg_left hle_imp' hr_nonneg
  have hxufin : ({x, u} : Finset (↥Λ)) = ({u, x} : Finset (↥Λ)) := by
    ext w; simp [or_comm]
  have hyufin : ({y, u} : Finset (↥Λ)) = ({u, y} : Finset (↥Λ)) := by
    ext w; simp [or_comm]
  have hterm1 :
      r *
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
        =
        (isingCorr (V := V) (Λ := Λ) β J ({x, v} : Finset (↥Λ)) *
              isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
    have hP :
        PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          =
          (isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
                isingCorr (V := V) (Λ := Λ) β J ({x, v} : Finset (↥Λ))) /
            isingCorr (V := V) (Λ := Λ) β J ({u, x} : Finset (↥Λ)) := by
      simpa [hxufin, mul_comm, mul_left_comm, mul_assoc] using
        (PPairReal_connected_eq_isingCorr_mul_isingCorr_div (V := V) (Λ := Λ) (β := β) (J := J)
          (x := u) (y := x) (u := v) hxu.symm huv hxv)
    have hZ0 : ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 :=
      ne_of_gt (ZReal_empty_pos (V := V) (Λ := Λ) (β := β) (J := J))
    have hCorr_xu :
        isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ≠ 0 := by
      have hxucorr :
          isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) =
            ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) /
              ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
        isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, u} : Finset (↥Λ))
      simpa [hxucorr] using div_ne_zero hZxu hZ0
    have hxucorr' :
        isingCorr (V := V) (Λ := Λ) β J ({u, x} : Finset (↥Λ)) ≠ 0 := by
      simpa [hxufin] using hCorr_xu
    rw [hP, hr]
    field_simp [hCorr_xu, hxucorr']
    simp [hxufin, hyufin]
    ring_nf
  have hterm2 :
      r *
          PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
        =
        (isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
              isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({v, y} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
    have hcomm :
        PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          =
          PPairReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := by
      simpa using (PPairReal_comm (V := V) (Λ := Λ) (β := β) (J := J)
        (A := (∅ : Finset (↥Λ))) (B := ({u, y} : Finset (↥Λ)))
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v})
    have hP :
        PPairReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          =
          (isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
                isingCorr (V := V) (Λ := Λ) β J ({y, v} : Finset (↥Λ))) /
            isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (PPairReal_connected_eq_isingCorr_mul_isingCorr_div (V := V) (Λ := Λ) (β := β) (J := J)
          (x := u) (y := y) (u := v) hyu.symm huv hyv)
    have hZ0 : ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 :=
      ne_of_gt (ZReal_empty_pos (V := V) (Λ := Λ) (β := β) (J := J))
    have hCorr_uy :
        isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) ≠ 0 := by
      have huycorr :
          isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) =
            ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) /
              ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
        isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({u, y} : Finset (↥Λ))
      simpa [huycorr] using div_ne_zero hZuy hZ0
    rw [hcomm, hP, hr]
    field_simp [hCorr_uy]
    have hyvfin : ({y, v} : Finset (↥Λ)) = ({v, y} : Finset (↥Λ)) := by
      ext w; simp [or_comm]
    simp [hyufin, hyvfin]
    ring_nf

  -- Put everything together.
  calc
    PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ |
          Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v}
        =
        r *
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := heq
    _ ≤
        r *
          (PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}) := hmul
    _ =
        r *
            PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          +
          r *
            PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v} := by
        ring
    _ =
        (isingCorr (V := V) (Λ := Λ) β J ({x, v} : Finset (↥Λ)) *
              isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))
          +
          (isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
              isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({v, y} : Finset (↥Λ))) /
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
        simp [hterm1, hterm2]

lemma one_sub_pairings_ind_eq
    (n : Current (V := V) Λ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hs : sources (V := V) (Λ := Λ) n = fourSources (V := V) (Λ := Λ) x y z t) :
    (1 : ℝ)
        -
        (ind (Connected (V := V) (Λ := Λ) n z t) +
          ind (Connected (V := V) (Λ := Λ) n y t) +
          ind (Connected (V := V) (Λ := Λ) n y z))
      =
      (-2 : ℝ) * ind (Connected (V := V) (Λ := Λ) n x z ∧ Connected (V := V) (Λ := Λ) n z t) := by
  classical
  have hall_implies (hall : Connected (V := V) (Λ := Λ) n x z ∧ Connected (V := V) (Λ := Λ) n z t) :
      Connected (V := V) (Λ := Λ) n y z ∧ Connected (V := V) (Λ := Λ) n y t := by
    set S : Finset (↥Λ) := clusterFinset (V := V) (Λ := Λ) n x with hS
    have hxS : x ∈ S := by
      simpa [S, clusterFinset] using (Connected.refl (V := V) (Λ := Λ) n x)
    have hzS : z ∈ S := by
      simpa [S, clusterFinset] using hall.1
    have htS : t ∈ S := by
      have hxt' : Connected (V := V) (Λ := Λ) n x t :=
        Connected.trans (V := V) (Λ := Λ) n hall.1 hall.2
      simpa [S, clusterFinset] using hxt'
    have hEven : Even ((sources (V := V) (Λ := Λ) n ∩ S).card) := by
      simpa [S] using even_card_sources_inter_clusterFinset (V := V) (Λ := Λ) n x
    have hyS : y ∈ S := by
      by_contra hyS
      have hcard : (sources (V := V) (Λ := Λ) n ∩ S).card = 3 := by
        have hEq : sources (V := V) (Λ := Λ) n ∩ S = ({x, z, t} : Finset (↥Λ)) := by
          ext u
          constructor
          · intro hu
            have hus : u ∈ sources (V := V) (Λ := Λ) n := (Finset.mem_inter.1 hu).1
            have huS : u ∈ S := (Finset.mem_inter.1 hu).2
            have : u = x ∨ u = y ∨ u = z ∨ u = t := by
              simpa [hs, fourSources] using hus
            rcases this with rfl | rfl | rfl | rfl
            · simp
            · exfalso; exact hyS (by simpa using huS)
            · simp
            · simp
          · intro hu
            have hu' : u = x ∨ u = z ∨ u = t := by simpa [fourSources] using hu
            refine Finset.mem_inter.2 ⟨?_, ?_⟩
            · rcases hu' with rfl | rfl | rfl <;> simp [hs, fourSources]
            · rcases hu' with rfl | rfl | rfl <;> first | exact hxS | exact hzS | exact htS
        simp [hEq, hxz, hxt, hzt]
      have : ¬ Even ((sources (V := V) (Λ := Λ) n ∩ S).card) := by
        simpa [hcard] using (show ¬ Even (3 : ℕ) from by decide)
      exact this hEven
    have hxy' : Connected (V := V) (Λ := Λ) n x y := by
      simpa [S, clusterFinset] using hyS
    have hyz' : Connected (V := V) (Λ := Λ) n y z :=
      Connected.trans (V := V) (Λ := Λ) n (Connected.symm (V := V) (Λ := Λ) n hxy') hall.1
    have hyt' : Connected (V := V) (Λ := Λ) n y t := by
      have hxt' : Connected (V := V) (Λ := Λ) n x t :=
        Connected.trans (V := V) (Λ := Λ) n hall.1 hall.2
      exact Connected.trans (V := V) (Λ := Λ) n (Connected.symm (V := V) (Λ := Λ) n hxy') hxt'
    exact ⟨hyz', hyt'⟩
  have all3_implies_hall
      (hzt_conn : Connected (V := V) (Λ := Λ) n z t)
      (hyt_conn : Connected (V := V) (Λ := Λ) n y t)
      (hyz_conn : Connected (V := V) (Λ := Λ) n y z) :
      Connected (V := V) (Λ := Λ) n x z ∧ Connected (V := V) (Λ := Λ) n z t := by
    set Sy : Finset (↥Λ) := clusterFinset (V := V) (Λ := Λ) n y with hSy
    have hySy : y ∈ Sy := by
      simpa [Sy, clusterFinset] using (Connected.refl (V := V) (Λ := Λ) n y)
    have hzSy : z ∈ Sy := by simpa [Sy, clusterFinset] using hyz_conn
    have htSy : t ∈ Sy := by simpa [Sy, clusterFinset] using hyt_conn
    have hEvenY : Even ((sources (V := V) (Λ := Λ) n ∩ Sy).card) := by
      simpa [Sy] using even_card_sources_inter_clusterFinset (V := V) (Λ := Λ) n y
    have hxSy : x ∈ Sy := by
      by_contra hxSy
      have hcard : (sources (V := V) (Λ := Λ) n ∩ Sy).card = 3 := by
        have hEq : sources (V := V) (Λ := Λ) n ∩ Sy = ({y, z, t} : Finset (↥Λ)) := by
          ext u
          constructor
          · intro hu
            have hus : u ∈ sources (V := V) (Λ := Λ) n := (Finset.mem_inter.1 hu).1
            have huSy : u ∈ Sy := (Finset.mem_inter.1 hu).2
            have : u = x ∨ u = y ∨ u = z ∨ u = t := by
              simpa [hs, fourSources] using hus
            rcases this with rfl | rfl | rfl | rfl
            · exfalso; exact hxSy (by simpa using huSy)
            · simp
            · simp
            · simp
          · intro hu
            have hu' : u = y ∨ u = z ∨ u = t := by simpa [fourSources] using hu
            refine Finset.mem_inter.2 ⟨?_, ?_⟩
            · rcases hu' with rfl | rfl | rfl <;> simp [hs, fourSources]
            · rcases hu' with rfl | rfl | rfl <;> first | exact hySy | exact hzSy | exact htSy
        simp [hEq, hyz, hyt, hzt]
      have : ¬ Even ((sources (V := V) (Λ := Λ) n ∩ Sy).card) := by
        simpa [hcard] using (show ¬ Even (3 : ℕ) from by decide)
      exact this hEvenY
    have hxy : Connected (V := V) (Λ := Λ) n x y := by
      have : Connected (V := V) (Λ := Λ) n y x := by
        simpa [Sy, clusterFinset] using hxSy
      exact Connected.symm (V := V) (Λ := Λ) n this
    have hxz : Connected (V := V) (Λ := Λ) n x z :=
      Connected.trans (V := V) (Λ := Λ) n hxy hyz_conn
    exact ⟨hxz, hzt_conn⟩
  by_cases hall : Connected (V := V) (Λ := Λ) n x z ∧ Connected (V := V) (Λ := Λ) n z t
  · have hpair := hall_implies hall
    simp [ind, hall, hpair.1, hpair.2]
    norm_num
  · have hnotAll3 :
        ¬ (Connected (V := V) (Λ := Λ) n z t ∧
            Connected (V := V) (Λ := Λ) n y t ∧
            Connected (V := V) (Λ := Λ) n y z) := by
      intro hAll
      exact hall (all3_implies_hall hAll.1 hAll.2.1 hAll.2.2)
    have hSome :
        Connected (V := V) (Λ := Λ) n z t ∨
          Connected (V := V) (Λ := Λ) n y t ∨
            Connected (V := V) (Λ := Λ) n y z := by
      by_contra hnone
      have hztF : ¬ Connected (V := V) (Λ := Λ) n z t := by
        intro hzt
        exact hnone (Or.inl hzt)
      have hytF : ¬ Connected (V := V) (Λ := Λ) n y t := by
        intro hyt
        exact hnone (Or.inr (Or.inl hyt))
      have hyzF : ¬ Connected (V := V) (Λ := Λ) n y z := by
        intro hyz
        exact hnone (Or.inr (Or.inr hyz))
      have hxz : Connected (V := V) (Λ := Λ) n x z := by
        set Sz : Finset (↥Λ) := clusterFinset (V := V) (Λ := Λ) n z with hSz
        have hzSz : z ∈ Sz := by
          simpa [Sz, clusterFinset] using (Connected.refl (V := V) (Λ := Λ) n z)
        have hEvenZ : Even ((sources (V := V) (Λ := Λ) n ∩ Sz).card) := by
          simpa [Sz] using even_card_sources_inter_clusterFinset (V := V) (Λ := Λ) n z
        have hySz : y ∉ Sz := by
          have : ¬ Connected (V := V) (Λ := Λ) n z y := by
            intro hzy
            exact hyzF (Connected.symm (V := V) (Λ := Λ) n hzy)
          simpa [Sz, clusterFinset] using this
        have htSz : t ∉ Sz := by
          simpa [Sz, clusterFinset] using hztF
        have hxSz : x ∈ Sz := by
          by_contra hxSz
          have hcard : (sources (V := V) (Λ := Λ) n ∩ Sz).card = 1 := by
            have hEq : sources (V := V) (Λ := Λ) n ∩ Sz = ({z} : Finset (↥Λ)) := by
              ext u
              constructor
              · intro hu
                have hus : u ∈ sources (V := V) (Λ := Λ) n := (Finset.mem_inter.1 hu).1
                have huSz : u ∈ Sz := (Finset.mem_inter.1 hu).2
                have : u = x ∨ u = y ∨ u = z ∨ u = t := by
                  simpa [hs, fourSources] using hus
                rcases this with rfl | rfl | rfl | rfl
                · exfalso; exact hxSz (by simpa using huSz)
                · exfalso; exact hySz (by simpa using huSz)
                · simp
                · exfalso; exact htSz (by simpa using huSz)
              · intro hu
                have hu' : u = z := by simpa using hu
                subst hu'
                refine Finset.mem_inter.2 ⟨?_, ?_⟩
                · simp [hs, fourSources]
                · exact hzSz
            simp [hEq]
          have : ¬ Even ((sources (V := V) (Λ := Λ) n ∩ Sz).card) := by
            simp [hcard]
          exact this hEvenZ
        have hzx : Connected (V := V) (Λ := Λ) n z x := by
          simpa [Sz, clusterFinset] using hxSz
        exact Connected.symm (V := V) (Λ := Λ) n hzx
      have hxt : Connected (V := V) (Λ := Λ) n x t := by
        set St : Finset (↥Λ) := clusterFinset (V := V) (Λ := Λ) n t with hSt
        have htSt : t ∈ St := by
          simpa [St, clusterFinset] using (Connected.refl (V := V) (Λ := Λ) n t)
        have hEvenT : Even ((sources (V := V) (Λ := Λ) n ∩ St).card) := by
          simpa [St] using even_card_sources_inter_clusterFinset (V := V) (Λ := Λ) n t
        have hySt : y ∉ St := by
          have : ¬ Connected (V := V) (Λ := Λ) n t y := by
            intro hty
            exact hytF (Connected.symm (V := V) (Λ := Λ) n hty)
          simpa [St, clusterFinset] using this
        have hzSt : z ∉ St := by
          have : ¬ Connected (V := V) (Λ := Λ) n t z := by
            intro htz
            exact hztF (Connected.symm (V := V) (Λ := Λ) n htz)
          simpa [St, clusterFinset] using this
        have hxSt : x ∈ St := by
          by_contra hxSt
          have hcard : (sources (V := V) (Λ := Λ) n ∩ St).card = 1 := by
            have hEq : sources (V := V) (Λ := Λ) n ∩ St = ({t} : Finset (↥Λ)) := by
              ext u
              constructor
              · intro hu
                have hus : u ∈ sources (V := V) (Λ := Λ) n := (Finset.mem_inter.1 hu).1
                have huSt : u ∈ St := (Finset.mem_inter.1 hu).2
                have : u = x ∨ u = y ∨ u = z ∨ u = t := by
                  simpa [hs, fourSources] using hus
                rcases this with rfl | rfl | rfl | rfl
                · exfalso; exact hxSt (by simpa using huSt)
                · exfalso; exact hySt (by simpa using huSt)
                · exfalso; exact hzSt (by simpa using huSt)
                · simp
              · intro hu
                have hu' : u = t := by simpa using hu
                subst hu'
                refine Finset.mem_inter.2 ⟨?_, ?_⟩
                · simp [hs, fourSources]
                · exact htSt
            simp [hEq]
          have : ¬ Even ((sources (V := V) (Λ := Λ) n ∩ St).card) := by
            simp [hcard]
          exact this hEvenT
        have htx : Connected (V := V) (Λ := Λ) n t x := by
          simpa [St, clusterFinset] using hxSt
        exact Connected.symm (V := V) (Λ := Λ) n htx
      have hzt : Connected (V := V) (Λ := Λ) n z t :=
        Connected.trans (V := V) (Λ := Λ) n (Connected.symm (V := V) (Λ := Λ) n hxz) hxt
      exact hall ⟨hxz, hzt⟩
    rcases hSome with hzt | hyt | hyz
    · have hytF : ¬ Connected (V := V) (Λ := Λ) n y t := by
        intro hyt
        have hyz : Connected (V := V) (Λ := Λ) n y z :=
          Connected.trans (V := V) (Λ := Λ) n hyt (Connected.symm (V := V) (Λ := Λ) n hzt)
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      have hyzF : ¬ Connected (V := V) (Λ := Λ) n y z := by
        intro hyz
        have hyt : Connected (V := V) (Λ := Λ) n y t :=
          Connected.trans (V := V) (Λ := Λ) n hyz hzt
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      have hxzF : ¬ Connected (V := V) (Λ := Λ) n x z := by
        intro hxz
        exact hall ⟨hxz, hzt⟩
      simp [ind, hzt, hytF, hyzF, hxzF]
    · have hztF : ¬ Connected (V := V) (Λ := Λ) n z t := by
        intro hzt
        have hyz : Connected (V := V) (Λ := Λ) n y z :=
          Connected.trans (V := V) (Λ := Λ) n hyt (Connected.symm (V := V) (Λ := Λ) n hzt)
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      have hyzF : ¬ Connected (V := V) (Λ := Λ) n y z := by
        intro hyz
        have hzt : Connected (V := V) (Λ := Λ) n z t :=
          Connected.trans (V := V) (Λ := Λ) n (Connected.symm (V := V) (Λ := Λ) n hyz) hyt
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      simp [ind, hyt, hztF, hyzF]
    · have hztF : ¬ Connected (V := V) (Λ := Λ) n z t := by
        intro hzt
        have hyt : Connected (V := V) (Λ := Λ) n y t :=
          Connected.trans (V := V) (Λ := Λ) n hyz hzt
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      have hytF : ¬ Connected (V := V) (Λ := Λ) n y t := by
        intro hyt
        have hzt : Connected (V := V) (Λ := Λ) n z t :=
          Connected.trans (V := V) (Λ := Λ) n (Connected.symm (V := V) (Λ := Λ) n hyz) hyt
        exact hnotAll3 ⟨hzt, hyt, hyz⟩
      simp [ind, hyz, hztF, hytF]

/-!
## A `ZReal`-level Ursell-4 identity (unnormalized)

This is the core random-current computation behind Eq. `(U4)`: after rewriting each product
`ZReal A * ZReal B` using the switching lemma to a common-source sum (sources `{x,y,z,t}` and `∅`),
the deterministic pairing identity `one_sub_pairings_ind_eq` is applied pointwise, and the
remaining sum is switched back to sources `({x,y},{z,t})` using `switchingLemma` with
`F n = ind (Connected n x z)`.
-/

/-- Core `ZReal` identity behind the Ursell-4 formula. -/
theorem ZReal_fourSources_mul_ZReal_empty_sub_pairings_eq_tsum_connected
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) :
    ZReal (V := V) (Λ := Λ) β J (fourSources (V := V) (Λ := Λ) x y z t) *
        ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
      -
      (ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ))
          +
          ZReal (V := V) (Λ := Λ) β J ({x, z} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({y, t} : Finset (↥Λ))
          +
          ZReal (V := V) (Λ := Λ) β J ({x, t} : Finset (↥Λ)) *
            ZReal (V := V) (Λ := Λ) β J ({y, z} : Finset (↥Λ)))
      =
      (-2 : ℝ) *
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = ({z, t} : Finset (↥Λ)) then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2
          else 0) := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let S4 : Finset (↥Λ) := fourSources (V := V) (Λ := Λ) x y z t
  let cond4 : (Current (V := V) Λ × Current (V := V) Λ) → Prop :=
    fun p => sources (V := V) p.1 = S4 ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ))
  let wprod : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p => w p.1 * w p.2
  have hBase :
      ZReal (V := V) (Λ := Λ) β J S4 * ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = S4 ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
            wprod p
          else 0) := by
    simpa [wprod, w, S4] using
      (ZReal_mul_ZReal_eq_tsum_pair (V := V) (Λ := Λ) (β := β) (J := J)
        (A := S4) (B := (∅ : Finset (↥Λ))))
  have hXY_ZT :
      ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ))
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
          else 0) := by
    have h :=
      switchingLemma_ZReal_mul_pair_eq_tsum_ind_connected (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, y} : Finset (↥Λ))) (u := z) (v := t) (huv := hzt)
    simpa [cond4, wprod, w, S4, mul_assoc,
      symmDiff_pairXY_pairZT_eq_fourSources (V := V) (Λ := Λ) (x := x) (y := y) (z := z) (t := t)
        (hxz := hxz) (hxt := hxt) (hyz := hyz) (hyt := hyt)] using h
  have hXZ_YT :
      ZReal (V := V) (Λ := Λ) β J ({x, z} : Finset (↥Λ)) *
          ZReal (V := V) (Λ := Λ) β J ({y, t} : Finset (↥Λ))
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t) * wprod p
          else 0) := by
    have h :=
      switchingLemma_ZReal_mul_pair_eq_tsum_ind_connected (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, z} : Finset (↥Λ))) (u := y) (v := t) (huv := hyt)
    simpa [cond4, wprod, w, S4, mul_assoc,
      symmDiff_pairXZ_pairYT_eq_fourSources (V := V) (Λ := Λ) (x := x) (y := y) (z := z) (t := t)
        (hxy := hxy) (hxt := hxt) (hyz := hyz) (hzt := hzt)] using h
  have hXT_YZ :
      ZReal (V := V) (Λ := Λ) β J ({x, t} : Finset (↥Λ)) *
          ZReal (V := V) (Λ := Λ) β J ({y, z} : Finset (↥Λ))
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z) * wprod p
          else 0) := by
    have h :=
      switchingLemma_ZReal_mul_pair_eq_tsum_ind_connected (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, t} : Finset (↥Λ))) (u := y) (v := z) (huv := hyz)
    simpa [cond4, wprod, w, S4, mul_assoc,
      symmDiff_pairXT_pairYZ_eq_fourSources (V := V) (Λ := Λ) (x := x) (y := y) (z := z) (t := t)
        (hxy := hxy) (hxz := hxz) (hyt := hyt) (hzt := hzt)] using h
  have hsWeight :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        ‖w p.1‖ * ‖w p.2‖) :=
    summable_norm_weightReal_mul_norm_weightReal (V := V) (Λ := Λ) (β := β) J
  have hsBaseFun :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        if cond4 p then wprod p else 0) := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : cond4 p <;> simp [hcond, wprod, w, norm_mul, mul_nonneg]
  have hsZT :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p else 0) := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : cond4 p
    · by_cases hzt' : Connected (V := V) (Λ := Λ) (p.1 + p.2) z t <;>
        simp [hcond, ind, hzt', wprod, w, norm_mul, mul_nonneg]
    · simp [hcond, mul_nonneg]
  have hsYT :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t) * wprod p else 0) := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : cond4 p
    · by_cases hyt' : Connected (V := V) (Λ := Λ) (p.1 + p.2) y t <;>
        simp [hcond, ind, hyt', wprod, w, norm_mul, mul_nonneg]
    · simp [hcond, mul_nonneg]
  have hsYZ :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z) * wprod p else 0) := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : cond4 p
    · by_cases hyz' : Connected (V := V) (Λ := Λ) (p.1 + p.2) y z <;>
        simp [hcond, ind, hyz', wprod, w, norm_mul, mul_nonneg]
    · simp [hcond, mul_nonneg]
  let fZT : Current (V := V) Λ × Current (V := V) Λ → ℝ :=
    fun p => if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p else 0
  let fYT : Current (V := V) Λ × Current (V := V) Λ → ℝ :=
    fun p => if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t) * wprod p else 0
  let fYZ : Current (V := V) Λ × Current (V := V) Λ → ℝ :=
    fun p => if cond4 p then ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z) * wprod p else 0
  have hsZT' : Summable fZT := by simpa [fZT] using hsZT
  have hsYT' : Summable fYT := by simpa [fYT] using hsYT
  have hsYZ' : Summable fYZ := by simpa [fYZ] using hsYZ
  have hSumPairings :
      (∑' p, fZT p) + (∑' p, fYT p) + (∑' p, fYZ p) = ∑' p, (fZT p + fYT p + fYZ p) := by
    calc
      (∑' p, fZT p) + (∑' p, fYT p) + (∑' p, fYZ p)
          = ((∑' p, fZT p) + (∑' p, fYT p)) + (∑' p, fYZ p) := by
              simp [add_assoc]
      _ = (∑' p, (fZT p + fYT p)) + (∑' p, fYZ p) := by
            simpa using congrArg (fun r => r + (∑' p, fYZ p)) (hsZT'.tsum_add hsYT').symm
      _ = ∑' p, ((fZT p + fYT p) + fYZ p) := by
            simpa using ( (hsZT'.add hsYT').tsum_add hsYZ' ).symm
      _ = ∑' p, (fZT p + fYT p + fYZ p) := by
            refine tsum_congr ?_
            intro p
            simp [add_assoc]
  have hDiff :
      ZReal (V := V) (Λ := Λ) β J S4 * ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
        -
        ((ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)))
          +
          (ZReal (V := V) (Λ := Λ) β J ({x, z} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({y, t} : Finset (↥Λ)))
          +
          (ZReal (V := V) (Λ := Λ) β J ({x, t} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({y, z} : Finset (↥Λ))))
        =
        ∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
              ((1 : ℝ) -
                  (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) +
                    ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t) +
                    ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z))) * wprod p
            else 0 := by
    rw [hBase, hXY_ZT, hXZ_YT, hXT_YZ]
    have hPair :
        (∑' p, fZT p) + (∑' p, fYT p) + (∑' p, fYZ p) = ∑' p, (fZT p + fYT p + fYZ p) := hSumPairings
    have hsPairFun : Summable (fun p => fZT p + fYT p + fYZ p) := (hsZT'.add hsYT').add hsYZ'
    rw [hPair]
    have := (hsBaseFun.tsum_sub hsPairFun).symm
    refine this.trans ?_
    refine tsum_congr ?_
    intro p
    by_cases hcond : cond4 p
    · simp [hcond, fZT, fYT, fYZ, wprod, sub_mul, add_mul, add_assoc]
    · simp [hcond, fZT, fYT, fYZ, wprod]
  have hMain :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
              ((1 : ℝ) -
                  ((ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t)) +
                    (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t)) +
                    (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z)))) * wprod p
            else 0)
        =
        (-2 : ℝ) *
          ∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if cond4 p then
                ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                      Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
              else 0 := by
    have hPoint :
        (fun p : Current (V := V) Λ × Current (V := V) Λ =>
            if cond4 p then
                ((1 : ℝ) -
                    ((ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t)) +
                      (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t)) +
                      (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z)))) * wprod p
              else 0)
          =
          (fun p : Current (V := V) Λ × Current (V := V) Λ =>
            (-2 : ℝ) *
              if cond4 p then
                  ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                        Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
                else 0) := by
      funext p
      by_cases hcond : cond4 p
      · have hsTot : sources (V := V) (Λ := Λ) (p.1 + p.2) = S4 := by
          have hs :=
            sources_add (V := V) (Λ := Λ) (n1 := p.1) (n2 := p.2)
          have hs' : sources (V := V) (Λ := Λ) (p.1 + p.2) = symmDiff S4 (∅ : Finset (↥Λ)) := by
            simpa [cond4, S4, hcond] using hs
          have hbot : symmDiff S4 (∅ : Finset (↥Λ)) = S4 := by simp
          exact hs'.trans hbot
        have hPair :=
          one_sub_pairings_ind_eq (V := V) (Λ := Λ) (n := (p.1 + p.2))
            (hxy := hxy) (hxz := hxz) (hxt := hxt) (hyz := hyz) (hyt := hyt) (hzt := hzt)
            (hs := hsTot)
        have hMul := congrArg (fun r : ℝ => r * wprod p) hPair
        simpa [hcond, wprod, mul_assoc, mul_left_comm, mul_comm, add_assoc] using hMul
      · simp [hcond]
    calc
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
              ((1 : ℝ) -
                  ((ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t)) +
                    (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t)) +
                    (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z)))) * wprod p
            else 0)
          =
          ∑' p : Current (V := V) Λ × Current (V := V) Λ,
            (-2 : ℝ) *
              if cond4 p then
                  ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                        Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
                else 0 := by
            simp [hPoint]
      _ = (-2 : ℝ) *
          ∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if cond4 p then
                ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                      Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
              else 0 := by
            simpa [mul_assoc] using
              (tsum_mul_left (a := (-2 : ℝ))
                (f := fun p : Current (V := V) Λ × Current (V := V) Λ =>
                  if cond4 p then
                      ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                            Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
                    else 0))
  have hSwitch :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = ({z, t} : Finset (↥Λ)) then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) * wprod p
          else 0)
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
              ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                    Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
            else 0) := by
    have h :=
      switchingLemma_pair_ind_connected_eq_tsum_ind_and (V := V) (Λ := Λ) (β := β) (J := J)
        (A := ({x, y} : Finset (↥Λ))) (u := z) (v := t) (x := x) (z := z) (huv := hzt)
    simpa [cond4, wprod, w, S4, mul_assoc,
      symmDiff_pairXY_pairZT_eq_fourSources (V := V) (Λ := Λ) (x := x) (y := y) (z := z) (t := t)
        (hxz := hxz) (hxt := hxt) (hyz := hyz) (hyt := hyt)] using h
  calc
    ZReal (V := V) (Λ := Λ) β J S4 * ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
        -
        ((ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)))
          +
          (ZReal (V := V) (Λ := Λ) β J ({x, z} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({y, t} : Finset (↥Λ)))
          +
          (ZReal (V := V) (Λ := Λ) β J ({x, t} : Finset (↥Λ)) *
              ZReal (V := V) (Λ := Λ) β J ({y, z} : Finset (↥Λ))))
        =
        ∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if cond4 p then
              ((1 : ℝ) -
                  (ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) +
                    ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y t) +
                    ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) y z))) * wprod p
            else 0 := hDiff
    _ = (-2 : ℝ) *
          ∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if cond4 p then
                ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z ∧
                      Connected (V := V) (Λ := Λ) (p.1 + p.2) z t) * wprod p
              else 0 := hMain
    _ = (-2 : ℝ) *
          (∑' p : Current (V := V) Λ × Current (V := V) Λ,
            if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
                sources (V := V) p.2 = ({z, t} : Finset (↥Λ)) then
              ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) * wprod p
            else 0) := by
          simpa [mul_assoc] using congrArg (fun r => (-2 : ℝ) * r) hSwitch.symm
    _ = (-2 : ℝ) *
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
              sources (V := V) p.2 = ({z, t} : Finset (↥Λ)) then
            ind (Connected (V := V) (Λ := Λ) (p.1 + p.2) x z) *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2
          else 0) := by
          congr 1
          refine tsum_congr ?_
          intro p
          by_cases hcond :
              sources (V := V) p.1 = ({x, y} : Finset (↥Λ)) ∧
                sources (V := V) p.2 = ({z, t} : Finset (↥Λ))
          · simp [hcond, wprod, w, mul_assoc]
          · simp [hcond]

/-!
## Eq. (U4)

We now prove the finite-volume Ursell-4 identity.

To match the “probability” form in the paper, we assume the *pair* normalizing factors `Z_{xy}`,
`Z_{zt}` are nonzero. (The empty-source sum `Z_∅` is always nonzero; see `ZReal_empty_ne_zero`.)
-/

theorem isingUrsell4_eq
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hZxy : ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0)
    (hZzt : ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) ≠ 0) :
    isingUrsell4 (V := V) (Λ := Λ) β J x y z t
      =
      -2 *
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
        isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} := by
  have hZ0 : ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 :=
    ZReal_empty_ne_zero (V := V) (Λ := Λ) (β := β) (J := J)
  have hCorr4 :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, y, z, t} : Finset (↥Λ))
  have hCorrXY :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, y} : Finset (↥Λ))
  have hCorrZT :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({z, t} : Finset (↥Λ))
  have hCorrXZ :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, z} : Finset (↥Λ))
  have hCorrYT :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({y, t} : Finset (↥Λ))
  have hCorrXT :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, t} : Finset (↥Λ))
  have hCorrYZ :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({y, z} : Finset (↥Λ))
  unfold isingUrsell4
  simp [hCorr4, hCorrXY, hCorrZT, hCorrXZ, hCorrYT, hCorrXT, hCorrYZ,
    PPairReal, indicator_const_eq_ind_mul, mul_assoc, mul_comm]
  field_simp [hZ0, hZxy, hZzt]
  simpa [fourSources, mul_assoc, mul_left_comm, mul_comm] using
    (ZReal_fourSources_mul_ZReal_empty_sub_pairings_eq_tsum_connected (V := V) (Λ := Λ)
      (β := β) (J := J) (x := x) (y := y) (z := z) (t := t) hxy hxz hxt hyz hyt hzt)

/--
Eq. (U4), with the nonvanishing hypotheses discharged under a simple “ferromagnetic positivity”
assumption: `β * J e ≥ 0` for all edges and strict positivity on the specific edges `{x,y}`, `{z,t}`.
-/
theorem isingUrsell4_eq_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (hxy_pos : 0 < β * J (edge (V := V) (Λ := Λ) x y hxy))
    (hzt_pos : 0 < β * J (edge (V := V) (Λ := Λ) z t hzt)) :
    isingUrsell4 (V := V) (Λ := Λ) β J x y z t
      =
      -2 *
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
        isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} := by
  have hZxy :
      ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y)
      hxy hβJ hxy_pos
  have hZzt :
      ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) (x := z) (y := t)
      hzt hβJ hzt_pos
  exact
    isingUrsell4_eq (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y) (z := z) (t := t)
      hxy hxz hxt hyz hyt hzt hZxy hZzt

/--
Eq. (U4), with the nonvanishing hypotheses discharged under:

- nonnegative couplings `β * J e ≥ 0`, and
- reachability in the graph of *strictly positive* couplings between `x` and `y`, and between `z` and `t`.

This is the form that applies directly to nearest-neighbour ferromagnetic Ising models, where
`J e > 0` only on lattice-neighbour edges and is `0` otherwise.
-/
theorem isingUrsell4_eq_of_nonneg_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (hreach_xy : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y)
    (hreach_zt : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable z t) :
    isingUrsell4 (V := V) (Λ := Λ) β J x y z t
      =
      -2 *
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
        isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} := by
  have hZxy :
      ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      hβJ hxy hreach_xy
  have hZzt :
      ZReal (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      hβJ hzt hreach_zt
  exact
    isingUrsell4_eq (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y) (z := z) (t := t)
      hxy hxz hxt hyz hyt hzt hZxy hZzt

/-! ### Simple bounds from (U4) in the ferromagnetic regime -/

lemma isingCorr_nonneg_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (A : Finset (↥Λ)) :
    0 ≤ isingCorr (V := V) (Λ := Λ) β J A := by
  have hA :
      0 ≤ ZReal (V := V) (Λ := Λ) β J A :=
    ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ A
  have h0 :
      0 ≤ ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ (∅ : Finset (↥Λ))
  simpa [isingCorr_eq_ZReal_div] using (div_nonneg hA h0)

theorem isingUrsell4_le_zero_of_nonneg_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (hreach_xy : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y)
    (hreach_zt : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable z t) :
    isingUrsell4 (V := V) (Λ := Λ) β J x y z t ≤ 0 := by
  have hid :=
    isingUrsell4_eq_of_nonneg_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      (x := x) (y := y) (z := z) (t := t) hxy hxz hxt hyz hyt hzt hβJ hreach_xy hreach_zt
  have hcorrxy :
      0 ≤ isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) :=
    isingCorr_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ ({x, y} : Finset (↥Λ))
  have hcorrzt :
      0 ≤ isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) :=
    isingCorr_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ ({z, t} : Finset (↥Λ))
  have hP :
      0 ≤
        PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} :=
    PPairReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J)
      ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
      {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} hβJ
  have hprod :
      0 ≤
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
            PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} :=
    mul_nonneg (mul_nonneg hcorrxy hcorrzt) hP
  have hnonpos :
      -2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} ≤ 0 := by
    have :
        (-2 : ℝ) *
            (isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
              isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
                PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
                  {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z}) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) hprod
    simpa [mul_assoc] using this
  simpa [hid] using hnonpos

theorem abs_isingUrsell4_le_two_mul_isingCorr_mul_isingCorr_of_nonneg_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y z t : ↥Λ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (hreach_xy : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y)
    (hreach_zt : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable z t) :
    |isingUrsell4 (V := V) (Λ := Λ) β J x y z t|
      ≤
      2 *
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
        isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) := by
  have hid :=
    isingUrsell4_eq_of_nonneg_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      (x := x) (y := y) (z := z) (t := t) hxy hxz hxt hyz hyt hzt hβJ hreach_xy hreach_zt
  have hnonpos :
      isingUrsell4 (V := V) (Λ := Λ) β J x y z t ≤ 0 :=
    isingUrsell4_le_zero_of_nonneg_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      (x := x) (y := y) (z := z) (t := t) hxy hxz hxt hyz hyt hzt hβJ hreach_xy hreach_zt
  have hP_le_one :
      PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} ≤ 1 :=
    PPairReal_le_one_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J)
      ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
      {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} hβJ
  have hcorrxy :
      0 ≤ isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) :=
    isingCorr_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ ({x, y} : Finset (↥Λ))
  have hcorrzt :
      0 ≤ isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) :=
    isingCorr_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ ({z, t} : Finset (↥Λ))
  have habs :
      |isingUrsell4 (V := V) (Λ := Λ) β J x y z t|
        =
        2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} := by
    calc
      |isingUrsell4 (V := V) (Λ := Λ) β J x y z t|
          = -(isingUrsell4 (V := V) (Λ := Λ) β J x y z t) := by
              simpa using (abs_of_nonpos hnonpos)
      _ = -(-2 *
            isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
            PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z}) := by
            simp [hid]
      _ = 2 *
            isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
            PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z} := by
            ring
  have hcoef_nonneg :
      0 ≤
        2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hcorrxy) hcorrzt
  have hbound :
      (2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ))) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z}
        ≤
        (2 *
            isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ))) * 1 :=
    mul_le_mul_of_nonneg_left hP_le_one hcoef_nonneg
  have hbound' :
      2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) *
          PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ({z, t} : Finset (↥Λ))
            {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x z}
        ≤
        2 *
          isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({z, t} : Finset (↥Λ)) := by
    simpa [mul_assoc] using hbound
  simpa [habs] using hbound'

end RandomCurrent

end SpinGlass.Papers.Triviality4D
