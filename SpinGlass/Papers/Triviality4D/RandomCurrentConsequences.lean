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

/-! ## Basic positivity/nonvanishing lemmas (ferromagnetic regime) -/

lemma weightReal_nonneg_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e, 0 ≤ β * J e) (n : Current (V := V) Λ) :
    0 ≤ weightReal (V := V) (Λ := Λ) β J n := by
  unfold weightReal
  simpa using
    (Finset.prod_nonneg (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial)
      (by
        intro e _he
        have hpow : 0 ≤ (β * J e) ^ (n e) := pow_nonneg (hβJ e) _
        have hfac : 0 ≤ ((n e).factorial : ℝ) := by
          exact_mod_cast (Nat.zero_le (n e).factorial)
        exact div_nonneg hpow hfac))

/-- Weight of a unit current is the corresponding coupling `β * J e₀`. -/
lemma weightReal_unitCurrent (β : ℝ) (J : Edge (V := V) Λ → ℝ) (e₀ : Edge (V := V) Λ) :
    weightReal (V := V) (Λ := Λ) β J (unitCurrent (V := V) (Λ := Λ) e₀) = β * J e₀ := by
  unfold weightReal unitCurrent
  let g : Edge (V := V) Λ → ℝ :=
    fun e : Edge (V := V) Λ =>
      (β * J e) ^ (if e = e₀ then 1 else 0) / ((if e = e₀ then 1 else 0).factorial)
  change (Finset.prod (Finset.univ : Finset (Edge (V := V) Λ)) g) = β * J e₀
  have he₀ : e₀ ∈ (Finset.univ : Finset (Edge (V := V) Λ)) := by simp
  have hsingle :
      Finset.prod (Finset.univ : Finset (Edge (V := V) Λ)) g = g e₀ := by
    refine Finset.prod_eq_single_of_mem e₀ he₀ ?_
    intro e he hne
    simp [hne]
  calc
    Finset.prod (Finset.univ : Finset (Edge (V := V) Λ)) g = g e₀ := hsingle
    _ = β * J e₀ := by simp [g]

/--
If couplings are nonnegative (`β * J e ≥ 0`) and there exists a current with sources `B` of
strictly positive weight, then the source-constrained sum `ZReal B` is strictly positive.

This is the basic “non-vacuity” lemma used to discharge `ZReal … ≠ 0` hypotheses.
-/
lemma ZReal_pos_of_exists_current
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (B : Finset (↥Λ)) (n₀ : Current (V := V) Λ)
    (hsources : sources (V := V) (Λ := Λ) n₀ = B)
    (hwpos : 0 < weightReal (V := V) (Λ := Λ) β J n₀) :
    0 < ZReal (V := V) (Λ := Λ) β J B := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let f : Current (V := V) Λ → ℝ := fun n => if sources (V := V) n = B then w n else 0
  have hs_norm : Summable (fun n : Current (V := V) Λ => ‖f n‖) := by
    refine Summable.of_norm_bounded (g := fun n : Current (V := V) Λ => ‖w n‖)
      (summable_norm_weightReal (V := V) (Λ := Λ) (β := β) J) ?_
    intro n
    by_cases hn : sources (V := V) n = B <;> simp [f, hn, w]
  have hs : Summable f := hs_norm.of_norm
  have hnonneg : ∀ n : Current (V := V) Λ, 0 ≤ f n := by
    intro n
    by_cases hn : sources (V := V) n = B
    · simp [f, hn, w, weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ n]
    · simp [f, hn]
  have hfpos : 0 < f n₀ := by
    simpa [f, w, hsources] using hwpos
  simpa [ZReal, f, w] using (Summable.tsum_pos hs hnonneg n₀ hfpos)

lemma ZReal_pair_pos_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ} (hxy : x ≠ y)
    (hβJ : ∀ e, 0 ≤ β * J e) (hpos : 0 < β * J (edge (V := V) (Λ := Λ) x y hxy)) :
    0 < ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  let B : Finset (↥Λ) := ({x, y} : Finset (↥Λ))
  let e₀ : Edge (V := V) Λ := edge (V := V) (Λ := Λ) x y hxy
  let n₀ : Current (V := V) Λ := unitCurrent (V := V) (Λ := Λ) e₀
  have hsources : sources (V := V) (Λ := Λ) n₀ = B := by
    simpa [B, e₀, n₀] using
      (sources_unitCurrent_edge (V := V) (Λ := Λ) (x := x) (y := y) hxy)
  have hwpos : 0 < weightReal (V := V) (Λ := Λ) β J n₀ := by
    have hw :
        weightReal (V := V) (Λ := Λ) β J n₀ = β * J e₀ := by
      simpa [n₀] using (weightReal_unitCurrent (V := V) (Λ := Λ) (β := β) (J := J) e₀)
    simpa [hw] using hpos
  exact
    ZReal_pos_of_exists_current (V := V) (Λ := Λ) (β := β) (J := J) hβJ B n₀ hsources hwpos

lemma ZReal_pair_ne_zero_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ} (hxy : x ≠ y)
    (hβJ : ∀ e, 0 ≤ β * J e) (hpos : 0 < β * J (edge (V := V) (Λ := Λ) x y hxy)) :
    ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
  ne_of_gt (ZReal_pair_pos_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y)
    hxy hβJ hpos)

/-! ## Nonvanishing of `ZReal {x,y}` from a positive-coupling walk -/

/-- Adjacency relation keeping only edges with strictly positive coupling `β * J`. -/
def posCouplingAdj (β : ℝ) (J : Edge (V := V) Λ → ℝ) (x y : ↥Λ) : Prop :=
  ∃ hxy : x ≠ y, 0 < β * J (edge (V := V) (Λ := Λ) x y hxy)

/-- The simple graph on `Λ` keeping only edges with strictly positive coupling `β * J`. -/
def posCouplingGraph (β : ℝ) (J : Edge (V := V) Λ → ℝ) : SimpleGraph (↥Λ) where
  Adj x y := posCouplingAdj (V := V) (Λ := Λ) β J x y
  symm := by
    intro x y h
    rcases h with ⟨hxy, hpos⟩
    refine ⟨hxy.symm, ?_⟩
    have he :
        edge (V := V) (Λ := Λ) y x hxy.symm = edge (V := V) (Λ := Λ) x y hxy := by
      apply Subtype.ext
      simp [edge]
    simpa [he] using hpos
  loopless := by
    intro x h
    rcases h with ⟨hxx, _⟩
    exact hxx rfl

/--
The current obtained by summing unit-currents along the edges of a walk in the positive-coupling
graph.
-/
noncomputable def currentOfPosCouplingWalk
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ}
    (w : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) : Current (V := V) Λ :=
  match w with
  | .nil => 0
  | .cons hab p =>
      unitCurrent (V := V) (Λ := Λ) (edge (V := V) (Λ := Λ) _ _ hab.choose) +
        currentOfPosCouplingWalk (β := β) (J := J) p

lemma sources_currentOfPosCouplingWalk
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ}
    (w : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) :
    sources (V := V) (Λ := Λ) (currentOfPosCouplingWalk (β := β) (J := J) w)
      = (if x = y then (∅ : Finset (↥Λ)) else ({x, y} : Finset (↥Λ))) := by
  induction w with
  | nil =>
      ext z
      simp [currentOfPosCouplingWalk, sources, IsSource, degree]
  | cons hab p ih =>
      rename_i u v z
      have huv : u ≠ v := hab.choose
      simp [currentOfPosCouplingWalk, sources_add,
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

lemma betaJ_pos_of_currentOfPosCouplingWalk_ne_zero
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ}
    (w : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) {e : Edge (V := V) Λ}
    (hne : currentOfPosCouplingWalk (β := β) (J := J) w e ≠ 0) :
    0 < β * J e := by
  induction w with
  | nil =>
      simp [currentOfPosCouplingWalk] at hne
  | cons hab p ih =>
      rename_i u v z
      let e₀ : Edge (V := V) Λ := edge (V := V) (Λ := Λ) u v hab.choose
      by_cases he : e = e₀
      · subst he
        simpa [e₀] using hab.choose_spec
      · have hne' :
            currentOfPosCouplingWalk (β := β) (J := J) p e ≠ 0 := by
          simpa [currentOfPosCouplingWalk, unitCurrent, e₀, he] using hne
        exact ih hne'

lemma weightReal_pos_currentOfPosCouplingWalk
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ}
    (w : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) :
    0 <
      weightReal (V := V) (Λ := Λ) β J
        (currentOfPosCouplingWalk (β := β) (J := J) w) := by
  unfold weightReal
  simpa using
    (Finset.prod_pos (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e : Edge (V := V) Λ =>
        (β * J e) ^
              (currentOfPosCouplingWalk (β := β) (J := J) w e) /
            (currentOfPosCouplingWalk (β := β) (J := J) w e).factorial)
      (by
        intro e _he
        by_cases hzero :
            currentOfPosCouplingWalk (β := β) (J := J) w e = 0
        · simp [hzero]
        · have hb : 0 < β * J e :=
            betaJ_pos_of_currentOfPosCouplingWalk_ne_zero (β := β) (J := J) w (e := e) hzero
          have hpow :
              0 <
                (β * J e) ^
                  (currentOfPosCouplingWalk (β := β) (J := J) w e) :=
            pow_pos hb _
          have hfac :
              0 <
                ((currentOfPosCouplingWalk (β := β) (J := J) w e).factorial : ℝ) := by
            exact_mod_cast
              (Nat.factorial_pos
                (currentOfPosCouplingWalk (β := β) (J := J) w e))
          exact div_pos hpow hfac))

lemma ZReal_pair_pos_of_posCouplingWalk
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    {x y : ↥Λ} (hxy : x ≠ y)
    (wxy : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) :
    0 < ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  let B : Finset (↥Λ) := ({x, y} : Finset (↥Λ))
  let n₀ : Current (V := V) Λ :=
    currentOfPosCouplingWalk (β := β) (J := J) wxy
  have hsources : sources (V := V) (Λ := Λ) n₀ = B := by
    simpa [B, n₀, hxy] using
      (sources_currentOfPosCouplingWalk (V := V) (Λ := Λ) (β := β) (J := J) wxy)
  have hwpos : 0 < weightReal (V := V) (Λ := Λ) β J n₀ := by
    simpa [n₀] using
      (weightReal_pos_currentOfPosCouplingWalk (V := V) (Λ := Λ) (β := β) (J := J) wxy)
  exact
    ZReal_pos_of_exists_current (V := V) (Λ := Λ) (β := β) (J := J) hβJ B n₀ hsources hwpos

lemma ZReal_pair_ne_zero_of_posCouplingWalk
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    {x y : ↥Λ} (hxy : x ≠ y)
    (wxy : (posCouplingGraph (V := V) (Λ := Λ) β J).Walk x y) :
    ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
  ne_of_gt (ZReal_pair_pos_of_posCouplingWalk (V := V) (Λ := Λ) (β := β) (J := J) hβJ hxy wxy)

lemma ZReal_pair_pos_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    {x y : ↥Λ} (hxy : x ≠ y) (hreach : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y) :
    0 < ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  rcases (SimpleGraph.Reachable.exists_isPath (G := posCouplingGraph (V := V) (Λ := Λ) β J) hreach) with
    ⟨w, _hw⟩
  exact ZReal_pair_pos_of_posCouplingWalk (V := V) (Λ := Λ) (β := β) (J := J) hβJ hxy w

lemma ZReal_pair_ne_zero_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    {x y : ↥Λ} (hxy : x ≠ y) (hreach : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y) :
    ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
  ne_of_gt (ZReal_pair_pos_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J) hβJ hxy hreach)

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

lemma PPairReal_comm
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ)) :
    PPairReal (V := V) (Λ := Λ) β J A B S = PPairReal (V := V) (Λ := Λ) β J B A S := by
  classical
  unfold PPairReal
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let f : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p =>
    if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
      S.indicator (fun _n => w p.1 * w p.2) (p.1 + p.2)
    else 0
  let g : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p =>
    if sources (V := V) p.1 = B ∧ sources (V := V) p.2 = A then
      S.indicator (fun _n => w p.1 * w p.2) (p.1 + p.2)
    else 0
  have hnum : (∑' p : Current (V := V) Λ × Current (V := V) Λ, f p) =
      ∑' p : Current (V := V) Λ × Current (V := V) Λ, g p := by
    let e :
        (Current (V := V) Λ × Current (V := V) Λ) ≃
          (Current (V := V) Λ × Current (V := V) Λ) :=
      Equiv.prodComm (Current (V := V) Λ) (Current (V := V) Λ)
    calc
      (∑' p : Current (V := V) Λ × Current (V := V) Λ, f p) =
          ∑' p : Current (V := V) Λ × Current (V := V) Λ, f (e p) := by
            simpa [e] using (e.tsum_eq (f := f)).symm
      _ = ∑' p : Current (V := V) Λ × Current (V := V) Λ, g p := by
          refine tsum_congr ?_
          intro p
          by_cases hcond : sources (V := V) p.1 = B ∧ sources (V := V) p.2 = A
          · -- swap the pair `(p.1,p.2)` and commute products
            simp [f, g, e, hcond, w, add_comm, mul_comm]
          · have hcond' : ¬ (sources (V := V) p.2 = A ∧ sources (V := V) p.1 = B) := by
              intro hcond'
              exact hcond ⟨hcond'.2, hcond'.1⟩
            simp [f, g, e, hcond, hcond', w]
  -- identical denominators after commuting `*`
  rw [hnum]
  simp [g, w, mul_comm]

/-! ### Basic normalization of `PPairReal` -/

@[simp]
lemma PPairReal_empty
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    PPairReal (V := V) (Λ := Λ) β J A B (∅ : Set (Current (V := V) Λ)) = 0 := by
  simp [PPairReal]

lemma PPairReal_univ_eq_one
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    (hZ : ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B ≠ 0) :
    PPairReal (V := V) (Λ := Λ) β J A B (Set.univ : Set (Current (V := V) Λ)) = 1 := by

  have hnum :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
            weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2
          else 0)
        =
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B := by
    simpa using
      (ZReal_mul_ZReal_eq_tsum_pair (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)).symm
  simp [PPairReal, Set.indicator, hnum, hZ]

/-! ### Positivity bounds for `PPairReal` under nonnegative couplings -/

lemma ZReal_nonneg_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (A : Finset (↥Λ)) :
    0 ≤ ZReal (V := V) (Λ := Λ) β J A := by
  unfold ZReal
  refine tsum_nonneg ?_
  intro n
  by_cases hn : sources (V := V) n = A
  · simp [hn, weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ n]
  · simp [hn]

lemma PPairReal_nonneg_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ))
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    0 ≤ PPairReal (V := V) (Λ := Λ) β J A B S := by
  unfold PPairReal
  have hnum :
      0 ≤
        ∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
            S.indicator
              (fun _n =>
                weightReal (V := V) (Λ := Λ) β J p.1 *
                  weightReal (V := V) (Λ := Λ) β J p.2)
              (p.1 + p.2)
          else 0 := by
    refine tsum_nonneg ?_
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · have hw1 :
          0 ≤ weightReal (V := V) (Λ := Λ) β J p.1 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.1
      have hw2 :
          0 ≤ weightReal (V := V) (Λ := Λ) β J p.2 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.2
      have hwprod :
          0 ≤
            weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2 :=
        mul_nonneg hw1 hw2
      by_cases hmem : (p.1 + p.2) ∈ S
      · simp [hcond, Set.indicator_of_mem, hmem, hwprod]
      · simp [hcond, Set.indicator, hmem]
    · simp [hcond]
  have hden :
      0 ≤
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B :=
    mul_nonneg
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ A)
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ B)
  exact div_nonneg hnum hden

lemma PPairReal_le_one_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ))
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    PPairReal (V := V) (Λ := Λ) β J A B S ≤ 1 := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let wprod : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p => w p.1 * w p.2
  let fAll : (Current (V := V) Λ × Current (V := V) Λ) → ℝ :=
    fun p =>
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then wprod p else 0
  let fS : (Current (V := V) Λ × Current (V := V) Λ) → ℝ :=
    fun p =>
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
        S.indicator (fun _n => wprod p) (p.1 + p.2)
      else 0
  have hsWeight :
      Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖w p.1‖ * ‖w p.2‖ :=
    summable_norm_weightReal_mul_norm_weightReal (V := V) (Λ := Λ) (β := β) J
  have hsAll_norm : Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖fAll p‖ := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · simp [fAll, wprod, w, hcond, norm_mul]
    · simpa [fAll, hcond] using
        (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
  have hsAll : Summable fAll := hsAll_norm.of_norm
  have hsS_norm : Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖fS p‖ := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · by_cases hmem : (p.1 + p.2) ∈ S
      · simp [fS, hcond, Set.indicator_of_mem, hmem, wprod, w, norm_mul]
      ·
        simpa [fS, hcond, Set.indicator, hmem] using
          (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
    ·
      simpa [fS, hcond] using
        (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
  have hsS : Summable fS := hsS_norm.of_norm
  have hpoint : ∀ p, fS p ≤ fAll p := by
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · have hw1 : 0 ≤ w p.1 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.1
      have hw2 : 0 ≤ w p.2 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.2
      have hwprod : 0 ≤ wprod p := mul_nonneg hw1 hw2
      by_cases hmem : (p.1 + p.2) ∈ S
      · simp [fS, fAll, hcond, Set.indicator_of_mem, hmem]
      · simp [fS, fAll, hcond, Set.indicator, hmem, hwprod]
    · simp [fS, fAll, hcond]
  have htsum :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ, fS p) ≤
        (∑' p : Current (V := V) Λ × Current (V := V) Λ, fAll p) :=
    hsS.tsum_le_tsum hpoint hsAll
  have hZ :
      ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B =
        ∑' p : Current (V := V) Λ × Current (V := V) Λ, fAll p := by
    simpa [fAll, wprod, w] using
      (ZReal_mul_ZReal_eq_tsum_pair (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B))
  have hden_nonneg :
      0 ≤
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B :=
    mul_nonneg
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ A)
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ B)
  have hnum_le :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ, fS p) ≤
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B := by
    simpa [hZ] using htsum
  have :
      (∑' p : Current (V := V) Λ × Current (V := V) Λ, fS p) /
          (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) ≤
        (1 : ℝ) := by
    exact div_le_one_of_le₀ hnum_le hden_nonneg
  simpa [PPairReal, fS, wprod, w] using this

lemma PPairReal_mono_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    {S T : Set (Current (V := V) Λ)} (hST : S ⊆ T)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    PPairReal (V := V) (Λ := Λ) β J A B S ≤ PPairReal (V := V) (Λ := Λ) β J A B T := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let wprod : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p => w p.1 * w p.2
  let fS : (Current (V := V) Λ × Current (V := V) Λ) → ℝ :=
    fun p =>
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
        S.indicator (fun _n => wprod p) (p.1 + p.2)
      else 0
  let fT : (Current (V := V) Λ × Current (V := V) Λ) → ℝ :=
    fun p =>
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
        T.indicator (fun _n => wprod p) (p.1 + p.2)
      else 0
  have hsWeight :
      Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖w p.1‖ * ‖w p.2‖ :=
    summable_norm_weightReal_mul_norm_weightReal (V := V) (Λ := Λ) (β := β) J
  have hsS_norm : Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖fS p‖ := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · by_cases hmem : (p.1 + p.2) ∈ S
      · simp [fS, hcond, Set.indicator_of_mem, hmem, wprod, w, norm_mul]
      · simpa [fS, hcond, Set.indicator, hmem] using
          (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
    · simpa [fS, hcond] using
        (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
  have hsS : Summable fS := hsS_norm.of_norm
  have hsT_norm : Summable fun p : Current (V := V) Λ × Current (V := V) Λ => ‖fT p‖ := by
    refine Summable.of_norm_bounded (g := fun p => ‖w p.1‖ * ‖w p.2‖) hsWeight ?_
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · by_cases hmem : (p.1 + p.2) ∈ T
      · simp [fT, hcond, Set.indicator_of_mem, hmem, wprod, w, norm_mul]
      · simpa [fT, hcond, Set.indicator, hmem] using
          (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
    · simpa [fT, hcond] using
        (mul_nonneg (norm_nonneg (w p.1)) (norm_nonneg (w p.2)))
  have hsT : Summable fT := hsT_norm.of_norm
  have hpoint : ∀ p, fS p ≤ fT p := by
    intro p
    by_cases hcond : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
    · have hw1 : 0 ≤ w p.1 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.1
      have hw2 : 0 ≤ w p.2 :=
        weightReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ p.2
      have hwprod : 0 ≤ wprod p := mul_nonneg hw1 hw2
      by_cases hmemS : (p.1 + p.2) ∈ S
      · have hmemT : (p.1 + p.2) ∈ T := hST hmemS
        simp [fS, fT, hcond, Set.indicator_of_mem, hmemS, hmemT]
      · by_cases hmemT : (p.1 + p.2) ∈ T
        · simp [fS, fT, hcond, Set.indicator, hmemS, hmemT, hwprod]
        · simp [fS, fT, hcond, Set.indicator, hmemS, hmemT]
    · simp [fS, fT, hcond]
  have htsum : (∑' p, fS p) ≤ ∑' p, fT p :=
    hsS.tsum_le_tsum hpoint hsT
  have hden_nonneg :
      0 ≤
        ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B :=
    mul_nonneg
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ A)
      (ZReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) hβJ B)
  have hdiv :
      (∑' p, fS p) /
          (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B)
        ≤
        (∑' p, fT p) /
          (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) :=
    div_le_div_of_nonneg_right htsum hden_nonneg
  simpa [PPairReal, fS, fT, wprod, w] using hdiv

lemma PPairReal_mem_Icc_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) (S : Set (Current (V := V) Λ))
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    PPairReal (V := V) (Λ := Λ) β J A B S ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨PPairReal_nonneg_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B) (S := S) hβJ,
    PPairReal_le_one_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B) (S := S) hβJ⟩

/--
Switching lemma as a normalized weight ratio: the total-current event `ℱ_B` (existence of a
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
  have hPP :
      PPairReal (V := V) (Λ := Λ) β J (symmDiff A B) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}
        =
        (ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B) /
          (ZReal (V := V) (Λ := Λ) β J (symmDiff A B) *
            ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))) :=
    (PPairReal_hasSubCurrent_eq_ZReal_ratio (V := V) (Λ := Λ) (β := β) (J := J) A B)
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
          set ZA : ℝ := ZReal (V := V) (Λ := Λ) β J A
          set ZB : ℝ := ZReal (V := V) (Λ := Λ) β J B
          set Z0 : ℝ := ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ))
          set ZAB : ℝ := ZReal (V := V) (Λ := Λ) β J (symmDiff A B)
          have hnum : (ZA / Z0) * (ZB / Z0) = (ZA * ZB) / (Z0 * Z0) := by
            simpa using (mul_div_mul_comm ZA ZB Z0 Z0).symm
          have hden : (Z0 * Z0) / Z0 = Z0 := by
            simpa [div_eq_mul_inv, mul_assoc] using (mul_self_mul_inv (a := Z0))
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

/-! ## (prop2b) Connectivity probability as a correlation ratio -/

/--
Paper Appendix Proposition `prop:3`, Eq. `(prop2b)` in finite volume:
for distinct `x,y,u`, the connectivity of `x` to `u` in the total current under sources `{x,y}` and `∅`
is given by a ratio of two-point correlations:
\[
{\bf P}^{xy,\emptyset}_{\Lambda,\beta}[u \leftrightarrow x]
= \frac{\langle\sigma_x\sigma_u\rangle_{\Lambda,\beta}\,\langle\sigma_u\sigma_y\rangle_{\Lambda,\beta}}
        {\langle\sigma_x\sigma_y\rangle_{\Lambda,\beta}}.
\]

Here the RHS is expressed using `isingCorr` and the LHS using `PPairReal` applied to the event
`Connected`.
-/
theorem PPairReal_connected_eq_isingCorr_mul_isingCorr_div
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y u : ↥Λ}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u) :
    PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x u}
      =
      (isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  have hsymm : symmDiff ({y, u} : Finset (↥Λ)) ({x, u} : Finset (↥Λ)) = ({x, y} : Finset (↥Λ)) := by
    ext v
    by_cases hvx : v = x
    · subst hvx
      constructor
      · intro _hx
        simp
      · intro _hx
        refine (Finset.mem_symmDiff).2 (Or.inr ?_)
        refine ⟨by simp, ?_⟩
        simp [hxy, hxu]
    by_cases hvy : v = y
    · subst hvy
      constructor
      · intro _hy
        simp
      · intro _hy
        refine (Finset.mem_symmDiff).2 (Or.inl ?_)
        refine ⟨by simp, ?_⟩
        simp [hvx, hyu]
    by_cases hvu : v = u
    · subst v
      have hux : u ≠ x := by simpa [eq_comm] using hxu
      have huy : u ≠ y := by simpa [eq_comm] using hyu
      simp [Finset.mem_symmDiff, hux, huy]
    · simp [Finset.mem_symmDiff, hvx, hvy, hvu]
  have hSet :
      {n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({x, u} : Finset (↥Λ))} =
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x u} := by
    ext n
    simpa using
      (hasSubCurrent_pair_iff_connected (V := V) (Λ := Λ) (n := n) (x := x) (y := u) (hxy := hxu))
  have horgaf :=
    (isingCorr_mul_isingCorr_div_isingCorr_symmDiff_eq_PPairReal_hasSubCurrent (V := V) (Λ := Λ)
      (β := β) (J := J) ({y, u} : Finset (↥Λ)) ({x, u} : Finset (↥Λ)))
  simpa [hsymm, hSet, mul_comm, mul_left_comm, mul_assoc] using horgaf.symm

/--
In the ferromagnetic regime, the paper’s ratio
\[
\frac{\langle\sigma_x\sigma_u\rangle\langle\sigma_y\sigma_u\rangle}{\langle\sigma_x\sigma_y\rangle}
\]
lies in `[0,1]` since it equals a connectivity probability (Proposition `prop:3`, Eq. `(prop2b)`).
-/
theorem isingCorr_mul_isingCorr_div_isingCorr_pair_mem_Icc_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y u : ↥Λ}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    ((isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({y, u} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) ∈ Set.Icc (0 : ℝ) 1 := by
  have hP :
      PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x u} ∈ Set.Icc (0 : ℝ) 1 :=
    PPairReal_mem_Icc_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J)
      ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
      {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x u} hβJ
  simpa [PPairReal_connected_eq_isingCorr_mul_isingCorr_div (V := V) (Λ := Λ) (β := β) (J := J)
    (x := x) (y := y) (u := u) hxy hxu hyu] using hP

/-! ## Two-point connectivity under sourceless pair law -/

/--
For distinct vertices `x ≠ y`, the event `Connected n x y` for the **total** current under two
independent sourceless currents has normalized weight ratio equal to the square of the two-point
correlation.

The “random current connectivity” identity
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
  have hSet :
      ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n ({x, y} : Finset (↥Λ))}) =
        {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y} := by
    ext n
    simpa using
      (hasSubCurrent_pair_iff_connected (V := V) (Λ := Λ) n (hxy := hxy))
  have hCorr :
      isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) =
        ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) /
          ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) :=
    isingCorr_eq_ZReal_div (V := V) (Λ := Λ) (β := β) (J := J) ({x, y} : Finset (↥Λ))
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
          simp [hCorr, pow_two]

theorem abs_isingCorr_pair_le_one_of_nonneg
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y : ↥Λ} (hxy : x ≠ y)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e) :
    |isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))| ≤ 1 := by
  have hP :
      PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
          {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y}
        ≤ 1 :=
    PPairReal_le_one_of_nonneg (V := V) (Λ := Λ) (β := β) (J := J)
      (A := (∅ : Finset (↥Λ))) (B := (∅ : Finset (↥Λ)))
      {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n x y} hβJ
  have hsq :
      (isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))) ^ 2 ≤ 1 := by
    simpa [PPairReal_connected_eq_isingCorr_sq (V := V) (Λ := Λ) (β := β) (J := J) (x := x) (y := y) hxy] using
      hP
  exact (sq_le_one_iff_abs_le_one _).1 hsq

end RandomCurrent

end SpinGlass.Papers.Triviality4D
