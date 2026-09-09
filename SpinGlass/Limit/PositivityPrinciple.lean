/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.GhirlandaGuerraLimit
import SpinGlass.Limit.OverlapArrayBracket

/-!
# Talagrand's positivity principle (Vol. II, §12.3)

If a system satisfies the extended Ghirlanda–Guerra identities, the overlap `R_{1,2}` is essentially
nonnegative. The proof has a deterministic half and an identities half.

**The deterministic half** (Proposition 12.3.2): for *any* probability measure `G` on `Σ_N`, the
probability that `n − 1` independent replicas all have overlap `≤ −ε` with a given one is at most
`5 log n / (εn)`. The mechanism is Gram positivity, `∫∫ R_{1,2} dμ dμ = ‖∫σ dμ‖²/N ≥ 0`, for the
restriction of `G` to the set of configurations negatively correlated with most others
(Lemma 12.3.3).

This file proves the deterministic half for the finite-volume Gibbs measures, in the form consumed
by the array-law framework: `negSet ε n` is Talagrand's set `D_n` (replica `0` in place of `1`), and
the annealed overlap-array law of any random Hamiltonian gives it mass at most `5 log n / (εn)`.

## Main statements

- `SpinGlass.sum_sum_mul_mul_overlap_nonneg`: Gram positivity for weighted configurations.
- `SpinGlass.sum_filter_le_of_overlap` (Lemma 12.3.3) and `sum_mul_pow_le` (Proposition 12.3.2)
  for a probability vector on `Config N`.
- `SpinGlass.negSet`, `overlapArrayLaw_negSet_eq`, `bind_overlapArrayLaw_real_negSet_le`:
  Proposition 12.3.2 for the annealed overlap-array law of any random Hamiltonian.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators MeasureTheory.GibbsMeasure

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### Gram positivity for weighted configurations -/

/-- The Ising overlap as a normalised sum of spin products. -/
lemma overlap_eq_sum (σ τ : Config N) :
    overlap N σ τ = (1 / (N : ℝ)) * ∑ i : Fin N, spin N σ i * spin N τ i := by
  rw [overlap_eq_overlapOf, overlapOf]
  simp [spin_eq_spinOf]

/-- **Gram positivity**: `∑_{σ,τ} p σ p τ R(σ,τ) = (1/N) ∑ᵢ (∑_σ p σ σᵢ)² ≥ 0` for any weights. -/
theorem sum_sum_mul_mul_overlap_nonneg (p : Config N → ℝ) :
    0 ≤ ∑ σ : Config N, ∑ τ : Config N, p σ * p τ * overlap N σ τ := by
  set a : Config N → Fin N → ℝ := fun σ i => p σ * spin N σ i with ha
  have hL : ∑ σ : Config N, ∑ τ : Config N, p σ * p τ * overlap N σ τ
      = (1 / (N : ℝ)) * ∑ σ : Config N, ∑ τ : Config N, ∑ i : Fin N, a σ i * a τ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [overlap_eq_sum]
    simp only [ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ∀ i : Fin N, (∑ σ : Config N, a σ i) ^ 2
      = ∑ σ : Config N, ∑ τ : Config N, a σ i * a τ i := fun i => by
    rw [sq, Finset.sum_mul_sum]
  have hR : ∑ i : Fin N, (∑ σ : Config N, a σ i) ^ 2
      = ∑ σ : Config N, ∑ τ : Config N, ∑ i : Fin N, a σ i * a τ i := by
    rw [Finset.sum_congr rfl fun i _ => hsq i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  rw [hL, ← hR]
  positivity

/-! ### Lemma 12.3.3 and Proposition 12.3.2 for a probability vector -/

section ProbabilityVector

variable {p : Config N → ℝ} (hp : ∀ σ, 0 ≤ p σ) (hp1 : ∑ σ, p σ = 1) {ε : ℝ}

/-- The `p`-mass of the configurations with overlap `≤ -ε` with `σ`. -/
def negMass (p : Config N → ℝ) (ε : ℝ) (σ : Config N) : ℝ :=
  ∑ τ : Config N, p τ * (if overlap N σ τ ≤ -ε then 1 else 0)

include hp in
lemma negMass_nonneg (σ : Config N) : 0 ≤ negMass p ε σ :=
  Finset.sum_nonneg fun τ _ => mul_nonneg (hp τ) (by split_ifs <;> norm_num)

include hp hp1 in
lemma negMass_le_one (σ : Config N) : negMass p ε σ ≤ 1 := by
  calc negMass p ε σ ≤ ∑ τ : Config N, p τ :=
        Finset.sum_le_sum fun τ _ => by
          split_ifs <;> simp [hp τ]
    _ = 1 := hp1

/-- The complementary mass: configurations with overlap `> -ε` with `σ`. -/
lemma sum_mul_ite_gt (σ : Config N) :
    ∑ τ : Config N, p τ * (if -ε < overlap N σ τ then 1 else 0) = (∑ τ, p τ) - negMass p ε σ := by
  unfold negMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : overlap N σ τ ≤ -ε
  · simp [h, not_lt.2 h]
  · simp [h, lt_of_not_ge h]

include hp hp1 in
/-- **Talagrand, Vol. II, Lemma 12.3.3.** The configurations negatively correlated (`≤ -ε`) with
more than a `1 - c` fraction of the others carry mass at most `2c/ε`. -/
theorem sum_filter_le_of_overlap (hε : 0 < ε) (hε1 : ε ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∑ σ ∈ Finset.univ.filter (fun σ => 1 - c < negMass p ε σ), p σ ≤ 2 * c / ε := by
  classical
  set U := Finset.univ.filter (fun σ => 1 - c < negMass p ε σ) with hU
  set w := ∑ σ ∈ U, p σ with hw
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun σ _ => hp σ
  -- the restricted weights
  set q : Config N → ℝ := fun σ => if σ ∈ U then p σ else 0 with hq
  have hgram := sum_sum_mul_mul_overlap_nonneg (N := N) q
  -- rewrite the Gram sum over `U × U`
  have hgram' : 0 ≤ ∑ σ ∈ U, ∑ τ ∈ U, p σ * p τ * overlap N σ τ := by
    have : ∑ σ : Config N, ∑ τ : Config N, q σ * q τ * overlap N σ τ
        = ∑ σ ∈ U, ∑ τ ∈ U, p σ * p τ * overlap N σ τ := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ ∈ U)]
      have h1 : ∑ σ ∈ Finset.univ.filter (fun σ => ¬ σ ∈ U),
          ∑ τ : Config N, q σ * q τ * overlap N σ τ = 0 := by
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        refine Finset.sum_eq_zero fun τ _ => ?_
        simp [hq, hσ.2]
      rw [h1, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => τ ∈ U)]
      have h2 : ∑ τ ∈ Finset.univ.filter (fun τ => ¬ τ ∈ U), q σ * q τ * overlap N σ τ = 0 := by
        refine Finset.sum_eq_zero fun τ hτ => ?_
        rw [Finset.mem_filter] at hτ
        simp [hq, hτ.2]
      rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      simp [hq, hσ, hτ]
    rw [← this]
    exact hgram
  -- pointwise bound on the inner sums, for `σ ∈ U`
  have hinner : ∀ σ ∈ U, ∑ τ ∈ U, p τ * overlap N σ τ ≤ c * (1 + ε) - ε * w := by
    intro σ hσ
    have hσU : 1 - c < negMass p ε σ := (Finset.mem_filter.1 hσ).2
    have hgt : ∑ τ ∈ U, p τ * (if -ε < overlap N σ τ then 1 else 0) < c := by
      calc ∑ τ ∈ U, p τ * (if -ε < overlap N σ τ then 1 else 0)
          ≤ ∑ τ : Config N, p τ * (if -ε < overlap N σ τ then 1 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun τ _ _ => mul_nonneg (hp τ) (by split_ifs <;> norm_num))
        _ = 1 - negMass p ε σ := by rw [sum_mul_ite_gt, hp1]
        _ < c := by linarith
    have hle : ∑ τ ∈ U, p τ * (if overlap N σ τ ≤ -ε then 1 else 0)
        = w - ∑ τ ∈ U, p τ * (if -ε < overlap N σ τ then 1 else 0) := by
      rw [hw, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases h : overlap N σ τ ≤ -ε
      · simp [h, not_lt.2 h]
      · simp [h, lt_of_not_ge h]
    have hpt : ∀ τ, p τ * overlap N σ τ
        ≤ p τ * (if -ε < overlap N σ τ then 1 else 0)
          - ε * (p τ * (if overlap N σ τ ≤ -ε then 1 else 0)) := by
      intro τ
      have hR1 := abs_overlap_le_one N σ τ
      rw [abs_le] at hR1
      have hpτ := hp τ
      by_cases h : overlap N σ τ ≤ -ε
      · simp only [h, not_lt.2 h, ite_true, ite_false]
        nlinarith [mul_le_mul_of_nonneg_left h hpτ]
      · simp only [h, lt_of_not_ge h, ite_true, ite_false]
        nlinarith [mul_le_mul_of_nonneg_left hR1.2 hpτ]
    calc ∑ τ ∈ U, p τ * overlap N σ τ
        ≤ ∑ τ ∈ U, (p τ * (if -ε < overlap N σ τ then 1 else 0)
            - ε * (p τ * (if overlap N σ τ ≤ -ε then 1 else 0))) :=
          Finset.sum_le_sum fun τ _ => hpt τ
      _ = ∑ τ ∈ U, p τ * (if -ε < overlap N σ τ then 1 else 0)
            - ε * ∑ τ ∈ U, p τ * (if overlap N σ τ ≤ -ε then 1 else 0) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ c * (1 + ε) - ε * w := by
          rw [hle]
          nlinarith [hgt, hε]
  -- assemble: `0 ≤ ∑_{σ∈U} p σ (c(1+ε) - ε w) = w (c(1+ε) - ε w)`
  have hsum : ∑ σ ∈ U, ∑ τ ∈ U, p σ * p τ * overlap N σ τ ≤ w * (c * (1 + ε) - ε * w) := by
    calc ∑ σ ∈ U, ∑ τ ∈ U, p σ * p τ * overlap N σ τ
        = ∑ σ ∈ U, p σ * ∑ τ ∈ U, p τ * overlap N σ τ := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring
      _ ≤ ∑ σ ∈ U, p σ * (c * (1 + ε) - ε * w) :=
          Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_left (hinner σ hσ) (hp σ)
      _ = w * (c * (1 + ε) - ε * w) := by rw [← Finset.sum_mul]
  have hkey : 0 ≤ w * (c * (1 + ε) - ε * w) := hgram'.trans hsum
  -- conclude
  rcases hw0.lt_or_eq with hwpos | hwzero
  · have : ε * w ≤ c * (1 + ε) := by nlinarith [hkey, hwpos]
    rw [le_div_iff₀ hε]
    nlinarith [hc, hε1]
  · rw [← hwzero]
    positivity

include hp hp1 in
/-- **Talagrand, Vol. II, Proposition 12.3.2**, for a probability vector: the probability that `m`
independent replicas all have overlap `≤ -ε` with a given one is at most
`(4 log(m+1) + 1)/(ε(m+1))` (Talagrand writes `5 log(m+1)/(ε(m+1))`). -/
theorem sum_mul_negMass_pow_le (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) :
    ∑ σ : Config N, p σ * (negMass p ε σ) ^ m
      ≤ (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := by
  classical
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlogpos : (0 : ℝ) < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  set c : ℝ := Real.log ((m : ℝ) + 1) / m with hc
  have hcpos : 0 < c := div_pos hlogpos (by linarith)
  set U := Finset.univ.filter (fun σ => 1 - c < negMass p ε σ) with hU
  have hUmass := sum_filter_le_of_overlap hp hp1 hε hε1 hcpos
  rw [← hU] at hUmass
  -- split the sum
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => 1 - c < negMass p ε σ)]
  have hA : ∑ σ ∈ Finset.univ.filter (fun σ => 1 - c < negMass p ε σ), p σ * (negMass p ε σ) ^ m
      ≤ 2 * c / ε := by
    refine le_trans (Finset.sum_le_sum fun σ _ => ?_) hUmass
    calc p σ * (negMass p ε σ) ^ m ≤ p σ * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (negMass_nonneg hp σ) (negMass_le_one hp hp1 σ)) (hp σ)
      _ = p σ := mul_one _
  have hB : ∑ σ ∈ Finset.univ.filter (fun σ => ¬ 1 - c < negMass p ε σ),
      p σ * (negMass p ε σ) ^ m ≤ 1 / ((m : ℝ) + 1) := by
    have hcm : (m : ℝ) * c = Real.log ((m : ℝ) + 1) := by
      rw [hc, mul_div_assoc', mul_comm, mul_div_assoc, div_self (by linarith), mul_one]
    calc ∑ σ ∈ Finset.univ.filter (fun σ => ¬ 1 - c < negMass p ε σ), p σ * (negMass p ε σ) ^ m
        ≤ ∑ σ ∈ Finset.univ.filter (fun σ => ¬ 1 - c < negMass p ε σ),
            p σ * Real.exp (-c) ^ m := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          have hσ' : negMass p ε σ ≤ 1 - c := not_lt.1 (Finset.mem_filter.1 hσ).2
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (negMass_nonneg hp σ) ?_ m) (hp σ)
          exact hσ'.trans (Real.one_sub_le_exp_neg c)
      _ = Real.exp (-c) ^ m * ∑ σ ∈ Finset.univ.filter (fun σ => ¬ 1 - c < negMass p ε σ), p σ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
      _ ≤ Real.exp (-c) ^ m * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hp1]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => hp σ
      _ = 1 / ((m : ℝ) + 1) := by
          rw [mul_one, ← Real.exp_nat_mul, mul_neg, hcm, Real.exp_neg, Real.exp_log hm1, one_div]
  have h2c : 2 * c / ε ≤ 4 * Real.log ((m : ℝ) + 1) / (ε * ((m : ℝ) + 1)) := by
    have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) := by linarith
    have hmpos : (0 : ℝ) < m := by linarith
    have hc2 : 2 * c / ε = 2 * Real.log ((m : ℝ) + 1) / (ε * m) := by
      rw [hc]
      field_simp
    rw [hc2, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (m : ℝ) + 1 ≤ 2 * m := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * Real.log ((m : ℝ) + 1) * ε)]
  have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / (ε * ((m : ℝ) + 1)) := by
    rw [div_le_div_iff₀ hm1 (by positivity)]
    nlinarith [hε1, hε, hm1]
  calc _ ≤ 2 * c / ε + 1 / ((m : ℝ) + 1) := add_le_add hA hB
    _ ≤ 4 * Real.log ((m : ℝ) + 1) / (ε * ((m : ℝ) + 1)) + 1 / (ε * ((m : ℝ) + 1)) :=
        add_le_add h2c h1
    _ = (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := by ring

end ProbabilityVector

/-! ### Proposition 12.3.2 for the annealed overlap-array law -/

section ArrayLaw

/-- **Talagrand's set `D_n`** (Vol. II, §12.3), with replica `0` in place of `1`: all overlaps of
replica `0` with replicas `1, …, n-1` are at most `-ε`. -/
def negSet (ε : ℝ) (n : ℕ) : Set (ℕ → ℕ → OverlapValue) :=
  {R | ∀ l ∈ Finset.Ico 1 n, ((R 0 l : OverlapValue) : ℝ) ≤ -ε}

lemma negSet_eq_biInter (ε : ℝ) (n : ℕ) :
    negSet ε n
      = ⋂ l ∈ Finset.Ico 1 n, {R : ℕ → ℕ → OverlapValue | ((R 0 l : OverlapValue) : ℝ) ≤ -ε} := by
  ext R
  simp [negSet]

lemma isClosed_negSet (ε : ℝ) (n : ℕ) : IsClosed (negSet ε n) := by
  rw [negSet_eq_biInter]
  exact isClosed_biInter fun l _ => isClosed_le (continuous_entry 0 l) continuous_const

lemma measurableSet_negSet (ε : ℝ) (n : ℕ) : MeasurableSet (negSet ε n) :=
  (isClosed_negSet ε n).measurableSet

/-- The configurations of `m` replicas all negatively correlated with a distinguished one. -/
def negBlock (N : ℕ) (ε : ℝ) (m : ℕ) : Set (Fin (m + 1) → Config N) :=
  {x | ∀ l : Fin m, overlap N (x 0) (x l.succ) ≤ -ε}

/-- `D_n` is the pull-back of the block event along the first `n` replicas. -/
lemma preimage_pairArray_negSet (ε : ℝ) (m : ℕ) :
    pairArray (overlapUnit N) ⁻¹' negSet ε (m + 1)
      = (fun ω : ℕ → Config N => fun l : Fin (m + 1) => ω (l : ℕ)) ⁻¹' negBlock N ε m := by
  ext ω
  simp only [Set.mem_preimage, negSet, negBlock, Set.mem_ofPred_eq, pairArray, overlapUnit_coe,
    Finset.mem_Ico, Fin.val_zero, Fin.val_succ]
  constructor
  · intro h l
    exact h ((l : ℕ) + 1) ⟨by omega, by omega⟩
  · intro h l hl
    have := h ⟨l - 1, by omega⟩
    simp only at this
    rwa [Nat.sub_add_cancel hl.1] at this

/-- The block event has the product structure: its Gibbs probability is
`∑_σ p σ (negMass p ε σ)^m`. -/
lemma gibbs_average_n_det_indicator_negBlock (H : EnergySpace N) (ε : ℝ) (m : ℕ) :
    FiniteGibbs.gibbs_average_n_det (α := Config N) (n := m + 1) H
        ((negBlock N ε m).indicator (1 : (Fin (m + 1) → Config N) → ℝ))
      = ∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) H σ
          * (negMass (FiniteGibbs.gibbs_pmf (α := Config N) H) ε σ) ^ m := by
  classical
  set p := FiniteGibbs.gibbs_pmf (α := Config N) H with hp
  unfold FiniteGibbs.gibbs_average_n_det
  obtain ⟨e, hcons⟩ : ∃ e : Config N × (Fin m → Config N) ≃ (Fin (m + 1) → Config N),
      ∀ x : Config N × (Fin m → Config N), e x = Fin.cons x.1 x.2 :=
    ⟨Fin.consEquiv fun _ : Fin (m + 1) => Config N, fun _ => rfl⟩
  rw [← Equiv.sum_comp e (fun σs : Fin (m + 1) → Config N =>
      (negBlock N ε m).indicator (1 : (Fin (m + 1) → Config N) → ℝ) σs * ∏ l, p (σs l)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hind : ∀ σs' : Fin m → Config N,
      (negBlock N ε m).indicator (1 : (Fin (m + 1) → Config N) → ℝ) (Fin.cons σ σs')
        = ∏ l : Fin m, (if overlap N σ (σs' l) ≤ -ε then (1 : ℝ) else 0) := by
    intro σs'
    rw [Fintype.prod_boole, Set.indicator_apply]
    simp [negBlock]
  have hprod : ∀ σs' : Fin m → Config N,
      ∏ l : Fin (m + 1), p ((Fin.cons σ σs' : Fin (m + 1) → Config N) l)
        = p σ * ∏ l : Fin m, p (σs' l) := by
    intro σs'
    rw [Fin.prod_univ_succ]
    simp
  simp only [hcons, hind, hprod]
  -- ∑ σs', (∏ l, ite) * (p σ * ∏ l, p (σs' l)) = p σ * (negMass p ε σ)^m
  have hfac : ∀ σs' : Fin m → Config N,
      (∏ l : Fin m, (if overlap N σ (σs' l) ≤ -ε then (1 : ℝ) else 0)) * (p σ * ∏ l, p (σs' l))
        = p σ * ∏ l : Fin m, (p (σs' l) * (if overlap N σ (σs' l) ≤ -ε then (1 : ℝ) else 0)) := by
    intro σs'
    rw [Finset.prod_mul_distrib]
    ring
  simp only [hfac]
  rw [← Finset.mul_sum]
  congr 1
  have hsum : ∑ σs' : Fin m → Config N,
      ∏ l : Fin m, (p (σs' l) * (if overlap N σ (σs' l) ≤ -ε then (1 : ℝ) else 0))
        = ∏ l : Fin m, ∑ τ : Config N, p τ * (if overlap N σ τ ≤ -ε then (1 : ℝ) else 0) := by
    rw [Finset.prod_univ_sum]
    simp [Fintype.piFinset_univ]
  rw [hsum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- **The mass of `D_{m+1}` under the finite-volume overlap-array law** is
`∑_σ p σ (negMass p ε σ)^m`, the Gibbs weights being `p`. -/
theorem overlapArrayLaw_negSet_eq (H : EnergySpace N) (ε : ℝ) (m : ℕ) :
    overlapArrayLaw N H (negSet ε (m + 1))
      = ENNReal.ofReal (∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) H σ
          * (negMass (FiniteGibbs.gibbs_pmf (α := Config N) H) ε σ) ^ m) := by
  classical
  have hmeasBlock : MeasurableSet (negBlock N ε m) := MeasurableSet.of_discrete
  rw [overlapArrayLaw, Measure.map_apply (measurable_pairArray Measurable.of_discrete)
    (measurableSet_negSet ε (m + 1)), preimage_pairArray_negSet,
    ← Measure.map_apply (measurable_take_config N (m + 1) (fun l => (l : ℕ))) hmeasBlock,
    map_take_configReplicaArrayLaw N (m + 1) H Fin.val_injective,
    ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
    ← integral_indicator_one hmeasBlock,
    FiniteGibbs.integral_replicaGibbsMeasure_eq_gibbs_average_n_det,
    gibbs_average_n_det_indicator_negBlock]

/-- **Talagrand, Vol. II, Proposition 12.3.2, for the annealed overlap-array law of any random
Hamiltonian**: `ν(D_{m+1}) ≤ (4 log(m+1) + 1)/(ε(m+1))`. -/
theorem bind_overlapArrayLaw_real_negSet_le (ν : Measure (EnergySpace N)) [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) :
    (ν.bind (overlapArrayLaw N)).real (negSet ε (m + 1))
      ≤ (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := by
  have hB0 : 0 ≤ (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := by
    have : 0 ≤ Real.log ((m : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    positivity
  have hbound : ∀ H : EnergySpace N, overlapArrayLaw N H (negSet ε (m + 1))
      ≤ ENNReal.ofReal ((4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1))) := fun H => by
    rw [overlapArrayLaw_negSet_eq]
    exact ENNReal.ofReal_le_ofReal (sum_mul_negMass_pow_le
      (FiniteGibbs.gibbs_pmf_nonneg (α := Config N) H) (FiniteGibbs.sum_gibbs_pmf (α := Config N) H)
      hε hε1 hm)
  rw [measureReal_def, Measure.bind_apply (measurableSet_negSet _ _)
    (measurable_overlapArrayLaw N).aemeasurable]
  calc (∫⁻ H, overlapArrayLaw N H (negSet ε (m + 1)) ∂ν).toReal
      ≤ (∫⁻ _ : EnergySpace N,
          ENNReal.ofReal ((4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1))) ∂ν).toReal := by
        refine ENNReal.toReal_mono ?_ (lintegral_mono hbound)
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.ofReal_ne_top
    _ = (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hB0]

end ArrayLaw

end

end SpinGlass
