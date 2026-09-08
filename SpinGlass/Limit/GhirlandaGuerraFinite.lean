/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.OverlapArrayBracket
import SpinGlass.FiniteGibbs.GGDefect

/-!
# The finite-volume Ghirlanda–Guerra identity, in the language of the overlap array

`SpinGlass.FiniteGibbs.ghirlandaGuerraCombination` is the Ghirlanda–Guerra combination of the
*finite replica calculus*: brackets of functions of finitely many configurations, with the
covariance kernel of the Hamiltonian inserted. `SpinGlass.SatisfiesGhirlandaGuerra` is Talagrand's
Definition 15.3.4: an identity between integrals of continuous test functions against the *law of
the overlap array*. This file proves that the two are the same number, up to the scale of the
kernel:

`ggCombination ν n (g ∘ overlaps) 0`
`  = κ · (n ∫ φ(R_{0,n}) g − (∫ φ(R_{0,n}))(∫ g) − ∑_{l=1}^{n-1} ∫ φ(R_{0,l}) g)`

for any Hamiltonian law `ν` whose covariance kernel is `κ φ(R_{στ})` — that is, for every mixed
`p`-spin model, `κ = N` and `φ = ξ`.

Consequently every quantitative bound on the Ghirlanda–Guerra combination (Vol. II, §12.2, via
Theorem 12.1.1) is a quantitative bound on the *defect in Talagrand's identity (15.40)* for the
test function `φ = ξ`, and the identity holds exactly in the limit as soon as the combination is
`o(κ)`.

## Main statements

- `SpinGlass.blockEntryCM`, `SpinGlass.blockReindex`, `SpinGlass.overlapReplicaFun`: the plumbing.
- `SpinGlass.ghirlandaGuerraCombination_eq_overlapArrayLaw`: **the translation**.
- `SpinGlass.abs_ghirlandaGuerra_defect_overlapArrayLaw_le`: the resulting bound on the defect in
  (15.40).
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure
open scoped ProbabilityTheory

namespace SpinGlass

noncomputable section

/-! ### Continuous plumbing for finite overlap blocks -/

/-- Selecting one entry of a finite overlap block, as a continuous map. -/
def blockEntryCM {k : ℕ} (a b : Fin k) : C(Fin k → Fin k → OverlapValue, OverlapValue) :=
  ⟨fun x => x a b, (continuous_apply b).comp (continuous_apply a)⟩

@[simp] lemma blockEntryCM_apply {k : ℕ} (a b : Fin k) (x : Fin k → Fin k → OverlapValue) :
    blockEntryCM a b x = x a b := rfl

/-- Reindexing a finite overlap block along a map of replica labels, as a continuous map. -/
def blockReindex {k m : ℕ} (u : Fin m → Fin k) :
    C(Fin k → Fin k → OverlapValue, Fin m → Fin m → OverlapValue) :=
  ⟨fun x l l' => x (u l) (u l'), continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)⟩

@[simp] lemma blockReindex_apply {k m : ℕ} (u : Fin m → Fin k)
    (x : Fin k → Fin k → OverlapValue) (l l' : Fin m) :
    blockReindex u x l l' = x (u l) (u l') := rfl

/-- **The replica test function attached to a test function of the overlap block.** Pulling a
continuous function of the `n × n` overlap matrix back along the overlap map turns it into an
admissible test function of `n` configurations — the objects the finite replica calculus and the
Ghirlanda–Guerra combination act on. -/
def overlapReplicaFun (N : ℕ) {n : ℕ} (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    FiniteGibbs.ReplicaFun (α := Config N) n :=
  fun σs => g fun l l' => overlapUnit N (σs l) (σs l')

@[simp] lemma overlapReplicaFun_apply (N : ℕ) {n : ℕ}
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) (σs : FiniteGibbs.ReplicaSpace (α := Config N) n) :
    overlapReplicaFun N g σs = g fun l l' => overlapUnit N (σs l) (σs l') := rfl

/-- A test function of the overlap block is bounded by the sup-norm of the block function. -/
lemma abs_overlapReplicaFun_le (N : ℕ) {n : ℕ} (g : C(Fin n → Fin n → OverlapValue, ℝ))
    (σs : FiniteGibbs.ReplicaSpace (α := Config N) n) :
    |overlapReplicaFun N g σs| ≤ ‖g‖ :=
  g.norm_coe_le_norm _

/-! ### The translation -/

section Translation

variable {N n : ℕ}

/-- **The Ghirlanda–Guerra combination of the finite replica calculus is the defect in Talagrand's
identity (15.40), scaled by the size of the covariance kernel.**

Let `ν` be a Hamiltonian law whose covariance kernel is `κ φ(R_{στ})` — for a mixed `p`-spin model
`κ = N` and `φ = ξ`. Then for every continuous test function `g` of the `n × n` overlap block and
every replica label `i`,

`ggCombination ν n (g ∘ overlaps) i`
`  = κ · (n ∫ φ(R_{i,n}) g − (∫ φ(R_{i,n}))(∫ g) − ∑_{l ≠ i} ∫ φ(R_{i,l}) g)`,

the integrals being taken against the disorder-averaged overlap array law. The left-hand side is
what Vol. II, §12.2 bounds; the right-hand side is `n` times the defect in Definition 15.3.4. -/
theorem ghirlandaGuerraCombinationOf_eq_overlapArrayLaw (ν : Measure (EnergySpace N))
    [IsProbabilityMeasure ν] {κ : ℝ} {c : Config N → Config N → ℝ} (φ : C(OverlapValue, ℝ))
    (hc : ∀ σ τ : Config N, c σ τ = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) (i : Fin n) :
    FiniteGibbs.ghirlandaGuerraCombinationOf ν c n (overlapReplicaFun N g) i
      = κ * ((n : ℝ) * (∫ R, φ (R i n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          - (∫ R, φ (R i n) ∂(ν.bind (overlapArrayLaw N)))
              * (∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          - ∑ l ∈ (Finset.univ.erase i).image Fin.val,
              ∫ R, φ (R i l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N))) := by
  classical
  have hin : (i : ℕ) < n := i.2
  -- the covariance kernel, as a two-configuration function
  have hfresh : ∀ (K : EnergySpace N) (ρ : Config N),
      FiniteGibbs.freshKernelAvg (α := Config N) K c ρ
        = ∑ τ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K τ
            * (κ * φ (overlapUnit N ρ τ)) := by
    intro K ρ
    rw [FiniteGibbs.freshKernelAvg]
    exact Finset.sum_congr rfl fun τ _ => by rw [hc ρ τ]
  /- **Term A**: the new-replica term. -/
  have hA : ∀ K : EnergySpace N,
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
          (fun σs => overlapReplicaFun N g σs
            * FiniteGibbs.freshKernelAvg (α := Config N) K c (σs i))
        = κ * FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n + 1) K
            (fun ρs => φ (overlapUnit N (ρs i.castSucc) (ρs (Fin.last n)))
              * overlapReplicaFun N g (fun l => ρs l.castSucc)) := by
    intro K
    have h1 : (fun σs : FiniteGibbs.ReplicaSpace (α := Config N) n =>
          overlapReplicaFun N g σs
            * FiniteGibbs.freshKernelAvg (α := Config N) K c (σs i))
        = fun σs => overlapReplicaFun N g σs
            * ∑ τ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K τ
                * (κ * φ (overlapUnit N (σs i) τ)) :=
      funext fun σs => by rw [hfresh K (σs i)]
    rw [h1, FiniteGibbs.gibbs_average_n_det_mul_sum_gibbs_pmf (α := Config N) n K
        (overlapReplicaFun N g) (fun ρ τ => κ * φ (overlapUnit N ρ τ)) i,
      ← FiniteGibbs.gibbs_average_n_det_const_mul (α := Config N) (n + 1) K κ
        (fun ρs => φ (overlapUnit N (ρs i.castSucc) (ρs (Fin.last n)))
          * overlapReplicaFun N g (fun l => ρs l.castSucc))]
    exact congrArg (FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n + 1) K)
      (funext fun ρs => by ring)
  have hT1 : (∫ R, φ (R i n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
      = ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n + 1) K
          (fun ρs => φ (overlapUnit N (ρs i.castSucc) (ρs (Fin.last n)))
            * overlapReplicaFun N g (fun l => ρs l.castSucc)) ∂ν :=
    integral_bind_overlapArrayLaw_comp_take N (n + 1) ν
      (e := fun l : Fin (n + 1) => (l : ℕ)) Fin.val_injective
      ((φ.comp (blockEntryCM i.castSucc (Fin.last n)))
        * (g.comp (blockReindex Fin.castSucc)))
  /- **Term B**: the product term. -/
  have hT3 : (∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
      = ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
          (overlapReplicaFun N g) ∂ν :=
    integral_bind_overlapArrayLaw_comp_take N n ν
      (e := fun l : Fin n => (l : ℕ)) Fin.val_injective g
  have hB : ∀ K : EnergySpace N,
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) K
          (fun τs => FiniteGibbs.freshKernelAvg (α := Config N) K c (τs 0))
        = κ * FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 2) K
            (fun ρs => φ (overlapUnit N (ρs 0) (ρs 1))) := by
    intro K
    have h1 : (fun τs : FiniteGibbs.ReplicaSpace (α := Config N) 1 =>
          FiniteGibbs.freshKernelAvg (α := Config N) K c (τs 0))
        = fun τs => (fun _ => (1 : ℝ)) τs
            * ∑ τ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K τ
                * (κ * φ (overlapUnit N (τs 0) τ)) :=
      funext fun τs => by rw [hfresh K (τs 0), one_mul]
    rw [h1, FiniteGibbs.gibbs_average_n_det_mul_sum_gibbs_pmf (α := Config N) 1 K
        (fun _ => (1 : ℝ)) (fun ρ τ => κ * φ (overlapUnit N ρ τ)) 0,
      ← FiniteGibbs.gibbs_average_n_det_const_mul (α := Config N) 2 K κ
        (fun ρs => φ (overlapUnit N (ρs 0) (ρs 1)))]
    exact congrArg (FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 2) K)
      (funext fun ρs => by norm_num [show (Fin.last 1 : Fin 2) = 1 from rfl])
  have hT2 : (∫ R, φ (R i n) ∂(ν.bind (overlapArrayLaw N)))
      = ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 2) K
          (fun ρs => φ (overlapUnit N (ρs 0) (ρs 1))) ∂ν := by
    have hinj : Function.Injective (fun j : Fin 2 => if j = 0 then (i : ℕ) else n) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all <;> omega
    have hbase := integral_bind_overlapArrayLaw_comp_take N 2 ν
      (e := fun j : Fin 2 => if j = 0 then (i : ℕ) else n) hinj
      (φ.comp (blockEntryCM 0 1))
    simpa using hbase
  /- **Term C**: the old-replica terms. -/
  have hT4 : ∀ l : Fin n,
      (∫ R, φ (R i (l : ℕ)) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
        = ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
            (fun σs => φ (overlapUnit N (σs i) (σs l)) * overlapReplicaFun N g σs) ∂ν := fun l =>
    integral_bind_overlapArrayLaw_comp_take N n ν
      (e := fun a : Fin n => (a : ℕ)) Fin.val_injective
      ((φ.comp (blockEntryCM i l)) * g)
  have hC : ∀ (K : EnergySpace N) (l : Fin n),
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
          (fun σs => overlapReplicaFun N g σs * c (σs i) (σs l))
        = κ * FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
            (fun σs => φ (overlapUnit N (σs i) (σs l)) * overlapReplicaFun N g σs) := by
    intro K l
    rw [← FiniteGibbs.gibbs_average_n_det_const_mul (α := Config N) n K κ
      (fun σs => φ (overlapUnit N (σs i) (σs l)) * overlapReplicaFun N g σs)]
    exact congrArg (FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K)
      (funext fun σs => by rw [hc (σs i) (σs l)]; ring)
  -- reindex the sum over old replicas
  have hsum : ∑ l ∈ (Finset.univ.erase i).image Fin.val,
        (∫ R, φ (R i l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
      = ∑ l ∈ Finset.univ.erase i,
          ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
            (fun σs => φ (overlapUnit N (σs i) (σs l)) * overlapReplicaFun N g σs) ∂ν := by
    rw [Finset.sum_image fun a _ b _ h => Fin.val_injective h]
    exact Finset.sum_congr rfl fun l _ => hT4 l
  have hCsum : ∑ l ∈ Finset.univ.erase i,
        (∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
          (fun σs => overlapReplicaFun N g σs * c (σs i) (σs l)) ∂ν)
      = κ * ∑ l ∈ Finset.univ.erase i,
          ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) K
            (fun σs => φ (overlapUnit N (σs i) (σs l)) * overlapReplicaFun N g σs) ∂ν := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun K => hC K l), integral_const_mul]
  -- assemble
  rw [FiniteGibbs.ghirlandaGuerraCombinationOf, hT1, hT2, hT3, hsum,
    integral_congr_ae (Filter.Eventually.of_forall hA),
    integral_congr_ae (Filter.Eventually.of_forall hB), hCsum,
    integral_const_mul, integral_const_mul]
  ring

/-- **The translation for the Hamiltonian's own covariance kernel**: the case
`c σ τ = Cov(H σ, H τ)` of `SpinGlass.ghirlandaGuerraCombinationOf_eq_overlapArrayLaw`. -/
theorem ghirlandaGuerraCombination_eq_overlapArrayLaw (ν : Measure (EnergySpace N))
    [IsProbabilityMeasure ν] {κ : ℝ} (φ : C(OverlapValue, ℝ))
    (hcov : ∀ σ τ : Config N,
      (ProbabilityTheory.covarianceOperator ν (FiniteGibbs.std_basis (α := Config N) σ)) τ
        = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) (i : Fin n) :
    FiniteGibbs.ghirlandaGuerraCombination ν n (overlapReplicaFun N g) i
      = κ * ((n : ℝ) * (∫ R, φ (R i n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          - (∫ R, φ (R i n) ∂(ν.bind (overlapArrayLaw N)))
              * (∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          - ∑ l ∈ (Finset.univ.erase i).image Fin.val,
              ∫ R, φ (R i l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N))) :=
  ghirlandaGuerraCombinationOf_eq_overlapArrayLaw ν φ hcov g i

/-! ### The defect in Talagrand's identity (15.40) -/

lemma image_val_erase_zero (n : ℕ) (hn : 0 < n) :
    ((Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩).image Fin.val = Finset.Ico 1 n := by
  ext m
  constructor
  · intro hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
    have hl' : l ≠ ⟨0, hn⟩ := (Finset.mem_erase.1 hl).1
    refine Finset.mem_Ico.2 ⟨?_, l.2⟩
    rcases Nat.eq_zero_or_pos (l : ℕ) with h0 | h0
    · exact absurd (Fin.val_injective h0) hl'
    · exact h0
  · intro hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hm
    refine Finset.mem_image.2 ⟨⟨m, h2⟩, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, rfl⟩
    intro hcon
    have hm0 : m = 0 := by simpa [Fin.ext_iff] using hcon
    omega

/-- **The defect in Talagrand's identity (15.40) is the Ghirlanda–Guerra combination divided by
`n κ`.** The left-hand side is exactly the difference of the two sides of
`SpinGlass.SatisfiesGhirlandaGuerra` at the test functions `g ∘ blockRestrict n` and `φ`; so the
identity holds for the profile `φ` of the model precisely when the finite-volume combination is
`o(κ)`, and Vol. II, §12.2 provides the rate. -/
theorem ghirlandaGuerra_defect_eq_combinationOf {n : ℕ} (hn : 0 < n)
    (ν : Measure (EnergySpace N)) [IsProbabilityMeasure ν] {κ : ℝ} (hκ : κ ≠ 0)
    {c : Config N → Config N → ℝ} (φ : C(OverlapValue, ℝ))
    (hc : ∀ σ τ : Config N, c σ τ = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    (∫ R, φ (R 0 n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
        - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂(ν.bind (overlapArrayLaw N)))
              * ∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
              ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
      = FiniteGibbs.ghirlandaGuerraCombinationOf ν c n (overlapReplicaFun N g) ⟨0, hn⟩
          / ((n : ℝ) * κ) := by
  have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [ghirlandaGuerraCombinationOf_eq_overlapArrayLaw ν φ hc g ⟨0, hn⟩,
    image_val_erase_zero n hn]
  field_simp
  ring

/-- **The defect in Talagrand's identity (15.40) is bounded by the Ghirlanda–Guerra error of the
kernel, over `n |κ|`.** -/
theorem abs_ghirlandaGuerra_defect_of_le {n : ℕ} (hn : 0 < n)
    (ν : Measure (EnergySpace N)) [IsProbabilityMeasure ν] {κ : ℝ} (hκ : κ ≠ 0)
    {c : Config N → Config N → ℝ} (φ : C(OverlapValue, ℝ))
    (hc : ∀ σ τ : Config N, c σ τ = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) {ε : ℝ}
    (hε : |FiniteGibbs.ghirlandaGuerraCombinationOf ν c n (overlapReplicaFun N g) ⟨0, hn⟩| ≤ ε) :
    |(∫ R, φ (R 0 n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
        - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂(ν.bind (overlapArrayLaw N)))
              * ∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
              ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))|
      ≤ ε / ((n : ℝ) * |κ|) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [ghirlandaGuerra_defect_eq_combinationOf hn ν hκ φ hc g, abs_div, abs_mul,
    abs_of_pos hnR, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hε (by positivity)

/-- The Hamiltonian's own case of `SpinGlass.ghirlandaGuerra_defect_eq_combinationOf`. -/
theorem ghirlandaGuerra_defect_eq_combination {n : ℕ} (hn : 0 < n)
    (ν : Measure (EnergySpace N)) [IsProbabilityMeasure ν] {κ : ℝ} (hκ : κ ≠ 0)
    (φ : C(OverlapValue, ℝ))
    (hcov : ∀ σ τ : Config N,
      (ProbabilityTheory.covarianceOperator ν (FiniteGibbs.std_basis (α := Config N) σ)) τ
        = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    (∫ R, φ (R 0 n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
        - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂(ν.bind (overlapArrayLaw N)))
              * ∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
              ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
      = FiniteGibbs.ghirlandaGuerraCombination ν n (overlapReplicaFun N g) ⟨0, hn⟩
          / ((n : ℝ) * κ) :=
  ghirlandaGuerra_defect_eq_combinationOf hn ν hκ φ hcov g

/-- **The defect in Talagrand's identity (15.40) is bounded by the Ghirlanda–Guerra error over
`n |κ|`.** The Hamiltonian's own case of `SpinGlass.abs_ghirlandaGuerra_defect_of_le`. -/
theorem abs_ghirlandaGuerra_defect_le {n : ℕ} (hn : 0 < n)
    (ν : Measure (EnergySpace N)) [IsProbabilityMeasure ν] {κ : ℝ} (hκ : κ ≠ 0)
    (φ : C(OverlapValue, ℝ))
    (hcov : ∀ σ τ : Config N,
      (ProbabilityTheory.covarianceOperator ν (FiniteGibbs.std_basis (α := Config N) σ)) τ
        = κ * φ (overlapUnit N σ τ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) {ε : ℝ}
    (hε : |FiniteGibbs.ghirlandaGuerraCombination ν n (overlapReplicaFun N g) ⟨0, hn⟩| ≤ ε) :
    |(∫ R, φ (R 0 n) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
        - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂(ν.bind (overlapArrayLaw N)))
              * ∫ R, g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
              ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂(ν.bind (overlapArrayLaw N)))|
      ≤ ε / ((n : ℝ) * |κ|) :=
  abs_ghirlandaGuerra_defect_of_le hn ν hκ φ hcov g hε

end Translation

end

end SpinGlass
