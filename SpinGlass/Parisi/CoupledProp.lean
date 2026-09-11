/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledSite
import Common.Mathlib.Probability.PointProcess.CascadePair

/-!
# Proposition 14.6.3 (Talagrand Vol. II, §14.6): the bound for Talagrand's coupling

The specialization of (14.147) (`coupled_bound'`) to Talagrand's choice (14.155)–(14.158): for an
even `ξ`, parameters `0 = ρ₀ ≤ ρ₁ ≤ ⋯ ≤ ρ_{κ+1}`, a level `τ ≥ 1` and a sign `η = ±1`, the two
copies read the same Gaussian below `τ` (with the sign `η`, `y¹ = η y²`) and independent ones
from `τ` on (`couplingFactorSgn`), so that `ρ^{ℓ,ℓ}_p = ρ_p` and `ρ^{1,2}_p = η ρ_{min(p,τ)}`
(`couplingRhoSgn`). The extra field `H⁰` of (14.160) is carried by further columns, with
arbitrary factors. The level sum becomes (14.152)

`∑_{ℓ,ℓ'} ∑_p n_p (θ(ρ^{ℓ,ℓ'}_{p+1}) − θ(ρ^{ℓ,ℓ'}_p))
  = 4 ∑_{p < τ} n_p (θ(ρ_{p+1}) − θ(ρ_p)) + 2 ∑_{τ ≤ p ≤ κ} n_p (θ(ρ_{p+1}) − θ(ρ_p))`

(`coupledLevelSum_couplingRhoSgn`), and with the same field at every site the endpoint is
Talagrand's one-site `Y₀(λ)` (`pairSiteY₀`). This is **Proposition 14.6.3**
(`coupled_bound_coupling`), for `0 < n₁ < ⋯ < n_κ < 1` and a free top value `ρ_{κ+1}`; under
`ρ_{κ+1} = 1`, `τ ≤ κ`, `u = η ρ_τ` the diagonal defect vanishes (`coupled_bound_coupling_of_top`).
Without the extra field the left-hand side is the constrained free energy (14.149)
(`constrainedPairZ`, `coupled_bound_coupling_zero`).
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-! ### Talagrand's coupling with a sign -/

/-- Talagrand's coupling (14.157) with the sign `η`: below `τ` both copies read the first
standard Gaussian, copy `2` with the coefficient `η` (`y¹ = η y²`); from `τ` on copy `ℓ` reads
the `ℓ`-th one, so that the two are independent. -/
def couplingFactorSgn (η : ℝ) (τ p : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if p < τ then fun l j => if j = 0 then (if l = 0 then 1 else η) else 0
  else fun l j => if l = j then 1 else 0

lemma gram_couplingFactorSgn_of_lt {η : ℝ} (hη : η ^ 2 = 1) {τ p : ℕ} (h : p < τ) (l l' : Fin 2) :
    gram (couplingFactorSgn η τ p) l l' = if l = l' then 1 else η := by
  have hη' : η * η = 1 := by rw [← sq]; exact hη
  fin_cases l <;> fin_cases l' <;> simp [gram, couplingFactorSgn, h, hη']

lemma gram_couplingFactorSgn_of_le {η : ℝ} {τ p : ℕ} (h : τ ≤ p) (l l' : Fin 2) :
    gram (couplingFactorSgn η τ p) l l' = if l = l' then 1 else 0 := by
  have h' : ¬ p < τ := not_lt.2 h
  fin_cases l <;> fin_cases l' <;> simp [gram, couplingFactorSgn, h']

/-- Talagrand's `ρ^{ℓ,ℓ'}_r` (14.158): `ρ_r` on the diagonal, `η ρ_{min(r,τ)}` off it. -/
def couplingRhoSgn (ρ : ℕ → ℝ) (η : ℝ) (τ : ℕ) (l l' : Fin 2) (r : ℕ) : ℝ :=
  if l = l' then ρ r else η * ρ (min r τ)

lemma couplingRhoSgn_zero (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 0) (η : ℝ) (τ : ℕ) (l l' : Fin 2) :
    couplingRhoSgn ρ η τ l l' 0 = 0 := by
  simp [couplingRhoSgn, hρ0]

/-- (14.132) for the coupling: at the top, `ρ^{ℓ,ℓ}_{κ+1} = 1` and `ρ^{1,2}_{κ+1} = η ρ_τ = u`. -/
lemma couplingRhoSgn_top (ρ : ℕ → ℝ) (η : ℝ) {τ κ : ℕ} (hτ : τ ≤ κ) (htop : ρ (κ + 1) = 1)
    (l l' : Fin 2) :
    couplingRhoSgn ρ η τ l l' (κ + 1) = if l = l' then 1 else η * ρ τ := by
  unfold couplingRhoSgn
  rw [htop, min_eq_right (by omega)]

/-! ### The columns: the coupled marks on `Fin 2`, the extra field on `J'` -/

variable {J' : Type*} [Fintype J']

/-- The factors of the coupled marks, on the first two columns. -/
def sumL (A : Fin 2 → Fin 2 → ℝ) (l : Fin 2) : Fin 2 ⊕ J' → ℝ := Sum.elim (A l) 0

/-- The factors of the extra field, on the remaining columns. -/
def sumR (B : Fin 2 → J' → ℝ) (l : Fin 2) : Fin 2 ⊕ J' → ℝ := Sum.elim 0 (B l)

lemma gram_sumL (A : Fin 2 → Fin 2 → ℝ) (l l' : Fin 2) :
    gram (sumL (J' := J') A) l l' = gram A l l' := by
  simp [gram, sumL, Fintype.sum_sum_type]

/-- The columns of the coupled marks. -/
def leftCols (J' : Type*) [Fintype J'] : Finset (Fin 2 ⊕ J') :=
  Finset.univ.filter fun j => j.isLeft = true

lemma sumL_of_not_mem_leftCols (A : Fin 2 → Fin 2 → ℝ) (l : Fin 2) {j : Fin 2 ⊕ J'}
    (hj : j ∉ leftCols J') : sumL A l j = 0 := by
  rcases j with j | j
  · exact absurd (by simp [leftCols]) hj
  · rfl

lemma sumR_of_mem_leftCols (B : Fin 2 → J' → ℝ) (l : Fin 2) {j : Fin 2 ⊕ J'}
    (hj : j ∈ leftCols J') : sumR B l j = 0 := by
  rcases j with j | j
  · rfl
  · exact absurd hj (by simp [leftCols])

/-! ### Even profiles -/

/-- For an even `ξ`, `ξ'` is odd. -/
lemma deriv_neg_of_even {ξ : ℝ → ℝ} (heven : ∀ x, ξ (-x) = ξ x) (x : ℝ) :
    deriv ξ (-x) = -deriv ξ x := by
  have h : ξ = fun y => ξ (-y) := funext fun y => (heven y).symm
  have h2 : deriv ξ x = -deriv ξ (-x) := by
    conv_lhs => rw [h]
    exact deriv_comp_neg (f := ξ) (x := x)
  linarith

lemma deriv_sgn_mul_of_even {ξ : ℝ → ℝ} (heven : ∀ x, ξ (-x) = ξ x) {η : ℝ}
    (hη : η = 1 ∨ η = -1) (x : ℝ) : deriv ξ (η * x) = η * deriv ξ x := by
  rcases hη with rfl | rfl
  · simp
  · rw [neg_one_mul, neg_one_mul, deriv_neg_of_even heven]

/-- For an even `ξ`, `θ` is even. -/
lemma parisiTheta_sgn_mul_of_even {ξ : ℝ → ℝ} (heven : ∀ x, ξ (-x) = ξ x) {η : ℝ}
    (hη : η = 1 ∨ η = -1) (x : ℝ) : parisiTheta ξ (η * x) = parisiTheta ξ x := by
  rcases hη with rfl | rfl
  · simp
  · rw [neg_one_mul, parisiTheta, parisiTheta, deriv_neg_of_even heven, heven]
    ring

/-! ### The level sum (14.152) -/

variable {κ : ℕ}

/-- Talagrand's level sum for the coupling, (14.152):
`2 ∑_{p < τ} n_p (θ(ρ_{p+1}) − θ(ρ_p)) + ∑_{τ ≤ p ≤ κ} n_p (θ(ρ_{p+1}) − θ(ρ_p))`,
for `n_p = ns ⟨p - 1⟩`. -/
def couplingLevelSum (ξ : ℝ → ℝ) (ρ : ℕ → ℝ) (τ : ℕ) (ns : Fin κ → ℝ) : ℝ :=
  ∑ p : Fin κ, (if p.val + 1 < τ then (2 : ℝ) else 1)
    * (ns p * (parisiTheta ξ (ρ (p.val + 2)) - parisiTheta ξ (ρ (p.val + 1))))

/-- **(14.152)**: for the coupling, the level sum of (14.147) is twice `couplingLevelSum`. -/
theorem coupledLevelSum_couplingRhoSgn {ξ : ℝ → ℝ} (heven : ∀ x, ξ (-x) = ξ x) {η : ℝ}
    (hη : η = 1 ∨ η = -1) (ρ : ℕ → ℝ) (τ : ℕ) (ns : Fin κ → ℝ) :
    coupledLevelSum ξ (couplingRhoSgn ρ η τ) ns = 2 * couplingLevelSum ξ ρ τ ns := by
  unfold coupledLevelSum couplingLevelSum
  rw [Finset.mul_sum]
  refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm)).symm.trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Fin.sum_univ_two, couplingRhoSgn, Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, one_ne_zero, parisiTheta_sgn_mul_of_even heven hη]
  by_cases hp : p.val + 1 < τ
  · rw [ite_eq_left hp, min_eq_left (by omega : p.val + 2 ≤ τ),
      min_eq_left (by omega : p.val + 1 ≤ τ)]
    ring
  · rw [ite_eq_right hp, min_eq_right (by omega : τ ≤ p.val + 2),
      min_eq_right (by omega : τ ≤ p.val + 1)]
    ring

/-! ### Proposition 14.6.3 -/

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
variable (N : ℕ) {J'' : Type u} [Fintype J''] [DecidableEq J'']

/-- The variance `ξ'(ρ_{p+1}) − ξ'(ρ_p)` of the marks at level `p`, (14.156). -/
def couplingVar (ξ : ℝ → ℝ) (ρ : ℕ → ℝ) (p : ℕ) : ℝ≥0 :=
  Real.toNNReal (deriv ξ (ρ (p + 1)) - deriv ξ (ρ p))

lemma coe_couplingVar {ξ : ℝ → ℝ} {ρ : ℕ → ℝ} {p : ℕ}
    (h : deriv ξ (ρ p) ≤ deriv ξ (ρ (p + 1))) :
    (couplingVar ξ ρ p : ℝ) = deriv ξ (ρ (p + 1)) - deriv ξ (ρ p) :=
  Real.coe_toNNReal _ (sub_nonneg.2 h)

omit [DecidableEq J''] in
/-- **The covariance identities (14.133) for the coupling**: with the variances (14.156) and the
factors (14.157), `𝔼 y^ℓ_p y^{ℓ'}_p = ξ'(ρ^{ℓ,ℓ'}_{p+1}) − ξ'(ρ^{ℓ,ℓ'}_p)`. -/
lemma couplingVar_mul_gram {ξ : ℝ → ℝ} (heven : ∀ x, ξ (-x) = ξ x) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {ρ : ℕ → ℝ} {τ : ℕ}
    {p : ℕ} (hmono : deriv ξ (ρ p) ≤ deriv ξ (ρ (p + 1))) (l l' : Fin 2) :
    (couplingVar ξ ρ p : ℝ) * gram (sumL (J' := J'') (couplingFactorSgn η τ p)) l l'
      = deriv ξ (couplingRhoSgn ρ η τ l l' (p + 1)) - deriv ξ (couplingRhoSgn ρ η τ l l' p) := by
  have hη2 : η ^ 2 = 1 := by rcases hη with rfl | rfl <;> norm_num
  rw [coe_couplingVar hmono, gram_sumL]
  unfold couplingRhoSgn
  by_cases hll : l = l'
  · simp only [hll, ite_true]
    rcases lt_or_ge p τ with hpτ | hpτ
    · rw [gram_couplingFactorSgn_of_lt hη2 hpτ, ite_eq_left rfl, mul_one]
    · rw [gram_couplingFactorSgn_of_le hpτ, ite_eq_left rfl, mul_one]
  · simp only [hll, ite_false]
    rcases lt_or_ge p τ with hpτ | hpτ
    · rw [gram_couplingFactorSgn_of_lt hη2 hpτ, ite_eq_right hll,
        min_eq_left (by omega : p + 1 ≤ τ), min_eq_left hpτ.le,
        deriv_sgn_mul_of_even heven hη, deriv_sgn_mul_of_even heven hη]
      ring
    · rw [gram_couplingFactorSgn_of_le hpτ, ite_eq_right hll, mul_zero,
        min_eq_right (by omega : τ ≤ p + 1), min_eq_right hpτ, sub_self]

/-- **Proposition 14.6.3** (Talagrand Vol. II, §14.6), for `0 < n₁ < ⋯ < n_κ < 1` and a free top
value `ρ_{κ+1}`: for an even `ξ` lying above its tangent lines, parameters
`0 = ρ₀ ≤ ρ₁ ≤ ⋯ ≤ ρ_{κ+1}` along which `ξ'` is nondecreasing, Talagrand's coupling at the level
`τ` with the sign `η`, an extra field with arbitrary factors `M₀, M` on further columns, the
field `h` at every site and any `λ`,

`(1/N) 𝔼 G₁ ≤ 2 log 2 + Y₀(λ) − λu
    − 2 ∑_{p < τ} n_p (θ(ρ_{p+1}) − θ(ρ_p)) − ∑_{τ ≤ p ≤ κ} n_p (θ(ρ_{p+1}) − θ(ρ_p)) + D`,

where `G₁` is the recursion (14.160) of `∑_{R_{1,2}=u} e^{-H_N(σ¹)-H_N(σ²)-H⁰}` in the marks of
`H⁰`, `Y₀(λ)` is the one-site recursion (14.168)–(14.169) with `g_p = y_p + Z_p`, and `D` is the
diagonal defect at `ρ_{κ+1}`, which vanishes when `ρ_{κ+1} = 1`, `τ ≤ κ` and `u = η ρ_τ`. -/
theorem coupled_bound_coupling (hN : 0 < N) (ξ : ℝ → ℝ) (heven : ∀ x, ξ (-x) = ξ x)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : ℝ, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 0) (hmono : ∀ r, r ≤ κ → deriv ξ (ρ r) ≤ deriv ξ (ρ (r + 1)))
    {η : ℝ} (hη : η = 1 ∨ η = -1) (τ : ℕ) (u : ℝ)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (M₀ : Fin 2 → J'' → ℝ) (M : Fin κ → Fin 2 → J'' → ℝ) (h : Fin 2 → ℝ) (lam : ℝ)
    (ns : Fin κ → ℝ) (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ J'')) κ fun p => couplingVar ξ ρ (p.val + 1))
        (coupledG N u (fun s => h s.2) (sumL (couplingFactorSgn η τ 0)) (sumR M₀)
          (fun p => sumL (couplingFactorSgn η τ (p.val + 1))) (fun p => sumR (M p)) ξ G₀ 1
          θ)).toReal ∂Pm.prod (rootMarksLaw N (couplingVar ξ ρ 0))
      ≤ 2 * Real.log 2
          + pairSiteY₀ ns (couplingVar ξ ρ 0) (fun p => couplingVar ξ ρ (p.val + 1)) lam h
            (sumL (couplingFactorSgn η τ 0) + sumR M₀)
            (fun p => sumL (couplingFactorSgn η τ (p.val + 1)) + sumR (M p))
          - lam * u - couplingLevelSum ξ ρ τ ns
          + pairDiagDefect ξ u (fun l l' => couplingRhoSgn ρ η τ l l' (κ + 1)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := coupled_bound' N hN ξ (couplingRhoSgn ρ η τ) u
    (couplingRhoSgn_zero ρ hρ0 η τ) (S := univ) (fun _ _ _ => mem_univ _)
    (fun x hx q _ => htan x hx q) h0 G₀ (couplingVar ξ ρ 0) (fun p => couplingVar ξ ρ (p.val + 1))
    (J₁ := leftCols J'') (L₀ := sumL (couplingFactorSgn η τ 0)) (L₀' := sumR M₀)
    (L := fun p => sumL (couplingFactorSgn η τ (p.val + 1))) (L' := fun p => sumR (M p))
    (fun l l' => couplingVar_mul_gram heven hη (hmono 0 (Nat.zero_le _)) l l')
    (fun p l l' => couplingVar_mul_gram heven hη (hmono (p.val + 1) (by omega)) l l')
    (fun l j hj => sumL_of_not_mem_leftCols _ l hj)
    (fun p l j hj => sumL_of_not_mem_leftCols _ l hj)
    (fun l j hj => sumR_of_mem_leftCols _ l hj)
    (fun p l j hj => sumR_of_mem_leftCols _ l hj)
    (fun s => h s.2) lam ns hsm hpos hlt hu
  rw [integral_parisiRec_pairCoshF N ns hsm hpos hlt _ _ lam h _ _,
    coupledLevelSum_couplingRhoSgn heven hη ρ τ ns] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

/-- **Proposition 14.6.3 under Talagrand's normalization** `ρ_{κ+1} = 1`, `τ ≤ κ`, `u = η ρ_τ`:
the diagonal defect vanishes. -/
theorem coupled_bound_coupling_of_top (hN : 0 < N) (ξ : ℝ → ℝ) (heven : ∀ x, ξ (-x) = ξ x)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : ℝ, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 0) (hmono : ∀ r, r ≤ κ → deriv ξ (ρ r) ≤ deriv ξ (ρ (r + 1)))
    (htop : ρ (κ + 1) = 1) {η : ℝ} (hη : η = 1 ∨ η = -1) {τ : ℕ} (hτκ : τ ≤ κ)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = η * ρ τ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (M₀ : Fin 2 → J'' → ℝ) (M : Fin κ → Fin 2 → J'' → ℝ) (h : Fin 2 → ℝ) (lam : ℝ)
    (ns : Fin κ → ℝ) (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ J'')) κ fun p => couplingVar ξ ρ (p.val + 1))
        (coupledG N (η * ρ τ) (fun s => h s.2) (sumL (couplingFactorSgn η τ 0)) (sumR M₀)
          (fun p => sumL (couplingFactorSgn η τ (p.val + 1))) (fun p => sumR (M p)) ξ G₀ 1
          θ)).toReal ∂Pm.prod (rootMarksLaw N (couplingVar ξ ρ 0))
      ≤ 2 * Real.log 2
          + pairSiteY₀ ns (couplingVar ξ ρ 0) (fun p => couplingVar ξ ρ (p.val + 1)) lam h
            (sumL (couplingFactorSgn η τ 0) + sumR M₀)
            (fun p => sumL (couplingFactorSgn η τ (p.val + 1)) + sumR (M p))
          - lam * (η * ρ τ) - couplingLevelSum ξ ρ τ ns := by
  have hb := coupled_bound_coupling N hN ξ heven htan h0 ρ hρ0 hmono hη τ (η * ρ τ) hu G₀ M₀ M h
    lam ns hsm hpos hlt
  have hd : (fun l l' => couplingRhoSgn ρ η τ l l' (κ + 1))
      = fun l l' => if l = l' then (1 : ℝ) else η * ρ τ :=
    funext fun l => funext fun l' => couplingRhoSgn_top ρ η hτκ htop l l'
  rw [hd, pairDiagDefect_diag, add_zero] at hb
  exact hb

/-! ### Without the extra field: the constrained free energy (14.149) -/

omit [Fintype J'] in
lemma sumR_zero : sumR (J' := J') (0 : Fin 2 → J' → ℝ) = 0 := by
  funext l j
  rcases j with j | j <;> rfl

/-- The constrained partition function of (14.149),
`∑_{R_{1,2}=u} exp (−H(σ¹) − H(σ²) − ∑_{i,ℓ} σ^ℓ_i a(i,ℓ))` (the field `a` enters with the sign of a
Hamiltonian: Talagrand's `+ ∑ᵢ hᵢ(σ¹ᵢ + σ²ᵢ)` is `a(i,ℓ) = −hᵢ`). -/
def constrainedPairZ (u : ℝ) (H : EnergySpace N) (a : Fin N × Fin 2 → ℝ) : ℝ :=
  ∑ σ : Fin 2 → Config N, constraintR N u σ
    * Real.exp (-(H (σ 0) + H (σ 1) + ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * a (i, l)))

omit [DecidableEq J''] in
lemma constrainedPairZ_nonneg (u : ℝ) (H : EnergySpace N) (a : Fin N × Fin 2 → ℝ) :
    0 ≤ constrainedPairZ N u H a :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (constraintR_nonneg N u σ) (Real.exp_pos _).le

omit [DecidableEq J''] in
lemma continuous_constrainedPairZ (u : ℝ) (a : Fin N × Fin 2 → ℝ) :
    Continuous fun H : EnergySpace N => constrainedPairZ N u H a := by
  unfold constrainedPairZ
  refine continuous_finsetSum _ fun σ _ => continuous_const.mul (Real.continuous_exp.comp
    (Continuous.neg (Continuous.add (Continuous.add ?_ ?_) continuous_const)))
  · exact (continuous_apply (σ 0)).comp (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))
  · exact (continuous_apply (σ 1)).comp (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))

omit [IsProbabilityMeasure Pm] [DecidableEq J''] in
/-- Without extra field the branch functions at `t = 1` do not depend on the marks. -/
lemma coupledG_one_zero (u : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ : Fin 2 → J'' → ℝ)
    (L : Fin κ → Fin 2 → J'' → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (θ : Ω × (Fin N × J'' → ℝ)) (x : Fin κ → Fin N × J'' → ℝ) :
    coupledG N u a L₀ 0 L 0 ξ G₀ 1 θ x = ENNReal.ofReal (constrainedPairZ N u (G₀.U θ.1) a) := by
  unfold coupledG pairHamG pairBranchZX constrainedPairZ
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  unfold pairBranchHamX pairBranchMark
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, add_zero,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]

omit [DecidableEq J''] in
/-- `Y₀` does not see the unused columns. -/
lemma pairSiteY₀_sumL (ns : Fin κ → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (A₀ : Fin 2 → Fin 2 → ℝ) (A : Fin κ → Fin 2 → Fin 2 → ℝ) :
    pairSiteY₀ (J := Fin 2 ⊕ J'') ns v₀ vs lam h (sumL A₀) (fun p => sumL (A p))
      = pairSiteY₀ (J := Fin 2) ns v₀ vs lam h A₀ A := by
  classical
  -- the one-site function only reads the first two columns
  have hF : ∀ (y₀ : Fin 2 ⊕ J'' → ℝ) (y : Fin κ → Fin 2 ⊕ J'' → ℝ),
      pairSiteF lam h (sumL A₀) (fun p => sumL (A p)) y₀ y
        = pairSiteF lam h A₀ A (y₀ ∘ Sum.inl) (fun p => y p ∘ Sum.inl) := by
    intro y₀ y
    unfold pairSiteF pairSiteMark
    simp [sumL, Fintype.sum_sum_type]
  set φ : (Fin 2 ⊕ J'' → ℝ) → (Fin 2 → ℝ) := fun y => y ∘ Sum.inl with hφ
  have hφm : Measurable φ := measurable_comp_right (E := ℝ) Sum.inl
  have hmap : ∀ p : Fin κ, (siteGaussianMarks (Fin 2 ⊕ J'') κ vs p).map φ
      = siteGaussianMarks (Fin 2) κ vs p := fun p =>
    map_comp_pi_of_injective (gaussianReal 0 (vs p)) Sum.inl_injective
  have hmap' : (fun p => (siteGaussianMarks (Fin 2 ⊕ J'') κ vs p).map φ)
      = siteGaussianMarks (Fin 2) κ vs := funext hmap
  have hmap₀ : (Measure.pi fun _ : Fin 2 ⊕ J'' => gaussianReal 0 v₀).map φ
      = Measure.pi fun _ : Fin 2 => gaussianReal 0 v₀ :=
    map_comp_pi_of_injective (gaussianReal 0 v₀) Sum.inl_injective
  -- the inner recursion
  have hinner : ∀ y₀ : Fin 2 ⊕ J'' → ℝ,
      parisiRec κ ns (siteGaussianMarks (Fin 2 ⊕ J'') κ vs)
          (pairSiteF lam h (sumL A₀) (fun p => sumL (A p)) y₀)
        = parisiRec κ ns (siteGaussianMarks (Fin 2) κ vs) (pairSiteF lam h A₀ A (φ y₀)) := by
    intro y₀
    rw [← hmap', parisiRec_map κ ns _ (fun _ => φ) (fun _ => hφm)
      (measurable_pairSiteF' lam h A₀ A (φ y₀))]
    exact congrArg _ (funext fun y => hF y₀ y)
  -- measurability of the one-site recursion in the root marks
  have hfm : Measurable fun y₀ : Fin 2 → ℝ => parisiRec κ ns (siteGaussianMarks (Fin 2) κ vs)
      (pairSiteF lam h A₀ A y₀) := by
    have hc := continuous_pairSiteF lam h A₀ A
    have hG : Measurable (Function.uncurry fun (y₀ : Fin 2 → ℝ) (y : Fin κ → Fin 2 → ℝ) =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h A₀ A y₀ y))) := by
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hR : Measurable fun y₀ : Fin 2 → ℝ => cascadeRec κ ns (siteGaussianMarks (Fin 2) κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h A₀ A y₀ y))) :=
      measurable_cascadeRec_prod κ ns (siteGaussianMarks (Fin 2) κ vs) hG
    exact hR.ennreal_toReal.log
  unfold pairSiteY₀
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), ← hmap₀,
    integral_map hφm.aemeasurable hfm.aestronglyMeasurable]

/-- **Proposition 14.6.3 without the extra field** (Talagrand's (14.149)): for the constrained
free energy `(1/N) 𝔼 log ∑_{R_{1,2}=u} e^{−H_N(σ¹) − H_N(σ²) − ∑ σ^ℓ_i h_ℓ}`,

`(1/N) 𝔼 log ∑_{R_{1,2}=u} … ≤ 2 log 2 + Y₀(λ) − λu − 2 ∑_{p<τ} n_p (θ(ρ_{p+1}) − θ(ρ_p))
    − ∑_{τ ≤ p ≤ κ} n_p (θ(ρ_{p+1}) − θ(ρ_p)) + D`,

with the one-site `Y₀(λ)` of the coupling on two columns. -/
theorem coupled_bound_coupling_zero (hN : 0 < N) (ξ : ℝ → ℝ) (heven : ∀ x, ξ (-x) = ξ x)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : ℝ, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 0) (hmono : ∀ r, r ≤ κ → deriv ξ (ρ r) ≤ deriv ξ (ρ (r + 1)))
    {η : ℝ} (hη : η = 1 ∨ η = -1) (τ : ℕ) (u : ℝ)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (h : Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ) (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    (1 / (N : ℝ)) * ∫ ω, Real.log (constrainedPairZ N u (G₀.U ω) (fun s => h s.2)) ∂Pm
      ≤ 2 * Real.log 2
          + pairSiteY₀ (J := Fin 2) ns (couplingVar ξ ρ 0) (fun p => couplingVar ξ ρ (p.val + 1))
            lam h (couplingFactorSgn η τ 0) (fun p => couplingFactorSgn η τ (p.val + 1))
          - lam * u - couplingLevelSum ξ ρ τ ns
          + pairDiagDefect ξ u (fun l l' => couplingRhoSgn ρ η τ l l' (κ + 1)) := by
  have hb := coupled_bound_coupling N hN ξ heven htan h0 ρ hρ0 hmono hη τ u hu G₀
    (J'' := PEmpty.{u + 1}) 0 0 h lam ns hsm hpos hlt
  simp only [Pi.zero_apply, sumR_zero, add_zero] at hb
  rw [pairSiteY₀_sumL] at hb
  -- the left-hand side: the branch functions are constant, and the recursion of a constant is
  -- that constant
  have hpt : ∀ θ : Ω × (Fin N × (Fin 2 ⊕ PEmpty.{u + 1}) → ℝ),
      Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ PEmpty.{u + 1})) κ
          fun p => couplingVar ξ ρ (p.val + 1))
        (coupledG N u (fun s => h s.2) (sumL (couplingFactorSgn η τ 0)) 0
          (fun p : Fin κ => sumL (couplingFactorSgn η τ (p.val + 1)))
          (fun _ : Fin κ => (0 : Fin 2 → Fin 2 ⊕ PEmpty.{u + 1} → ℝ)) ξ G₀ 1 θ)).toReal
      = Real.log (constrainedPairZ N u (G₀.U θ.1) (fun s => h s.2)) := by
    intro θ
    have he : coupledG N u (fun s => h s.2) (sumL (couplingFactorSgn η τ 0)) 0
        (fun p : Fin κ => sumL (couplingFactorSgn η τ (p.val + 1)))
        (fun _ : Fin κ => (0 : Fin 2 → Fin 2 ⊕ PEmpty.{u + 1} → ℝ)) ξ G₀ 1 θ
        = fun _ => ENNReal.ofReal (constrainedPairZ N u (G₀.U θ.1) (fun s => h s.2)) :=
      funext fun x => coupledG_one_zero N u (fun s => h s.2) (sumL (couplingFactorSgn η τ 0))
        (fun p : Fin κ => sumL (couplingFactorSgn η τ (p.val + 1))) ξ G₀ θ x
    rw [he, cascadeRec_const κ ns _ hpos, ENNReal.toReal_ofReal (constrainedPairZ_nonneg N u _ _)]
  have hm : Measurable fun ω : Ω => Real.log (constrainedPairZ N u (G₀.U ω) (fun s => h s.2)) := by
    have h1 := (continuous_constrainedPairZ N u (fun s => h s.2)).measurable.comp G₀.measU
    have h2 := Real.measurable_log.comp h1
    exact h2
  have hmap : (Pm.prod (rootMarksLaw (J := Fin 2 ⊕ PEmpty.{u + 1}) N (couplingVar ξ ρ 0))).map
      Prod.fst = Pm := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hL : (∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ PEmpty.{u + 1})) κ
          fun p => couplingVar ξ ρ (p.val + 1))
        (coupledG N u (fun s => h s.2) (sumL (couplingFactorSgn η τ 0)) 0
          (fun p : Fin κ => sumL (couplingFactorSgn η τ (p.val + 1)))
          (fun _ : Fin κ => (0 : Fin 2 → Fin 2 ⊕ PEmpty.{u + 1} → ℝ)) ξ G₀ 1 θ)).toReal
        ∂Pm.prod (rootMarksLaw N (couplingVar ξ ρ 0)))
      = ∫ ω, Real.log (constrainedPairZ N u (G₀.U ω) (fun s => h s.2)) ∂Pm := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hi := integral_map (μ := Pm.prod (rootMarksLaw (J := Fin 2 ⊕ PEmpty.{u + 1}) N
      (couplingVar ξ ρ 0))) measurable_fst.aemeasurable hm.aestronglyMeasurable
    rw [hmap] at hi
    exact hi.symm
  rw [hL] at hb
  exact hb

end

end SpinGlass
