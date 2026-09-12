/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.PairTreeField
import SpinGlass.FiniteGibbs.GaussianFieldProd
import SpinGlass.MixedPSpin
import Common.Mathlib.Analysis.Convex.TangentLine

/-!
# The coupled scheme of §14.6: the two fields, and Talagrand's choice (14.150)–(14.151)

The two-dimensional interpolation of Talagrand, Vol. II, §14.6 compares, on the pairs
`(σ¹, σ², α)`, the model Hamiltonian `H_N(σ¹) + H_N(σ²)` with the tree Hamiltonian of (14.135).

* `GaussianField.pairModel`: `(σ¹, σ², α) ↦ H(σ¹) + H(σ²)` for a field `H` on `Σ_N` with kernel
  `K`, a field on the pairs with kernel `∑_{ℓ,ℓ'} K(σ^ℓ, τ^{ℓ'})` — the image of `H` under the sum
  of the two pullbacks; for `K = N ξ(R)` this is `pairModelKernel` (`pairModelFieldOverlap`).
* `couplingFactor`, `couplingRho`: Talagrand's choice (14.150)–(14.151) — at the levels below `τ`
  the two copies share one Gaussian, from `τ` on they are independent, so that
  `ρ^{ℓ,ℓ}_p = q_p` and `ρ^{1,2}_p = q_{min(p,τ)}`; with the Parisi variances the kernel of
  `pairTreeField` is the kernel of (14.127) (`pairTreeFieldKernel_coupling`), and (14.128) holds
  with `u = q_τ` (`couplingRho_diag`).
* `wFreeEnergy_coupled_sub_le`: Lemma 14.6.1 for these fields, on the product of the model law
  with the marks law — the two-dimensional counterpart of `guerra_truncated`.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {N : ℕ} {A : Type*} [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The pair-model field -/

/-- `(σ¹, σ², α) ↦ H(σ¹) + H(σ²)`, for a field `H` on `Σ_N` with kernel `K`: the image of `H` under
the sum of the two pullbacks, with kernel `∑_{ℓ,ℓ'} K(σ^ℓ, τ^{ℓ'})`. -/
def FiniteGibbs.GaussianField.pairModel {K : Config N → Config N → ℝ}
    (G : GaussianField (α := Config N) P K) :
    GaussianField (α := PairConfig N A) P
      (fun x y => ∑ l : Fin 2, ∑ l' : Fin 2, K (x.1 l) (y.1 l')) :=
  (G.mapCLM (pullbackCLM (fun x : PairConfig N A => x.1 0)
      + pullbackCLM (fun x : PairConfig N A => x.1 1))).copy _ fun x y => by
    simp only [map_add, add_apply, adjoint_pullbackCLM_std_basis,
      PiLp.add_apply, Fin.sum_univ_two]
    have hexp : ∀ p₀ p₁ q₀ q₁ κ : ℝ,
        (p₀ + p₁) * (q₀ + q₁) * κ = p₀ * q₀ * κ + p₀ * q₁ * κ + (p₁ * q₀ * κ + p₁ * q₁ * κ) :=
      fun _ _ _ _ _ => by ring
    simp_rw [hexp, sum_add_distrib, sum_sum_std_basis_mul_std_basis_mul]

@[simp] lemma FiniteGibbs.GaussianField.pairModel_U {K : Config N → Config N → ℝ}
    (G : GaussianField (α := Config N) P K) (ω : Ω) (x : PairConfig N A) :
    (G.pairModel (A := A)).U ω x = G.U ω (x.1 0) + G.U ω (x.1 1) := rfl

/-- The pair-model field of the mixed `p`-spin model: kernel `pairModelKernel N ξ`. -/
def pairModelFieldOverlap (ξ : ℝ → ℝ)
    (G : GaussianField (α := Config N) P (fun σ τ => overlapCovMatrix N ξ σ τ)) :
    GaussianField (α := PairConfig N A) P (pairModelKernel N ξ) :=
  (G.pairModel (A := A)).copy _ fun x y => by
    simp only [pairModelKernel, pairOverlap, mul_sum]
    rfl

/-! ### Talagrand's coupling (14.150)–(14.151) -/

/-- The per-level factor of Talagrand's coupling (14.151): below `τ` the two copies share one
standard Gaussian (`y¹ = y²`), from `τ` on they are independent. -/
def couplingFactor (τ p : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if p < τ then fun _ j => if j = 0 then 1 else 0 else fun l j => if l = j then 1 else 0

lemma gram_couplingFactor_of_lt {τ p : ℕ} (h : p < τ) (l l' : Fin 2) :
    gram (couplingFactor τ p) l l' = 1 := by
  simp [gram, couplingFactor, h]

lemma gram_couplingFactor_of_le {τ p : ℕ} (h : τ ≤ p) (l l' : Fin 2) :
    gram (couplingFactor τ p) l l' = if l = l' then 1 else 0 := by
  have h' : ¬ p < τ := not_lt.2 h
  fin_cases l <;> fin_cases l' <;> simp [gram, couplingFactor, h']

variable {k : ℕ}

/-- Talagrand's `ρ^{ℓ,ℓ'}_r` for the coupling at `τ` (14.150)–(14.151): `q_r` on the diagonal,
`q_{min(r,τ)}` off it. -/
def couplingRho (qs : Fin (k + 1) → ℝ) (τ : ℕ) (l l' : Fin 2) (r : ℕ) : ℝ :=
  if l = l' then qExt qs r else qExt qs (min r τ)

lemma couplingRho_zero (qs : Fin (k + 1) → ℝ) (τ : ℕ) (l l' : Fin 2) :
    couplingRho qs τ l l' 0 = 0 := by
  simp [couplingRho]

lemma qExt_add_two (qs : Fin (k + 1) → ℝ) : qExt qs (k + 2) = 1 := by
  simp [qExt]

/-- **(14.128) for the coupling**: at the top of a tree of depth `k + 1`,
`ρ^{ℓ,ℓ}_{k+2} = 1` and `ρ^{1,2}_{k+2} = q_τ`. -/
lemma couplingRho_diag (qs : Fin (k + 1) → ℝ) {τ : ℕ} (hτ : τ ≤ k + 2) (l l' : Fin 2) :
    couplingRho qs τ l l' (k + 2) = if l = l' then 1 else qExt qs τ := by
  unfold couplingRho
  rw [min_eq_right hτ, qExt_add_two]

/-- **The kernel of the coupled marks field with Talagrand's choice** is the kernel of (14.127)
with `q^{ℓ,ℓ'}_{α,γ} = ρ^{ℓ,ℓ'}_{(α,γ)}`. -/
theorem pairTreeFieldKernel_coupling {M : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (τ : ℕ) (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (h0 : deriv ξ 0 = 0) :
    pairTreeFieldKernel N (k + 1) M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
        (couplingFactor τ 0) (fun p => couplingFactor τ (p.val + 1))
      = pairTreeKernel N ξ fun α γ l l' => couplingRho qs τ l l' (branchLevel α γ + 1) := by
  have hvar : ∀ r, r ≤ k + 1 → (parisiVar ξ qs r : ℝ)
      = deriv ξ (qExt qs (r + 1)) - deriv ξ (qExt qs r) := by
    intro r hr
    unfold parisiVar
    exact Real.coe_toNNReal _ (sub_nonneg.2 (hmono r hr))
  -- the per-level covariance identity, for a level `p` with variance `parisiVar ξ qs p`
  have hlevel : ∀ p, p ≤ k + 1 → ∀ l l' : Fin 2,
      (parisiVar ξ qs p : ℝ) * gram (couplingFactor τ p) l l'
        = deriv ξ (couplingRho qs τ l l' (p + 1)) - deriv ξ (couplingRho qs τ l l' p) := by
    intro p hp l l'
    rw [hvar p hp]
    unfold couplingRho
    by_cases hll : l = l'
    · simp only [hll, ite_true]
      rcases lt_or_ge p τ with hpτ | hpτ
      · rw [gram_couplingFactor_of_lt hpτ, mul_one]
      · rw [gram_couplingFactor_of_le hpτ, ite_eq_left rfl, mul_one]
    · simp only [hll, ite_false]
      rcases lt_or_ge p τ with hpτ | hpτ
      · rw [gram_couplingFactor_of_lt hpτ, mul_one, min_eq_left (by omega : p + 1 ≤ τ),
          min_eq_left hpτ.le]
      · rw [gram_couplingFactor_of_le hpτ, ite_eq_right hll, mul_zero,
          min_eq_right (by omega : τ ≤ p + 1), min_eq_right hpτ, sub_self]
  refine pairTreeFieldKernel_eq_pairTreeKernel N (k + 1) M hN ξ (couplingRho qs τ) _ _ _ _
    (couplingRho_zero qs τ) h0 (fun l l' => ?_) (fun p l l' => ?_)
  · exact hlevel 0 (by omega) l l'
  · have := hlevel (p.val + 1) (by omega) l l'
    simpa using this

/-! ### Lemma 14.6.1 for the coupled scheme -/

/-- The marks law of the coupled scheme: independent Gaussian pairs at every site and node, with
the Parisi variances. -/
def couplingMarksLaw (N : ℕ) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) :
    Measure (SiteMarksSpace (Fin N × Fin 2) (k + 1)) :=
  siteMarksLaw (Fin N × Fin 2) (k + 1) (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1)

instance (N : ℕ) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) :
    IsProbabilityMeasure (couplingMarksLaw N ξ qs) :=
  isProbabilityMeasure_siteMarksLaw (Fin N × Fin 2) (k + 1) _ _

/-- The marks field of the coupled scheme with Talagrand's choice; its kernel is that of (14.127)
by `pairTreeFieldKernel_coupling`. -/
def couplingTreeField (N : ℕ) (M : ℕ) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (τ : ℕ) :
    GaussianField (α := PairConfig N (TruncBranch (k + 1) M)) (couplingMarksLaw N ξ qs)
      (pairTreeFieldKernel N (k + 1) M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
        (couplingFactor τ 0) (fun p => couplingFactor τ (p.val + 1))) :=
  pairTreeField N (k + 1) M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
    (couplingFactor τ 0) (fun p => couplingFactor τ (p.val + 1))

variable {Pm : Measure Ω} [IsProbabilityMeasure Pm]

/-- **Lemma 14.6.1 for Talagrand's coupled scheme**: with the model field `H_N(σ¹) + H_N(σ²)` on
the model law and the marks field of (14.135) with the choice (14.150)–(14.151) on the marks law,
for weights carrying the constraint `R_{1,2} = q_τ`,

`𝔼 F_w(H_N(σ¹) + H_N(σ²) + c) - 𝔼 F_w(H(σ¹,σ²,α) + c) ≤ ∫₀¹ b(t) dt`,

`b(t) = -θ(1) - θ(q_τ) + (1/2) ∑_{ℓ,ℓ'} 𝔼⟨θ(ρ^{ℓ,ℓ'}_{(α,γ)})⟩_t` — the two-dimensional
counterpart of `guerra_truncated`, before the evaluation of the endpoints. -/
theorem wFreeEnergy_coupled_sub_le {M : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (hconv : ConvexOn ℝ univ ξ)
    (hdiff : Differentiable ℝ ξ) (qs : Fin (k + 1) → ℝ) {τ : ℕ} (hτ : τ ≤ k + 2)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (wt : PairConfig N (TruncBranch (k + 1) M) → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (hu : ∀ x, wt x ≠ 0 → overlap N (x.1 0) (x.1 1) = qExt qs τ)
    (c : FiniteGibbs.EnergySpace (PairConfig N (TruncBranch (k + 1) M))) :
    (∫ ω, wFreeEnergy wt N (((pairModelFieldOverlap (A := TruncBranch (k + 1) M) ξ G₀).prodLeft
          (couplingMarksLaw N ξ qs)).U ω + c) ∂Pm.prod (couplingMarksLaw N ξ qs))
        - (∫ ω, wFreeEnergy wt N (((couplingTreeField N M ξ qs τ).prodRight Pm).U ω + c)
            ∂Pm.prod (couplingMarksLaw N ξ qs))
      ≤ ∫ t in (0 : ℝ)..1, guerraBoundFn
          ((pairModelFieldOverlap (A := TruncBranch (k + 1) M) ξ G₀).prodLeft
            (couplingMarksLaw N ξ qs))
          ((couplingTreeField N M ξ qs τ).prodRight Pm) wt
          (-2 * parisiTheta ξ 1 - 2 * parisiTheta ξ (qExt qs τ))
          (fun x y => ∑ l : Fin 2, ∑ l' : Fin 2,
            parisiTheta ξ (couplingRho qs τ l l' (branchLevel x.2 y.2 + 1))) c t := by
  rw [← pairDiagConst_diag ξ (qExt qs τ)]
  exact wFreeEnergy_pair_sub_le hN ξ (fun α γ l l' => couplingRho qs τ l l' (branchLevel α γ + 1))
    (qExt qs τ) _ (fun α l l' => by rw [branchLevel_self, couplingRho_diag qs hτ]) (S := univ)
    (fun _ _ _ _ => mem_univ _) (fun x _ q _ => by
      have := hconv.add_deriv_mul_sub_le_univ hdiff q x
      linarith [mul_comm (x - q) (deriv ξ q)])
    _ _ rfl (pairTreeFieldKernel_coupling hN ξ qs τ hmono h0)
    (GaussianField.prodLeft_indepFun_prodRight _ _) wt hwt hne hu c

end

end SpinGlass
