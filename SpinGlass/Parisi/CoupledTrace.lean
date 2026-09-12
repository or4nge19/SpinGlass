/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.TreeTrace
import SpinGlass.Parisi.GuerraBound

/-!
# The Guerra trace of the coupled system: Lemma 14.6.1

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.6. To bound the free energy of two
**coupled copies** — a sum restricted to the pairs `(σ¹, σ²)` with `R_{1,2} = u` — one runs Guerra's
interpolation on the system of *pairs*. The state space is `(Fin 2 → Σ_N) × A`, the model kernel is
the covariance of `H_N(σ¹) + H_N(σ²)`,

`K₁(x, y) = N ∑_{ℓ,ℓ'} ξ(R^{ℓ,ℓ'})`,   `R^{ℓ,ℓ'} = R(σ^ℓ, τ^{ℓ'})`,

and the interpolating Hamiltonian of (14.127) has kernel

`K₂(x, y) = N ∑_{ℓ,ℓ'} R^{ℓ,ℓ'} ξ'(q^{ℓ,ℓ'}_{α,γ})`.

The point of the construction (Talagrand's own emphasis) is the diagonal. The term created by the
interaction of `H_N(σ¹)` with `H_N(σ²)` is `⟨ξ(R_{1,2}) - R_{1,2} ξ'(u)⟩`, which has the *wrong
sign* to be bounded above by the tangent-line inequality; it is exactly the restriction of the sum
to the pairs with `R_{1,2} = u` that turns it into a constant and saves the day. If the diagonal
values `q^{ℓ,ℓ'}_{α,α} = d^{ℓ,ℓ'}` do not depend on `α`, the whole diagonal is the constant
`pairDiagConst ξ u d = ∑_{ℓ,ℓ'} (ξ(R^{ℓ,ℓ'}) - R^{ℓ,ℓ'} ξ'(d^{ℓ,ℓ'}))`, `R^{ℓ,ℓ} = 1`, `R^{1,2} = u`
— under Talagrand's (14.128), `d = (1, u; u, 1)`, this is `-2θ(1) - 2θ(u)` — and the off-diagonal
is controlled by convexity, giving **(14.129)**

`φ*'(s) ≤ (1/2) pairDiagConst ξ u d + (1/2) ∑_{ℓ,ℓ'} 𝔼⟨θ(q^{ℓ,ℓ'}_{α,γ})⟩`.

Leaving `d` free is what allows the last level of the tree to carry an arbitrary parameter
`ρ_{κ+1}` (the level `n_{κ+1} = 1` of Proposition 14.6.3 is then absorbed exactly, with no
continuity argument in the `n_p`).

## Main statements

- `SpinGlass.wGuerraTrace_pair_eq`: the Guerra trace of the coupled system, *exactly*.
- `SpinGlass.wGuerraTrace_pair_le`: **Lemma 14.6.1 / (14.129)**.
- `SpinGlass.wFreeEnergy_pair_sub_le`: Lemma 14.6.1 integrated over the interpolation — the
  free-energy comparison for coupled copies, `𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ b(t) dt` with
  `b(t) = (1/2) pairDiagConst ξ u d + (1/2) ∑_{ℓ,ℓ'} 𝔼⟨θ(q^{ℓ,ℓ'}_{α,γ})⟩_t`.

The restriction `R_{1,2} = u` is imposed by giving weight `0` to every other pair
(`hu`), which is why the whole development runs in the *weighted* interpolation framework of
`FiniteGibbs/WeightedInterpolation`: the weights carry both the cascade weights `w_α` and the
constraint.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {N : ℕ} {A : Type*} [Fintype A]

/-- The state space of Talagrand's two-dimensional scheme (§14.6): a pair of configurations,
indexed by `Fin 2`, together with a branch index. -/
abbrev PairConfig (N : ℕ) (A : Type*) := (Fin 2 → Config N) × A

/-- `R^{ℓ,ℓ'} = R(σ^ℓ, τ^{ℓ'})`, the four overlaps of two pairs of configurations. -/
def pairOverlap (N : ℕ) (x y : PairConfig N A) (l l' : Fin 2) : ℝ :=
  overlap N (x.1 l) (y.1 l')

/-- The model kernel of the coupled system, `N ∑_{ℓ,ℓ'} ξ(R^{ℓ,ℓ'})`: the covariance of
`H_N(σ¹) + H_N(σ²)` for a Hamiltonian of type (14.55). -/
def pairModelKernel (N : ℕ) (ξ : ℝ → ℝ) (x y : PairConfig N A) : ℝ :=
  (N : ℝ) * ∑ l : Fin 2, ∑ l' : Fin 2, ξ (pairOverlap N x y l l')

/-- The kernel of the interpolating Hamiltonian of **(14.127)**,
`N ∑_{ℓ,ℓ'} R^{ℓ,ℓ'} ξ'(q^{ℓ,ℓ'}_{α,γ})`. -/
def pairTreeKernel (N : ℕ) (ξ : ℝ → ℝ) (qt : A → A → Fin 2 → Fin 2 → ℝ)
    (x y : PairConfig N A) : ℝ :=
  (N : ℝ) * ∑ l : Fin 2, ∑ l' : Fin 2,
    pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')

omit [Fintype A] in
lemma pairOverlap_diag_self (hN : 0 < N) (x : PairConfig N A) (l : Fin 2) :
    pairOverlap N x x l l = 1 :=
  overlap_self (N := N) hN _

omit [Fintype A] in
/-- On the diagonal the four overlaps of a pair with itself are `1, u, u, 1` as soon as the pair
is constrained by `R_{1,2} = u`. -/
lemma pairOverlap_diag (hN : 0 < N) {u : ℝ} (x : PairConfig N A)
    (hx : overlap N (x.1 0) (x.1 1) = u) (l l' : Fin 2) :
    pairOverlap N x x l l' = if l = l' then 1 else u := by
  have h10 : overlap N (x.1 1) (x.1 0) = u := by
    rw [overlap_comm (N := N)]; exact hx
  have hdd : ∀ j : Fin 2, overlap N (x.1 j) (x.1 j) = 1 := fun _ =>
    overlap_self (N := N) hN _
  fin_cases l <;> fin_cases l' <;> simp [pairOverlap, hdd, hx, h10]

/-- **The diagonal constant of the coupled Guerra trace**: for the self-overlaps `R^{ℓ,ℓ} = 1`,
`R^{1,2} = R^{2,1} = u` of a constrained pair and the diagonal values `d^{ℓ,ℓ'}` of the
interpolation parameters, `∑_{ℓ,ℓ'} (ξ(R^{ℓ,ℓ'}) - R^{ℓ,ℓ'} ξ'(d^{ℓ,ℓ'}))`. -/
def pairDiagConst (ξ : ℝ → ℝ) (u : ℝ) (d : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ l : Fin 2, ∑ l' : Fin 2,
    (ξ (if l = l' then 1 else u) - (if l = l' then 1 else u) * deriv ξ (d l l'))

/-- Under Talagrand's (14.128), `d = (1, u; u, 1)`, the diagonal constant is `-2θ(1) - 2θ(u)`. -/
lemma pairDiagConst_diag (ξ : ℝ → ℝ) (u : ℝ) :
    pairDiagConst ξ u (fun l l' => if l = l' then 1 else u)
      = -2 * parisiTheta ξ 1 - 2 * parisiTheta ξ u := by
  simp only [pairDiagConst, Fin.sum_univ_two, parisiTheta]
  norm_num
  ring

/-- **The Guerra trace of the coupled system, exactly.** If the diagonal values `q^{ℓ,ℓ'}_{α,α}`
do not depend on `α` and the weights carry the constraint `R_{1,2} = u`, the diagonal contributes
the constant `pairDiagConst ξ u d` and the trace is

`(1/2) pairDiagConst ξ u d - (1/2) ⟨∑_{ℓ,ℓ'} (ξ(R^{ℓ,ℓ'}) - R^{ℓ,ℓ'} ξ'(q^{ℓ,ℓ'}_{α,γ}))⟩`. -/
theorem wGuerraTrace_pair_eq (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → Fin 2 → Fin 2 → ℝ) (u : ℝ)
    (d : Fin 2 → Fin 2 → ℝ) (hq : ∀ α l l', qt α α l l' = d l l')
    (wt : PairConfig N A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (hu : ∀ x, wt x ≠ 0 → overlap N (x.1 0) (x.1 1) = u)
    (H : FiniteGibbs.EnergySpace (PairConfig N A)) :
    wGuerraTrace wt (pairModelKernel N ξ) (pairTreeKernel N ξ qt) N H
      = (1 / 2) * pairDiagConst ξ u d
        - (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y
            * ∑ l : Fin 2, ∑ l' : Fin 2, (ξ (pairOverlap N x y l l')
                - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')) := by
  unfold wGuerraTrace
  -- the diagonal, on the support of the weights
  have hdiag : ∀ x : PairConfig N A, wt x ≠ 0 →
      pairModelKernel N ξ x x - pairTreeKernel N ξ qt x x = (N : ℝ) * pairDiagConst ξ u d := by
    intro x hx
    simp only [pairModelKernel, pairTreeKernel, pairOverlap_diag hN x (hu x hx), hq,
      pairDiagConst, Fin.sum_univ_two]
    norm_num
    ring
  have hd : ∀ x : PairConfig N A,
      (pairModelKernel N ξ x x - pairTreeKernel N ξ qt x x) * wGibbs wt H x
        = ((N : ℝ) * pairDiagConst ξ u d) * wGibbs wt H x := by
    intro x
    by_cases hx : wt x = 0
    · rw [wGibbs_of_eq_zero wt H hx, mul_zero, mul_zero]
    · rw [hdiag x hx]
  -- the off-diagonal
  have hoff : ∀ x y : PairConfig N A,
      (pairModelKernel N ξ x y - pairTreeKernel N ξ qt x y) * (wGibbs wt H x * wGibbs wt H y)
        = (N : ℝ) * (wGibbs wt H x * wGibbs wt H y
            * ∑ l : Fin 2, ∑ l' : Fin 2, (ξ (pairOverlap N x y l l')
                - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l'))) := by
    intro x y
    simp only [pairModelKernel, pairTreeKernel]
    have hs : (∑ l : Fin 2, ∑ l' : Fin 2, ξ (pairOverlap N x y l l'))
        - ∑ l : Fin 2, ∑ l' : Fin 2, pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')
        = ∑ l : Fin 2, ∑ l' : Fin 2, (ξ (pairOverlap N x y l l')
            - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => (Finset.sum_sub_distrib _ _).symm
    rw [← mul_sub, hs]
    ring
  simp_rw [hd, hoff]
  rw [← Finset.mul_sum, sum_wGibbs wt hwt hne H, mul_one]
  simp_rw [← Finset.mul_sum]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **Lemma 14.6.1 / (14.129)** (Talagrand Vol. II): if `ξ` lies above its tangent lines at the
values `q^{ℓ,ℓ'}_{α,γ}` that occur (a set `S`; for a convex `ξ` any set will do, and in particular
`u` may be negative), then the Guerra trace of the coupled system is at most

`(1/2) pairDiagConst ξ u d + (1/2) ⟨∑_{ℓ,ℓ'} θ(q^{ℓ,ℓ'}_{α,γ})⟩`,   `θ(x) = x ξ'(x) - ξ(x)`,

which is `-θ(1) - θ(u) + (1/2) ⟨∑_{ℓ,ℓ'} θ(q^{ℓ,ℓ'}_{α,γ})⟩` under (14.128). Composed with
`FiniteGibbs.wFreeEnergy_sub_le` this is the two-dimensional version of Guerra's Lemma 14.4.1,
the basic tool of §14.6. -/
theorem wGuerraTrace_pair_le (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → Fin 2 → Fin 2 → ℝ) (u : ℝ)
    (d : Fin 2 → Fin 2 → ℝ) (hq : ∀ α l l', qt α α l l' = d l l')
    {S : Set ℝ} (hqS : ∀ α γ l l', qt α γ l l' ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (wt : PairConfig N A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (hu : ∀ x, wt x ≠ 0 → overlap N (x.1 0) (x.1 1) = u)
    (H : FiniteGibbs.EnergySpace (PairConfig N A)) :
    wGuerraTrace wt (pairModelKernel N ξ) (pairTreeKernel N ξ qt) N H
      ≤ (1 / 2) * pairDiagConst ξ u d
        + (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y
            * ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (qt x.2 y.2 l l') := by
  rw [wGuerraTrace_pair_eq hN ξ qt u d hq wt hwt hne hu H]
  have hkey : ∀ x y : PairConfig N A,
      -(wGibbs wt H x * wGibbs wt H y * ∑ l : Fin 2, ∑ l' : Fin 2,
            (ξ (pairOverlap N x y l l')
              - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')))
        ≤ wGibbs wt H x * wGibbs wt H y
            * ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (qt x.2 y.2 l l') := by
    intro x y
    have hg : 0 ≤ wGibbs wt H x * wGibbs wt H y :=
      mul_nonneg (wGibbs_nonneg wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y)
    have hsum : -(∑ l : Fin 2, ∑ l' : Fin 2, (ξ (pairOverlap N x y l l')
          - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')))
        ≤ ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (qt x.2 y.2 l l') := by
      rw [neg_le, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun l' _ => ?_
      have hR : pairOverlap N x y l l' ∈ Icc (-1 : ℝ) 1 :=
        abs_le.1 (abs_overlap_le_one N _ _)
      have h := htan _ hR _ (hqS x.2 y.2 l l')
      unfold parisiTheta
      linarith
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hsum hg
  have hfin : -(∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y
        * ∑ l : Fin 2, ∑ l' : Fin 2, (ξ (pairOverlap N x y l l')
            - pairOverlap N x y l l' * deriv ξ (qt x.2 y.2 l l')))
      ≤ ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y
          * ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (qt x.2 y.2 l l') := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun y _ => hkey x y
  linarith

/-! ### Lemma 14.6.1 in free-energy form -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Lemma 14.6.1, integrated** (Talagrand Vol. II, (14.129) over `s ∈ [0, 1]`): for independent
centered Gaussian fields on the pairs whose kernels are the model kernel and the interpolating
kernel of (14.127), and weights carrying the constraint `R_{1,2} = u`,

`𝔼 F_w(U + c) - 𝔼 F_w(V + c)
  ≤ ∫₀¹ ((1/2) pairDiagConst ξ u d + (1/2) ∑_{ℓ,ℓ'} 𝔼⟨θ(q^{ℓ,ℓ'}_{α,γ})⟩_t) dt`,

where `F_w(H) = (1/N) log ∑_{R_{1,2} = u, α} w_α e^{-H(σ¹,σ²,α)}` is the free energy of the coupled
copies. This is the basic tool of §14.6. -/
theorem wFreeEnergy_pair_sub_le (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → Fin 2 → Fin 2 → ℝ)
    (u : ℝ) (d : Fin 2 → Fin 2 → ℝ) (hq : ∀ α l l', qt α α l l' = d l l')
    {S : Set ℝ} (hqS : ∀ α γ l l', qt α γ l l' ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    {K₁ K₂ : PairConfig N A → PairConfig N A → ℝ}
    (G₁ : GaussianField (α := PairConfig N A) P K₁) (G₂ : GaussianField (α := PairConfig N A) P K₂)
    (hK₁ : K₁ = pairModelKernel N ξ) (hK₂ : K₂ = pairTreeKernel N ξ qt)
    (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : PairConfig N A → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (hu : ∀ x, wt x ≠ 0 → overlap N (x.1 0) (x.1 1) = u)
    (c : FiniteGibbs.EnergySpace (PairConfig N A)) :
    (∫ ω, wFreeEnergy wt N (G₁.U ω + c) ∂P) - (∫ ω, wFreeEnergy wt N (G₂.U ω + c) ∂P)
      ≤ ∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt (pairDiagConst ξ u d)
          (fun x y => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (qt x.2 y.2 l l')) c t :=
  wFreeEnergy_sub_le_of_le_treeBoundIntegrand G₁ G₂ hindep wt hwt hne N c _ _ fun H => by
    rw [hK₁, hK₂]
    exact (wGuerraTrace_pair_le hN ξ qt u d hq hqS htan wt hwt hne hu H).trans (le_of_eq rfl)

end

end SpinGlass
