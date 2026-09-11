/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GaussianFieldPullback

/-!
# Guerra's interpolation for a weighted free energy

The free energy of a Hamiltonian `H` on a finite state space with **nonnegative weights**
`w : α → ℝ` — `(1/n) log ∑_x w_x exp(-H x)` — is the free energy on the support `{w ≠ 0}` of
the shifted Hamiltonian `H - log w`. Pulling the Gaussian fields back to the support
(`GaussianField.comp`) therefore gives Guerra's comparison bound for weighted free energies
(`wFreeEnergy_sub_le`), with the derivative controlled by the **weighted Guerra trace**
`(1/(2n)) [∑_x (K₁-K₂)(x,x) g_x - ∑_{x,y} (K₁-K₂)(x,y) g_x g_y]`, `g` the weighted Gibbs weights.
This is Lemma 14.4.1 of Talagrand (Vol. II, §14.4) for the weights `w_α` of a finite family of
branches, zero weights allowed — the form needed for a truncated Poisson–Dirichlet cascade, some of
whose branches do not exist.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α]

/-! ### Weighted partition function, free energy, Gibbs weights and trace -/

/-- The weighted partition function `∑_x w_x exp(-H x)`. -/
def wZ (wt : α → ℝ) (H : EnergySpace α) : ℝ := ∑ x, wt x * Real.exp (-H x)

/-- The weighted free energy density `(1/n) log ∑_x w_x exp(-H x)`. -/
def wFreeEnergy (wt : α → ℝ) (n : ℕ) (H : EnergySpace α) : ℝ := (1 / (n : ℝ)) * Real.log (wZ wt H)

/-- The weighted Gibbs weights `w_x exp(-H x) / ∑_y w_y exp(-H y)`. -/
def wGibbs (wt : α → ℝ) (H : EnergySpace α) (x : α) : ℝ := wt x * Real.exp (-H x) / wZ wt H

/-- The weighted Guerra trace
`(1/(2n)) [∑_x (K₁-K₂)(x,x) g_x - ∑_{x,y} (K₁-K₂)(x,y) g_x g_y]`. -/
def wGuerraTrace (wt : α → ℝ) (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) : ℝ :=
  (1 / (2 * (n : ℝ))) * ((∑ x : α, (K₁ x x - K₂ x x) * wGibbs wt H x)
    - ∑ x : α, ∑ y : α, (K₁ x y - K₂ x y) * (wGibbs wt H x * wGibbs wt H y))

/-! ### Constrained weights -/

omit [Fintype α] in
/-- Restricting the weights by a `[0, 1]`-valued factor can only decrease the partition function. -/
lemma wZ_mul_le [Fintype α] (wt c : α → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hc1 : ∀ x, c x ≤ 1) (H : EnergySpace α) :
    wZ (fun x => wt x * c x) H ≤ wZ wt H :=
  Finset.sum_le_sum fun x _ => by
    change wt x * c x * Real.exp (-H x) ≤ wt x * Real.exp (-H x)
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hwt x) (hc1 x))
      (Real.exp_pos _).le

omit [Fintype α] in
/-- **Tilting a constrained partition function**: if the weights vanish off `{R = u}`, adding
`-λ R` to the Hamiltonian multiplies the partition function by `exp (λ u)`. -/
lemma wZ_mul_sub_smul [Fintype α] (wt c : α → ℝ) (R : α → ℝ) {u : ℝ} (lam : ℝ)
    (hR : ∀ x, c x ≠ 0 → R x = u) (H : EnergySpace α) :
    wZ (fun x => wt x * c x) (H - lam • WithLp.toLp 2 R)
      = Real.exp (lam * u) * wZ (fun x => wt x * c x) H := by
  unfold wZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hc : c x = 0
  · simp [hc]
  · have hsub : (H - lam • WithLp.toLp 2 R) x = H x - lam * R x := rfl
    rw [hsub, hR x hc, show -(H x - lam * u) = lam * u + -H x by ring, Real.exp_add]
    ring

omit [Fintype α] in
/-- **The `λ`-trick** (Talagrand Vol. II, (14.140)): a sum restricted to `{R = u}` is at most
`exp (-λ u)` times the unrestricted sum with `-λ R` added to the Hamiltonian, for every `λ`. -/
lemma wZ_mul_le_exp_mul_wZ_sub [Fintype α] (wt c : α → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hc1 : ∀ x, c x ≤ 1) (R : α → ℝ) {u : ℝ} (lam : ℝ)
    (hR : ∀ x, c x ≠ 0 → R x = u) (H : EnergySpace α) :
    wZ (fun x => wt x * c x) H
      ≤ Real.exp (-(lam * u)) * wZ wt (H - lam • WithLp.toLp 2 R) := by
  have h := wZ_mul_sub_smul wt c R lam hR H
  have hpos : 0 < Real.exp (lam * u) := Real.exp_pos _
  have hle := wZ_mul_le wt c hwt hc1 (H - lam • WithLp.toLp 2 R)
  rw [h] at hle
  rw [Real.exp_neg]
  exact (le_inv_mul_iff₀ hpos).2 hle

/-! ### Product state spaces: weights `u_α · c_x` -/

section Prod

variable {X A : Type*} [Fintype X] [Fintype A]

/-- The partial partition function `Z_α(c) = ∑_x c_x e^{-H(x, α)}` of the block `α`. -/
def wCondZ (c : X → ℝ) (H : EnergySpace (X × A)) (α : A) : ℝ :=
  ∑ x, c x * Real.exp (-H (x, α))

/-- The weighted partition function on `X × A` with weights `u_α c_x` is `∑_α u_α Z_α(c)`. -/
lemma wZ_prod_eq (u : A → ℝ) (c : X → ℝ) (H : EnergySpace (X × A)) :
    wZ (fun p => u p.2 * c p.1) H = ∑ α, u α * wCondZ c H α := by
  unfold wZ wCondZ
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Marginalizing a pair average to the blocks**: the Gibbs pair average on `X × A` of a function
of the `A`-components is the pair average over `A` with the weights `u_α Z_α(c)`. -/
theorem sum_wGibbs_prod_pair (u : A → ℝ) (c : X → ℝ) (H : EnergySpace (X × A))
    (φ : A → A → ℝ) :
    (∑ p, ∑ q, wGibbs (fun p : X × A => u p.2 * c p.1) H p
        * wGibbs (fun p : X × A => u p.2 * c p.1) H q * φ p.2 q.2)
      = (∑ α, ∑ γ, u α * wCondZ c H α * (u γ * wCondZ c H γ) * φ α γ)
        / (∑ α, u α * wCondZ c H α) ^ 2 := by
  have hZ : ∀ p : X × A, wGibbs (fun p : X × A => u p.2 * c p.1) H p
      = u p.2 * c p.1 * Real.exp (-H p) / ∑ α, u α * wCondZ c H α := by
    intro p
    rw [wGibbs, wZ_prod_eq]
  have hsplit : ∀ g : X × A → ℝ, ∑ p, g p = ∑ α, ∑ x, g (x, α) := by
    intro g
    rw [Fintype.sum_prod_type (f := g), Finset.sum_comm]
  simp_rw [hZ, hsplit]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp only [wCondZ, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end Prod

/-! ### Transport to the support -/

/-- The support of the weights. -/
abbrev Support (wt : α → ℝ) : Type _ := {x : α // wt x ≠ 0}

/-- The shift `log w` on the support, as an element of the energy space. -/
def logWeights (wt : α → ℝ) : EnergySpace (Support wt) :=
  WithLp.toLp 2 fun x => Real.log (wt x.val)

/-- The shifted Hamiltonian `H - log w` on the support. -/
def shiftHam (wt : α → ℝ) (H : EnergySpace α) : EnergySpace (Support wt) :=
  pullbackCLM Subtype.val H - logWeights wt

lemma shiftHam_apply (wt : α → ℝ) (H : EnergySpace α) (x : Support wt) :
    shiftHam wt H x = H x.val - Real.log (wt x.val) := rfl

lemma shiftHam_add (wt : α → ℝ) (H c : EnergySpace α) :
    shiftHam wt (H + c) = pullbackCLM Subtype.val H + shiftHam wt c := by
  unfold shiftHam
  rw [map_add]
  abel

/-- A sum over the support is a sum over all states of the terms that vanish off the support. -/
lemma sum_support_eq (wt : α → ℝ) (g : α → ℝ) (hg : ∀ x, wt x = 0 → g x = 0) :
    ∑ x : Support wt, g x.val = ∑ x : α, g x := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun x => wt x ≠ 0) (by simp) g,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · rw [hg x (not_not.1 h)]

lemma exp_neg_shiftHam (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (H : EnergySpace α)
    (x : Support wt) : Real.exp (-shiftHam wt H x) = wt x.val * Real.exp (-H x.val) := by
  rw [shiftHam_apply, neg_sub, Real.exp_sub, Real.exp_log (lt_of_le_of_ne (hwt _) x.2.symm),
    Real.exp_neg, div_eq_mul_inv]

/-- The weighted partition function is the partition function of the shifted Hamiltonian. -/
lemma wZ_eq_Z (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (H : EnergySpace α) :
    wZ wt H = Z (α := Support wt) (shiftHam wt H) := by
  unfold wZ Z
  simp_rw [exp_neg_shiftHam wt hwt H]
  exact (sum_support_eq wt _ fun x hx => by rw [hx, zero_mul]).symm

/-- The weighted free energy is the free energy of the shifted Hamiltonian. -/
lemma wFreeEnergy_eq (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (n : ℕ) (H : EnergySpace α) :
    wFreeEnergy wt n H = free_energy_density (α := Support wt) n (shiftHam wt H) := by
  unfold wFreeEnergy free_energy_density
  rw [wZ_eq_Z wt hwt]

/-- The weighted Gibbs weights are the Gibbs weights of the shifted Hamiltonian. -/
lemma wGibbs_eq (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (H : EnergySpace α) (x : Support wt) :
    wGibbs wt H x.val = gibbs_pmf (α := Support wt) (shiftHam wt H) x := by
  unfold wGibbs gibbs_pmf
  rw [exp_neg_shiftHam wt hwt, wZ_eq_Z wt hwt]

lemma wGibbs_of_eq_zero (wt : α → ℝ) (H : EnergySpace α) {x : α} (hx : wt x = 0) :
    wGibbs wt H x = 0 := by
  simp [wGibbs, hx]

lemma wZ_pos (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (H : EnergySpace α) :
    0 < wZ wt H := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine Finset.sum_pos' (fun x _ => mul_nonneg (hwt x) (Real.exp_pos _).le) ⟨x₀, Finset.mem_univ _,
    mul_pos (lt_of_le_of_ne (hwt x₀) hx₀.symm) (Real.exp_pos _)⟩

lemma wGibbs_nonneg (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : EnergySpace α) (x : α) : 0 ≤ wGibbs wt H x :=
  div_nonneg (mul_nonneg (hwt x) (Real.exp_pos _).le) (wZ_pos wt hwt hne H).le

lemma wGibbs_le_one (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : EnergySpace α) (x : α) : wGibbs wt H x ≤ 1 := by
  unfold wGibbs
  rw [div_le_one (wZ_pos wt hwt hne H)]
  exact Finset.single_le_sum (f := fun y => wt y * Real.exp (-H y))
    (fun y _ => mul_nonneg (hwt y) (Real.exp_pos _).le) (Finset.mem_univ x)

/-- The weighted Guerra trace is bounded uniformly in the Hamiltonian. -/
lemma abs_wGuerraTrace_le (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) :
    |wGuerraTrace wt K₁ K₂ n H|
      ≤ (1 / (2 * (n : ℝ))) * ((∑ x, |K₁ x x - K₂ x x|) + ∑ x, ∑ y, |K₁ x y - K₂ x y|) := by
  unfold wGuerraTrace
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) (by positivity)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)).trans (mul_one _).le
    rw [abs_of_nonneg (wGibbs_nonneg wt hwt hne H x)]
    exact wGibbs_le_one wt hwt hne H x
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)).trans (mul_one _).le
    rw [abs_of_nonneg (mul_nonneg (wGibbs_nonneg wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y))]
    exact mul_le_one₀ (wGibbs_le_one wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y)
      (wGibbs_le_one wt hwt hne H y)

/-- The weighted Gibbs weights sum to one. -/
lemma sum_wGibbs (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : EnergySpace α) : ∑ x, wGibbs wt H x = 1 := by
  unfold wGibbs
  rw [← Finset.sum_div]
  exact div_self (wZ_pos wt hwt hne H).ne'

/-- The weighted Guerra trace is the Guerra trace of the restricted kernels at the shifted
Hamiltonian. -/
lemma wGuerraTrace_eq (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (K₁ K₂ : α → α → ℝ) (n : ℕ)
    (H : EnergySpace α) :
    wGuerraTrace wt K₁ K₂ n H
      = guerraTrace (α := Support wt) (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
          (shiftHam wt H) := by
  rw [guerraTrace_eq]
  unfold wGuerraTrace
  congr 1
  congr 1
  · rw [← sum_support_eq wt (fun x => (K₁ x x - K₂ x x) * wGibbs wt H x)
      (fun x hx => by rw [wGibbs_of_eq_zero wt H hx, mul_zero])]
    exact Finset.sum_congr rfl fun x _ => by rw [wGibbs_eq wt hwt]
  · rw [← sum_support_eq wt
      (fun x => ∑ y : α, (K₁ x y - K₂ x y) * (wGibbs wt H x * wGibbs wt H y))
      (fun x hx => by simp [wGibbs_of_eq_zero wt H hx])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← sum_support_eq wt
      (fun y => (K₁ x.val y - K₂ x.val y) * (wGibbs wt H x.val * wGibbs wt H y))
      (fun y hy => by simp [wGibbs_of_eq_zero wt H hy])]
    exact Finset.sum_congr rfl fun y _ => by rw [wGibbs_eq wt hwt, wGibbs_eq wt hwt]

/-! ### The weighted comparison bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K₁ K₂ : α → α → ℝ}
  (G₁ : GaussianField (α := α) P K₁) (G₂ : GaussianField (α := α) P K₂)

/-- The pullback of a pair of Hamiltonians to the support. -/
def pairPullback (wt : α → ℝ) : PairSpace α → PairSpace (Support wt) := fun p =>
  WithLp.toLp 2 (pullbackCLM Subtype.val (WithLp.ofLp p).1,
    pullbackCLM Subtype.val (WithLp.ofLp p).2)

lemma measurable_pairPullback (wt : α → ℝ) : Measurable (pairPullback (α := α) wt) :=
  measurable_toLp_prodMk
    ((pullbackCLM Subtype.val).continuous.measurable.comp
      ((WithLp.prod_continuous_ofLp (p := (2 : ℝ≥0∞)) (α := EnergySpace α)
        (β := EnergySpace α)).fst.measurable))
    ((pullbackCLM Subtype.val).continuous.measurable.comp
      ((WithLp.prod_continuous_ofLp (p := (2 : ℝ≥0∞)) (α := EnergySpace α)
        (β := EnergySpace α)).snd.measurable))

lemma pairLaw_comp (wt : α → ℝ) :
    pairLaw (G₁.comp (Subtype.val : Support wt → α)) (G₂.comp Subtype.val)
      = (pairLaw G₁ G₂).map (pairPullback wt) := by
  change P.map (pair (G₁.comp _) (G₂.comp _)) = (P.map (pair G₁ G₂)).map (pairPullback wt)
  rw [Measure.map_map (measurable_pairPullback wt) (measurable_pair G₁ G₂)]
  rfl

lemma gaussianInterp_pairPullback (wt : α → ℝ) (t : ℝ) (p : PairSpace α) :
    gaussianInterp t (pairPullback wt p) = pullbackCLM Subtype.val (gaussianInterp t p) := by
  simp only [gaussianInterp_apply, pairPullback]
  rw [map_add, map_smul, map_smul]

/-- **Guerra's comparison bound for a weighted free energy**: for nonnegative weights `w`, not all
zero, independent centered Gaussian fields `U, V` with kernels `K₁, K₂`, and a fixed vector `c`,
if the averaged weighted Guerra trace along the path is at most `b t` on `(0,1)`, then
`𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ b`, where `F_w(H) = (1/n) log ∑_x w_x exp(-H x)`. -/
theorem wFreeEnergy_sub_le (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (c : EnergySpace α) (n : ℕ) {b : ℝ → ℝ}
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p : PairSpace α, wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) ≤ b t)
    (hbint : IntervalIntegrable b volume 0 1) :
    (∫ ω, wFreeEnergy wt n (G₁.U ω + c) ∂P) - (∫ ω, wFreeEnergy wt n (G₂.U ω + c) ∂P)
      ≤ ∫ t in (0 : ℝ)..1, b t := by
  have : Nonempty (Support wt) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hindep' := GaussianField.comp_indepFun hindep (Subtype.val : Support wt → α) Subtype.val
  have hcontH : Continuous fun H : EnergySpace (Support wt) =>
      guerraTrace (α := Support wt) (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n H :=
    continuous_guerraTrace _ _ n
  have hb' : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p : PairSpace (Support wt), guerraTrace (α := Support wt)
        (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
        (gaussianInterp t p + shiftHam wt c)
        ∂pairLaw (G₁.comp Subtype.val) (G₂.comp Subtype.val)) ≤ b t := by
    intro t ht
    have hmeasF : AEStronglyMeasurable (fun p : PairSpace (Support wt) =>
        guerraTrace (α := Support wt) (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
          (gaussianInterp t p + shiftHam wt c)) ((pairLaw G₁ G₂).map (pairPullback wt)) :=
      (hcontH.comp ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
    rw [pairLaw_comp, integral_map (measurable_pairPullback wt).aemeasurable hmeasF]
    refine le_trans (le_of_eq ?_) (hb t ht)
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change guerraTrace (α := Support wt) (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
        (gaussianInterp t (pairPullback wt p) + shiftHam wt c)
      = wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c)
    rw [gaussianInterp_pairPullback, wGuerraTrace_eq wt hwt, shiftHam_add]
  have h := guerraPhi_one_sub_zero_le (G₁.comp Subtype.val) (G₂.comp Subtype.val) hindep'
    (shiftHam wt c) n hb' hbint
  rw [guerraPhi_one, guerraPhi_zero] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change wFreeEnergy wt n (G₁.U ω + c)
      = free_energy_density (α := Support wt) n ((G₁.comp Subtype.val).U ω + shiftHam wt c)
    rw [wFreeEnergy_eq wt hwt, shiftHam_add]
    rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change wFreeEnergy wt n (G₂.U ω + c)
      = free_energy_density (α := Support wt) n ((G₂.comp Subtype.val).U ω + shiftHam wt c)
    rw [wFreeEnergy_eq wt hwt, shiftHam_add]
    rfl

end

end FiniteGibbs

end SpinGlass
