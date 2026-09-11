/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledEndpoint
import SpinGlass.Parisi.BranchAverages

/-!
# The coupled copies along a branch

The two-copy counterpart of `BranchAverages` (Talagrand, Vol. II, §14.6). With per-level factors
`K₀, K_p : Fin 2 → J → ℝ` and marks `z₀, x_p ∈ ℝ^{Fin N × J}` along a branch, the copy `ℓ` sees at
the site `i` the mark

`y^ℓ_i = ∑_j (K₀)_{ℓj} z₀(i,j) + ∑_p ∑_j (K_p)_{ℓj} x_p(i,j)`   (`pairBranchMark`),

which is the field `pairTreeField` evaluated along the branch (`pairTreeLin_siteTreeCoords_apply`,
the two-copy (14.73)). The branch Hamiltonian of the pair

`H(σ¹) + H(σ²) - λ ∑_i σ¹_i σ²_i + ∑_ℓ ∑_i σ^ℓ_i (a(i,ℓ) + y^ℓ_i)`   (`pairBranchHamX`)

carries the whole interpolation in its parameters: `H = √s H_N`, and `K = √(1-s) L + L'` for the
interpolating factors `L` and the factors `L'` of the external field `H⁰` of (14.136); `λ` is the
parameter of the bound (14.140) and `a` a deterministic external field. Its **constrained partition
function** `∑_σ c_σ e^{-H(σ)}` (`pairBranchZX`, `pairHamG` in `ℝ≥0∞`), with `c = 1_{R_{1,2} = u}`
for (14.125), has finite Gaussian moments (`cascadeRec_pairHamG_ne_top`, Talagrand's (14.4)), and
at `H = 0` without constraint it is `∏ᵢ 4 (ch A_i ch B_i ch λ + sh A_i sh B_i sh λ)` by (14.142)
(`pairBranchZX_one_zero`), i.e. `exp (N log 4 + Y_{κ+1})` for the site sum `Y_{κ+1}` of (14.144)
(`pairCoshF`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ) {J : Type*} [Fintype J]

/-! ### An algebraic identity -/

omit N k in
/-- `∑_ℓ ∑_i σ^ℓ_i ∑_p ∑_j K_{p,ℓj} x_p(i,j) = ∑_p ∑_{(i,j)} (∑_ℓ σ^ℓ_i K_{p,ℓj}) x_p(i,j)`. -/
lemma sum_sum_mul_sum_sum_eq {ι P : Type*} [Fintype ι] [Fintype P] (σ : Fin 2 → ι → ℝ)
    (K : P → Fin 2 → J → ℝ) (x : P → ι × J → ℝ) :
    ∑ l : Fin 2, ∑ i, σ l i * ∑ p, ∑ j, K p l j * x p (i, j)
      = ∑ p, ∑ c : ι × J, (∑ l : Fin 2, σ l c.1 * K p l c.2) * x p c := by
  simp only [Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  refine (Finset.sum_comm.trans ((Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun p _ => Finset.sum_comm)).trans Finset.sum_comm)).trans ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit N k in
/-- `∑_ℓ ∑_i σ^ℓ_i ∑_j K_{ℓj} z(i,j) = ∑_{(i,j)} (∑_ℓ σ^ℓ_i K_{ℓj}) z(i,j)`. -/
lemma sum_sum_mul_sum_eq {ι : Type*} [Fintype ι] (σ : Fin 2 → ι → ℝ) (K : Fin 2 → J → ℝ)
    (z : ι × J → ℝ) :
    ∑ l : Fin 2, ∑ i, σ l i * ∑ j, K l j * z (i, j)
      = ∑ c : ι × J, (∑ l : Fin 2, σ l c.1 * K l c.2) * z c := by
  simp only [Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_comm.trans ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### The marks seen by the two copies along a branch -/

/-- The coupled mark of the copy `ℓ` at the site `i`:
`∑_j (K₀)_{ℓj} z₀(i,j) + ∑_p ∑_j (K_p)_{ℓj} x_p(i,j)`. -/
def pairBranchMark (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) (l : Fin 2) (i : Fin N) : ℝ :=
  ∑ j, K₀ l j * z₀ (i, j) + ∑ p, ∑ j, K p l j * x p (i, j)

/-- **The coupled field along a branch** (the two-copy (14.73)): at `(σ, α)` the field of
`pairTreeField` is `∑_ℓ ∑_i σ^ℓ_i y^ℓ_i` with the marks of the nodes of `α`. -/
theorem pairTreeLin_siteTreeCoords_apply (M : ℕ) (L₀ : Fin 2 → J → ℝ)
    (L : Fin k → Fin 2 → J → ℝ) (ω : SiteMarksSpace (Fin N × J) k)
    (x : PairConfig N (TruncBranch k M)) :
    coordLin (pairTreeCoeff N k M L₀ L) (siteTreeCoords (Fin N × J) k M ω) x
      = ∑ l : Fin 2, ∑ i, isingSpin (x.1 l i)
          * pairBranchMark N k L₀ L ω.1 (fun p => truncMarks k M ω.2 (branchNode k M x.2 p))
            l i := by
  classical
  rw [coordLin_apply, Fintype.sum_sum_type (f := fun c => pairTreeCoeff N k M L₀ L x c
    * siteTreeCoords (Fin N × J) k M ω c)]
  rw [Fintype.sum_prod_type (f := fun c : TruncNode k M × (Fin N × J) =>
    pairTreeCoeff N k M L₀ L x (Sum.inr c) * siteTreeCoords (Fin N × J) k M ω (Sum.inr c))]
  simp only [pairTreeCoeff, siteTreeCoords, Sum.elim_inl, Sum.elim_inr, pairBranchMark, mul_add,
    Finset.sum_add_distrib]
  congr 1
  · -- the level-`0` block
    rw [Fintype.sum_prod_type (f := fun c : Fin N × J =>
      (∑ l : Fin 2, isingSpin (x.1 l c.1) * L₀ l c.2) * ω.1 c)]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  · -- the node blocks
    have hsum : ∀ v : TruncNode k M, (∑ c : Fin N × J,
        (if v = branchNode k M x.2 v.1 then ∑ l : Fin 2, isingSpin (x.1 l c.1) * L v.1 l c.2 else 0)
          * truncMarks k M ω.2 v c)
        = if v = branchNode k M x.2 v.1
          then ∑ c : Fin N × J, (∑ l : Fin 2, isingSpin (x.1 l c.1) * L v.1 l c.2)
            * truncMarks k M ω.2 v c else 0 := by
      intro v
      split_ifs <;> simp
    simp_rw [hsum]
    rw [sum_truncNode_branchNode k M x.2 (fun v => ∑ c : Fin N × J,
      (∑ l : Fin 2, isingSpin (x.1 l c.1) * L v.1 l c.2) * truncMarks k M ω.2 v c)]
    simp only [branchNode, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans (Eq.trans ?_ Finset.sum_comm.symm)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine ((Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ### The branch Hamiltonian and the constrained branch partition function -/

/-- The Hamiltonian of the coupled pair on a branch, as a function of the root marks `z₀` and
of the marks `x` along the branch (the two-copy (14.77)):
`H(σ¹) + H(σ²) - λ ∑_i σ¹_i σ²_i + ∑_ℓ ∑_i σ^ℓ_i (a(i,ℓ) + y^ℓ_i)`. -/
def pairBranchHamX (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ)
    (σ : Fin 2 → Config N) : ℝ :=
  H (σ 0) + H (σ 1) - lam * ∑ i, isingSpin (σ 0 i) * isingSpin (σ 1 i)
    + ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * (a (i, l) + pairBranchMark N k K₀ K z₀ x l i)

/-- The constrained branch partition function `∑_σ c_σ e^{-H(σ)}` (the two-copy (14.78), with
the constraint `c = 1_{R_{1,2} = u}` of (14.125)). -/
def pairBranchZX (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) : ℝ :=
  ∑ σ : Fin 2 → Config N, c σ * Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ)

lemma pairBranchZX_nonneg {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (H : EnergySpace N)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) : 0 ≤ pairBranchZX N k c H lam a K₀ K z₀ x :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (hc0 σ) (Real.exp_pos _).le

lemma pairBranchZX_pos {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    (hcne : ∃ σ, 0 < c σ) (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    (x : Fin k → Fin N × J → ℝ) : 0 < pairBranchZX N k c H lam a K₀ K z₀ x := by
  obtain ⟨σ₀, hσ₀⟩ := hcne
  exact Finset.sum_pos' (fun σ _ => mul_nonneg (hc0 σ) (Real.exp_pos _).le)
    ⟨σ₀, Finset.mem_univ _, mul_pos hσ₀ (Real.exp_pos _)⟩

/-- The parameters of the branch Hamiltonian: the Hamiltonian `H`, the factors `K₀`, `K` and the
marks `z₀`, `x`. -/
abbrev PairBranchParam (N k : ℕ) (J : Type*) : Type _ :=
  (EnergySpace N × (Fin 2 → J → ℝ) × (Fin k → Fin 2 → J → ℝ))
    × ((Fin N × J → ℝ) × (Fin k → Fin N × J → ℝ))

/-- Instance search does not find this instance on the fivefold product. -/
instance : OpensMeasurableSpace (PairBranchParam N k J) := Prod.opensMeasurableSpace

lemma continuous_pairBranchMark (l : Fin 2) (i : Fin N) :
    Continuous fun q : PairBranchParam N k J =>
      pairBranchMark N k q.1.2.1 q.1.2.2 q.2.1 q.2.2 l i := by
  unfold pairBranchMark
  fun_prop

/-- Joint continuity of the constrained branch partition function in `(H, K₀, K, z₀, x)`. -/
lemma continuous_pairBranchZX (c : (Fin 2 → Config N) → ℝ) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) :
    Continuous fun q : PairBranchParam N k J =>
      pairBranchZX N k c q.1.1 lam a q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  unfold pairBranchZX pairBranchHamX
  have hH : ∀ τ : Config N, Continuous fun q : PairBranchParam N k J => q.1.1 τ := fun τ =>
    ((continuous_apply τ).comp (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).comp
      continuous_fst.fst
  refine continuous_finsetSum _ fun σ _ => continuous_const.mul
    (Real.continuous_exp.comp (Continuous.neg ?_))
  exact (((hH (σ 0)).add (hH (σ 1))).sub continuous_const).add
    (continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_const.add (continuous_pairBranchMark N k (J := J) l i)))

/-- Continuity of the constrained branch partition function in the marks along the branch. -/
lemma continuous_pairBranchZX' (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) : Continuous (pairBranchZX N k c H lam a K₀ K z₀) :=
  (continuous_pairBranchZX N k c lam a).comp
    ((continuous_const (y := (H, K₀, K))).prodMk ((continuous_const (y := z₀)).prodMk
      continuous_id))

/-- The constrained branch partition function in `ℝ≥0∞`, as a function of the marks along the
branch: the branch weight of the coupled Gibbs measure. -/
def pairHamG (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    (x : Fin k → Fin N × J → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (pairBranchZX N k c H lam a K₀ K z₀ x)

lemma pairHamG_pos {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hcne : ∃ σ, 0 < c σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    0 < pairHamG N k c H lam a K₀ K z₀ x :=
  ENNReal.ofReal_pos.2 (pairBranchZX_pos N k hc0 hcne H lam a K₀ K z₀ x)

/-- `|log ∑_σ c_σ e^{-H(σ)}| ≤ log |Σ_N²| + ∑_σ |H(σ)|` for `0 ≤ c ≤ 1` with `c_{σ₀} = 1`. -/
lemma abs_log_pairHamG_le {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    (hc1 : ∀ σ, c σ ≤ 1) {σ₀ : Fin 2 → Config N} (hσ₀ : c σ₀ = 1) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    |Real.log (pairHamG N k c H lam a K₀ K z₀ x).toReal|
      ≤ Real.log (Fintype.card (Fin 2 → Config N))
        + ∑ τ, |pairBranchHamX N k H lam a K₀ K z₀ x τ| := by
  set B := ∑ τ, |pairBranchHamX N k H lam a K₀ K z₀ x τ| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcard : (1 : ℝ) ≤ Fintype.card (Fin 2 → Config N) := by
    exact_mod_cast Fintype.card_pos (α := Fin 2 → Config N)
  have hlogc : 0 ≤ Real.log (Fintype.card (Fin 2 → Config N)) := Real.log_nonneg hcard
  have hle_each : ∀ τ, |pairBranchHamX N k H lam a K₀ K z₀ x τ| ≤ B := fun τ =>
    Finset.single_le_sum (f := fun τ => |pairBranchHamX N k H lam a K₀ K z₀ x τ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  have hZpos : 0 < pairBranchZX N k c H lam a K₀ K z₀ x :=
    pairBranchZX_pos N k hc0 ⟨σ₀, by rw [hσ₀]; exact one_pos⟩ _ _ _ _ _ _ _
  have hup : pairBranchZX N k c H lam a K₀ K z₀ x
      ≤ Fintype.card (Fin 2 → Config N) * Real.exp B := by
    unfold pairBranchZX
    calc ∑ σ : Fin 2 → Config N, c σ * Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ)
        ≤ ∑ _σ : Fin 2 → Config N, Real.exp B := Finset.sum_le_sum fun σ _ => by
          calc c σ * Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ)
              ≤ 1 * Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ) :=
                mul_le_mul_of_nonneg_right (hc1 σ) (Real.exp_pos _).le
            _ ≤ Real.exp B := by
                rw [one_mul]
                exact Real.exp_le_exp.2 ((neg_le_abs _).trans (hle_each σ))
      _ = Fintype.card (Fin 2 → Config N) * Real.exp B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlow : Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ₀)
      ≤ pairBranchZX N k c H lam a K₀ K z₀ x := by
    unfold pairBranchZX
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun σ => c σ * Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ))
      (fun σ _ => mul_nonneg (hc0 σ) (Real.exp_pos _).le) (Finset.mem_univ σ₀))
    rw [hσ₀, one_mul]
  rw [pairHamG, ENNReal.toReal_ofReal hZpos.le, abs_le]
  constructor
  · have h1 : -B ≤ -pairBranchHamX N k H lam a K₀ K z₀ x σ₀ := by
      have := hle_each σ₀
      have := le_abs_self (pairBranchHamX N k H lam a K₀ K z₀ x σ₀)
      linarith
    have h2 : -pairBranchHamX N k H lam a K₀ K z₀ x σ₀
        ≤ Real.log (pairBranchZX N k c H lam a K₀ K z₀ x) := by
      rw [← Real.log_exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ₀)]
      exact Real.log_le_log (Real.exp_pos _) hlow
    linarith
  · calc Real.log (pairBranchZX N k c H lam a K₀ K z₀ x)
        ≤ Real.log (Fintype.card (Fin 2 → Config N) * Real.exp B) := Real.log_le_log hZpos hup
      _ = Real.log (Fintype.card (Fin 2 → Config N)) + B := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

lemma measurable_pairHamG (c : (Fin 2 → Config N) → ℝ) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) :
    Measurable fun q : PairBranchParam N k J =>
      pairHamG N k c q.1.1 lam a q.1.2.1 q.1.2.2 q.2.1 q.2.2 :=
  (continuous_pairBranchZX N k c lam a).measurable.ennreal_ofReal

lemma measurable_pairHamG' (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) : Measurable (pairHamG N k c H lam a K₀ K z₀) :=
  (continuous_pairBranchZX' N k c H lam a K₀ K z₀).measurable.ennreal_ofReal

section Param

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The parameters of the branch Hamiltonian from a disorder sample `ω`, the root marks `z₀` and
the marks `x` along the branch, for the disorder Hamiltonian `Hf ω`. -/
def branchParam (Hf : Ω → EnergySpace N) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (p : (Ω × (Fin N × J → ℝ)) × (Fin k → Fin N × J → ℝ)) : PairBranchParam N k J :=
  ((Hf p.1.1, K₀, K), (p.1.2, p.2))

omit [Fintype J] in
lemma measurable_branchParam {Hf : Ω → EnergySpace N} (hHf : Measurable Hf)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Measurable (branchParam N k Hf K₀ K) :=
  ((hHf.comp (measurable_fst.comp measurable_fst)).prodMk measurable_const).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Joint measurability of the branch weight in the disorder sample, the root marks and the
marks along the branch. -/
lemma measurable_pairHamG_branchParam (c : (Fin 2 → Config N) → ℝ) {Hf : Ω → EnergySpace N}
    (hHf : Measurable Hf) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) :
    Measurable fun p : (Ω × (Fin N × J → ℝ)) × (Fin k → Fin N × J → ℝ) =>
      pairHamG N k c (Hf p.1.1) lam a K₀ K p.1.2 p.2 := by
  have h := (measurable_pairHamG N k c lam a).comp (measurable_branchParam N k hHf K₀ K)
  exact h

end Param

/-! ### Gaussian finiteness: Talagrand's (14.4) -/

/-- The constant part of `-H(σ)`. -/
def pairBranchA (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (σ : Fin 2 → Config N) : ℝ :=
  -(H (σ 0) + H (σ 1) - lam * ∑ i, isingSpin (σ 0 i) * isingSpin (σ 1 i)
    + ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * (a (i, l) + ∑ j, K₀ l j * z₀ (i, j)))

/-- The coefficients of `-H(σ)` in the marks along the branch. -/
def pairBranchB (K : Fin k → Fin 2 → J → ℝ) (σ : Fin 2 → Config N) (p : Fin k)
    (s : Fin N × J) : ℝ :=
  -(∑ l : Fin 2, isingSpin (σ l s.1) * K p l s.2)

/-- The constant part of `-H(σ)`, split into the disorder, a constant and the root marks:
`-(H(σ¹) + H(σ²)) + (λ ∑ᵢ σ¹ᵢσ²ᵢ - ∑_ℓ ∑_i σ^ℓ_i a(i,ℓ))
  + ∑_s (-(∑_ℓ σ^ℓ_{s.1} (K₀)_{ℓ s.2})) z₀(s)`. -/
lemma pairBranchA_eq (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (σ : Fin 2 → Config N) :
    pairBranchA N H lam a K₀ z₀ σ
      = -(H (σ 0) + H (σ 1))
        + (lam * ∑ i, isingSpin (σ 0 i) * isingSpin (σ 1 i)
          - ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * a (i, l))
        + ∑ s : Fin N × J, (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * z₀ s := by
  unfold pairBranchA
  have e := sum_sum_mul_sum_eq (fun l i => isingSpin (σ l i)) K₀ z₀
  simp only [neg_mul, Finset.sum_neg_distrib, ← e, mul_add, Finset.sum_add_distrib]
  ring

/-- `-H(σ)` is affine in the marks along the branch. -/
lemma neg_pairBranchHamX_eq (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    (x : Fin k → Fin N × J → ℝ) (σ : Fin 2 → Config N) :
    -pairBranchHamX N k H lam a K₀ K z₀ x σ
      = pairBranchA N H lam a K₀ z₀ σ + ∑ p, ∑ s, pairBranchB N k K σ p s * x p s := by
  unfold pairBranchHamX pairBranchA pairBranchB pairBranchMark
  have e := sum_sum_mul_sum_sum_eq (fun l i => isingSpin (σ l i)) K x
  simp only [neg_mul, Finset.sum_neg_distrib, ← e, mul_add, Finset.sum_add_distrib]
  ring

lemma pairHamG_eq_sum {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (H : EnergySpace N)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a K₀ K z₀ x
      = ∑ σ : Fin 2 → Config N, ENNReal.ofReal (c σ) * ENNReal.ofReal (Real.exp
          (pairBranchA N H lam a K₀ z₀ σ + ∑ p, ∑ s, pairBranchB N k K σ p s * x p s)) := by
  unfold pairHamG pairBranchZX
  rw [ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg (hc0 σ) (Real.exp_pos _).le]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ENNReal.ofReal_mul (hc0 σ), neg_pairBranchHamX_eq]

lemma lintegral_pairHamG_ne_top (vs : Fin k → ℝ≥0) {c : (Fin 2 → Config N) → ℝ}
    (hc0 : ∀ σ, 0 ≤ c σ) (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    ∫⁻ x, pairHamG N k c H lam a K₀ K z₀ x ∂Measure.pi (siteGaussianMarks (Fin N × J) k vs)
      ≠ ∞ := by
  simp_rw [pairHamG_eq_sum N k hc0]
  exact lintegral_sum_ofReal_mul_ofReal_exp_siteGaussianMarks (Fin N × J) k vs c _ _

/-- The recursion is finite for the constrained branch partition function (Talagrand's (14.4)). -/
lemma cascadeRec_pairHamG_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (H : EnergySpace N)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) :
    cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs) (pairHamG N k c H lam a K₀ K z₀) ≠ ∞ :=
  ne_top_of_le_ne_top (lintegral_pairHamG_ne_top N k vs hc0 H lam a K₀ K z₀)
    (cascadeRec_le_lintegral_pi k ms _ (measurable_pairHamG' N k c H lam a K₀ K z₀) hpos hle)

/-! ### The endpoint `H = 0` without constraint: (14.142)–(14.144) -/

omit N k in
/-- `ch a ch b ch λ + sh a sh b sh λ = (e^λ ch(a+b) + e^{-λ} ch(a-b)) / 2 > 0`. -/
lemma cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos (a b lam : ℝ) :
    0 < Real.cosh a * Real.cosh b * Real.cosh lam + Real.sinh a * Real.sinh b * Real.sinh lam := by
  have h : Real.cosh a * Real.cosh b * Real.cosh lam + Real.sinh a * Real.sinh b * Real.sinh lam
      = (Real.exp lam * Real.cosh (a + b) + Real.exp (-lam) * Real.cosh (a - b)) / 2 := by
    rw [Real.cosh_add, Real.cosh_sub, Real.cosh_eq lam, Real.sinh_eq lam]
    ring
  rw [h]
  have h1 := Real.cosh_pos (a + b)
  have h2 := Real.cosh_pos (a - b)
  have h3 := Real.exp_pos lam
  have h4 := Real.exp_pos (-lam)
  positivity

/-- **(14.142) summed over the sites**: at `H = 0` and without constraint, the branch partition
function is `∏ᵢ 4 (ch A_i ch B_i ch λ + sh A_i sh B_i sh λ)`, `A_i = a(i,1) + y¹_i`,
`B_i = a(i,2) + y²_i`. -/
theorem pairBranchZX_one_zero (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairBranchZX N k (fun _ => 1) 0 lam a K₀ K z₀ x
      = ∏ i, 4 * (Real.cosh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
          * Real.cosh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.cosh lam
        + Real.sinh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
          * Real.sinh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.sinh lam) := by
  have h := sum_pairConfig_exp N (fun i => -(a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i))
    (fun i => -(a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i)) lam
  simp only [Real.cosh_neg, Real.sinh_neg, neg_mul_neg] at h
  rw [← h]
  unfold pairBranchZX pairBranchHamX
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [one_mul]
  congr 1
  simp only [PiLp.zero_apply, Fin.sum_univ_two, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

/-- The site sum `Y_{κ+1}` of Talagrand's (14.144), summed over the sites:
`∑ᵢ log (ch A_i ch B_i ch λ + sh A_i sh B_i sh λ)`. -/
def pairCoshF (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) : ℝ :=
  ∑ i, Real.log (Real.cosh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
      * Real.cosh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.cosh lam
    + Real.sinh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
      * Real.sinh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.sinh lam)

lemma exp_pairCoshF (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    Real.exp (pairCoshF N k lam a K₀ K z₀ x)
      = ∏ i, (Real.cosh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
          * Real.cosh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.cosh lam
        + Real.sinh (a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i)
          * Real.sinh (a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i) * Real.sinh lam) := by
  rw [pairCoshF, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ =>
    Real.exp_log (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _)

/-- `∑_σ e^{-H(σ)} = exp (N log 4 + Y_{κ+1})` at `H = 0` without constraint. -/
theorem pairBranchZX_one_zero_eq_exp (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairBranchZX N k (fun _ => 1) 0 lam a K₀ K z₀ x
      = Real.exp ((N : ℝ) * Real.log 4 + pairCoshF N k lam a K₀ K z₀ x) := by
  rw [pairBranchZX_one_zero, Real.exp_add, exp_pairCoshF, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 4)]

lemma continuous_pairCoshF (lam : ℝ) (a : Fin N × Fin 2 → ℝ) :
    Continuous fun q : PairBranchParam N k J =>
      pairCoshF N k lam a q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  unfold pairCoshF
  refine continuous_finsetSum _ fun i _ => Continuous.log ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  have h0 : Continuous fun q : PairBranchParam N k J =>
      a (i, 0) + pairBranchMark N k q.1.2.1 q.1.2.2 q.2.1 q.2.2 0 i :=
    continuous_const.add (continuous_pairBranchMark N k (J := J) 0 i)
  have h1 : Continuous fun q : PairBranchParam N k J =>
      a (i, 1) + pairBranchMark N k q.1.2.1 q.1.2.2 q.2.1 q.2.2 1 i :=
    continuous_const.add (continuous_pairBranchMark N k (J := J) 1 i)
  exact (((Real.continuous_cosh.comp h0).mul (Real.continuous_cosh.comp h1)).mul
    continuous_const).add (((Real.continuous_sinh.comp h0).mul
      (Real.continuous_sinh.comp h1)).mul continuous_const)

lemma continuous_pairCoshF' (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    Continuous (pairCoshF N k lam a K₀ K z₀) := by
  unfold pairCoshF
  refine continuous_finsetSum _ fun i _ => Continuous.log ?_ fun x =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  have h0 : Continuous fun x : Fin k → Fin N × J → ℝ =>
      a (i, 0) + pairBranchMark N k K₀ K z₀ x 0 i := by
    unfold pairBranchMark
    fun_prop
  have h1 : Continuous fun x : Fin k → Fin N × J → ℝ =>
      a (i, 1) + pairBranchMark N k K₀ K z₀ x 1 i := by
    unfold pairBranchMark
    fun_prop
  exact (((Real.continuous_cosh.comp h0).mul (Real.continuous_cosh.comp h1)).mul
    continuous_const).add (((Real.continuous_sinh.comp h0).mul
      (Real.continuous_sinh.comp h1)).mul continuous_const)

lemma measurable_pairCoshF' (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    Measurable (pairCoshF N k lam a K₀ K z₀) :=
  (continuous_pairCoshF' N k lam a K₀ K z₀).measurable

/-- `exp Y_{κ+1}` in `ℝ≥0∞`: the branch weight at the endpoint. -/
lemma ofReal_exp_pairCoshF (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    ENNReal.ofReal (Real.exp (pairCoshF N k lam a K₀ K z₀ x))
      = ENNReal.ofReal (Real.exp (-((N : ℝ) * Real.log 4)))
        * pairHamG N k (fun _ => 1) 0 lam a K₀ K z₀ x := by
  rw [pairHamG, pairBranchZX_one_zero_eq_exp, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring

/-- The recursion is finite for `exp Y_{κ+1}` (Talagrand's (14.4) for (14.144)). -/
lemma cascadeRec_ofReal_exp_pairCoshF_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
      (fun x => ENNReal.ofReal (Real.exp (pairCoshF N k lam a K₀ K z₀ x))) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (cascadeRec_le_lintegral_pi k ms _
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_pairCoshF' N k lam a K₀ K z₀))) hpos hle)
  simp_rw [ofReal_exp_pairCoshF]
  rw [lintegral_const_mul _ (measurable_pairHamG' N k (fun _ => 1) 0 lam a K₀ K z₀)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) 0 lam a K₀ K z₀)

end

end SpinGlass
