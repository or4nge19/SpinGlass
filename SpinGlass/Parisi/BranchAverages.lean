/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.BranchLimit
import Common.Mathlib.Probability.PointProcess.CascadeBranchLaw

/-!
# Branch Hamiltonians and the Gibbs pair average over branches

For a general address `α : Fin k → ℕ × ℕ` of the (untruncated) tree, the marks along `α`
(`branchMark`), the interpolating Hamiltonian `√t H_N(σ) + √(1−t) ∑ᵢ σᵢ z_{i,α} + h ∑ᵢ σᵢ` of
the branch (`branchHam`, which is `truncHam` on the truncated branches, `truncHam_apply`), and the
branch partition function `exp F_t(α) = ∑_σ exp(−H_t(σ, α))` (`branchZ`). Summing the weighted
Gibbs weights over the configurations, the pair average `⟨θ(q_{(α,γ)})⟩_t` on `Σ_N × A` is a
pair average over the branches alone with weights `u*_α exp F_t(α)`
(`sum_wGibbs_treeOverlap_eq`), which is Talagrand's reduction in the proof of (14.76).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-- The mark at site `i` along the address `α`: `z₀ᵢ + ∑ₚ z_{i,p,α}`. -/
def branchMark (z : MarksSpace N k) (α : Fin k → ℕ × ℕ) (i : Fin N) : ℝ :=
  z.1 i + ∑ p : Fin k, nodeMark k z.2 ⟨p, branchPrefix α p⟩ i

omit k in
lemma branchMark_truncBranchCoe {k M : ℕ} (z : MarksSpace N k) (α : TruncBranch k M) (i : Fin N) :
    branchMark N k z (truncBranchCoe k M α) i = treeMark N k M z α i := rfl

/-- The interpolating Hamiltonian of the branch `α`:
`√t H_N(σ) + √(1−t) ∑ᵢ σᵢ z_{i,α} + h ∑ᵢ σᵢ`. -/
def branchHam (t h : ℝ) (H : EnergySpace N) (z : MarksSpace N k) (α : Fin k → ℕ × ℕ)
    (σ : Config N) : ℝ :=
  Real.sqrt t * H σ + Real.sqrt (1 - t) * ∑ i, isingSpin (σ i) * branchMark N k z α i
    + h * ∑ i, isingSpin (σ i)

lemma truncHam_apply {M : ℕ} (t h : ℝ) (ω : EnergySpace N × MarksSpace N k)
    (x : Config N × TruncBranch k M) :
    truncHam N k M t h ω x = branchHam N k t h ω.1 ω.2 (truncBranchCoe k M x.2) x.1 := by
  unfold truncHam branchHam
  rw [PiLp.add_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, pullbackCLM_apply,
    pullbackCLM_apply, treeLin_treeCoords_apply, smul_eq_mul, smul_eq_mul]
  simp only [H_field, magnetic_field_vector, magnetization_eq_magnetizationOf, magnetizationOf,
    spinOf, branchMark_truncBranchCoe]

/-- The branch partition function `exp F_t(α) = ∑_σ exp(−H_t(σ, α))`. -/
def branchZ (t h : ℝ) (H : EnergySpace N) (z : MarksSpace N k) (α : Fin k → ℕ × ℕ) : ℝ :=
  ∑ σ : Config N, Real.exp (-branchHam N k t h H z α σ)

lemma branchZ_pos (t h : ℝ) (H : EnergySpace N) (z : MarksSpace N k) (α : Fin k → ℕ × ℕ) :
    0 < branchZ N k t h H z α :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The branch partition function is the partial partition function of `truncHam`. -/
lemma wCondZ_truncHam {M : ℕ} (t h : ℝ) (ω : EnergySpace N × MarksSpace N k)
    (α : TruncBranch k M) :
    wCondZ (fun _ : Config N => (1 : ℝ)) (truncHam N k M t h ω) α
      = branchZ N k t h ω.1 ω.2 (truncBranchCoe k M α) := by
  unfold wCondZ branchZ
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [one_mul, truncHam_apply]

/-- The weighted partition function on `Σ_N × A` is the weighted sum of the branch partition
functions. -/
lemma wZ_truncHam {M : ℕ} (u : TruncBranch k M → ℝ) (t h : ℝ) (ω : EnergySpace N × MarksSpace N k) :
    wZ (branchWt (N := N) u) (truncHam N k M t h ω)
      = ∑ α, u α * branchZ N k t h ω.1 ω.2 (truncBranchCoe k M α) := by
  rw [branchWt_eq]
  refine (wZ_prod_eq u (fun _ : Config N => (1 : ℝ)) (truncHam N k M t h ω)).trans ?_
  exact Finset.sum_congr rfl fun α _ => by rw [wCondZ_truncHam]

/-- **The Gibbs pair average of a function of the branches** reduces to a pair average over the
branches with the weights `u_α exp F_t(α)`: the case of `sum_wGibbs_prod_pair`. -/
theorem sum_wGibbs_pair_eq {M : ℕ} (u : TruncBranch k M → ℝ) (t h : ℝ)
    (ω : EnergySpace N × MarksSpace N k)
    (φ : TruncBranch k M → TruncBranch k M → ℝ) :
    (∑ x, ∑ y, wGibbs (branchWt (N := N) u) (truncHam N k M t h ω) x
        * wGibbs (branchWt (N := N) u) (truncHam N k M t h ω) y * φ x.2 y.2)
      = (∑ α, ∑ γ, u α * branchZ N k t h ω.1 ω.2 (truncBranchCoe k M α)
          * (u γ * branchZ N k t h ω.1 ω.2 (truncBranchCoe k M γ)) * φ α γ)
        / (∑ α, u α * branchZ N k t h ω.1 ω.2 (truncBranchCoe k M α)) ^ 2 := by
  rw [branchWt_eq]
  refine (sum_wGibbs_prod_pair u (fun _ : Config N => (1 : ℝ)) (truncHam N k M t h ω) φ).trans ?_
  simp_rw [wCondZ_truncHam]

/-! ### The marks along a branch, and the branch objects as functions of the marks -/

/-- The mark at site `i` along `α` is the root mark plus the marks of the nodes of `α`. -/
lemma branchMark_eq (z : MarksSpace N k) (α : Fin k → ℕ × ℕ) (i : Fin N) :
    branchMark N k z α i = z.1 i + ∑ p, branchMarks k z.2 α p i := by
  unfold branchMark
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [branchMarks_eq_nodeMark]

/-- Talagrand's Hamiltonian (14.77): the interpolating Hamiltonian as a function of the root marks
`z₀` and of the marks `x = (x₁, …, x_k)` along a branch. -/
def branchHamX (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ)
    (σ : Config N) : ℝ :=
  Real.sqrt t * H σ + Real.sqrt (1 - t) * ∑ i, isingSpin (σ i) * (z₀ i + ∑ p, x p i)
    + h * ∑ i, isingSpin (σ i)

lemma branchHam_eq (t h : ℝ) (H : EnergySpace N) (z : MarksSpace N k) (α : Fin k → ℕ × ℕ)
    (σ : Config N) :
    branchHam N k t h H z α σ = branchHamX N k t h H z.1 (branchMarks k z.2 α) σ := by
  unfold branchHam branchHamX
  simp_rw [branchMark_eq]

/-- Talagrand's `exp F(x₁, …, x_k) = ∑_σ exp (−H(σ, x₁, …, x_k))`, (14.78). -/
def branchZX (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : ℝ :=
  ∑ σ : Config N, Real.exp (-branchHamX N k t h H z₀ x σ)

lemma branchZ_eq (t h : ℝ) (H : EnergySpace N) (z : MarksSpace N k) (α : Fin k → ℕ × ℕ) :
    branchZ N k t h H z α = branchZX N k t h H z.1 (branchMarks k z.2 α) := by
  unfold branchZ branchZX
  simp_rw [branchHam_eq]

lemma branchZX_pos (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    0 < branchZX N k t h H z₀ x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Joint continuity of the branch partition function in `(t, H, z₀, x)`. -/
lemma continuous_branchZX (h : ℝ) :
    Continuous fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      branchZX N k q.1.1 h q.1.2.1 q.1.2.2 q.2 := by
  unfold branchZX branchHamX
  refine continuous_finsetSum _ fun σ _ => Real.continuous_exp.comp (Continuous.neg ?_)
  refine (((Real.continuous_sqrt.comp continuous_fst.fst).mul
    (((continuous_apply σ).comp (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).comp
      continuous_fst.snd.fst)).add
    ((Real.continuous_sqrt.comp (continuous_const.sub continuous_fst.fst)).mul
      (continuous_finsetSum _ fun i _ => continuous_const.mul
        (((continuous_apply i).comp continuous_fst.snd.snd).add
          (continuous_finsetSum _ fun p _ =>
            (continuous_apply i).comp ((continuous_apply p).comp continuous_snd)))))).add
    continuous_const

/-- Continuity of the branch partition function in the marks along the branch. -/
lemma continuous_branchZX' (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    Continuous (branchZX N k t h H z₀) := by
  unfold branchZX branchHamX
  refine continuous_finsetSum _ fun σ _ => Real.continuous_exp.comp (Continuous.neg ?_)
  refine (continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_const.add (continuous_finsetSum _ fun p _ =>
        (continuous_apply i).comp (continuous_apply p)))))).add continuous_const

/-- The branch partition function `exp F_t(x)`, in `ℝ≥0∞`, as a function of the marks along the
branch. -/
def hamG (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (branchZX N k t h H z₀ x)

lemma hamG_pos (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    0 < hamG N k t h H z₀ x :=
  ENNReal.ofReal_pos.2 (branchZX_pos N k t h H z₀ x)

lemma measurable_hamG (h : ℝ) :
    Measurable fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      hamG N k q.1.1 h q.1.2.1 q.1.2.2 q.2 := by
  unfold hamG
  exact (continuous_branchZX N k h).measurable.ennreal_ofReal

lemma measurable_hamG' (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    Measurable (hamG N k t h H z₀) := by
  unfold hamG
  exact (continuous_branchZX' N k t h H z₀).measurable.ennreal_ofReal

/-- `F_{k+1}` of Talagrand's (14.81): `∑ᵢ log (2 cosh (h + z_{i,0} + ∑ₚ x_{i,p}))`. -/
def coshF (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : ℝ :=
  ∑ i, Real.log (2 * Real.cosh (h + z₀ i + ∑ p, x p i))

/-- `exp F_{k+1} = ∏ᵢ 2 cosh (h + z_{i,0} + ∑ₚ x_{i,p})`, in `ℝ≥0∞`. -/
def coshG (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (coshF N k h z₀ x))

lemma exp_coshF (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    Real.exp (coshF N k h z₀ x) = ∏ i, (2 * Real.cosh (h + z₀ i + ∑ p, x p i)) := by
  rw [coshF, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => Real.exp_log (by positivity)

lemma coshG_eq (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    coshG N k h z₀ x = ENNReal.ofReal (∏ i, (2 * Real.cosh (h + z₀ i + ∑ p, x p i))) := by
  rw [coshG, exp_coshF]

lemma coshG_pos (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : 0 < coshG N k h z₀ x :=
  ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma continuous_coshF (h : ℝ) :
    Continuous fun q : (Fin N → ℝ) × (Fin k → Fin N → ℝ) => coshF N k h q.1 q.2 := by
  unfold coshF
  refine continuous_finsetSum _ fun i _ => Continuous.log ?_ fun q => by positivity
  exact continuous_const.mul (Real.continuous_cosh.comp ((continuous_const.add
    ((continuous_apply i).comp continuous_fst)).add (continuous_finsetSum _ fun p _ =>
      (continuous_apply i).comp ((continuous_apply p).comp continuous_snd))))

lemma continuous_coshF' (h : ℝ) (z₀ : Fin N → ℝ) : Continuous (coshF N k h z₀) := by
  unfold coshF
  refine continuous_finsetSum _ fun i _ => Continuous.log ?_ fun x => by positivity
  exact continuous_const.mul (Real.continuous_cosh.comp (continuous_const.add
    (continuous_finsetSum _ fun p _ => (continuous_apply i).comp (continuous_apply p))))

lemma measurable_coshF (h : ℝ) :
    Measurable fun q : (Fin N → ℝ) × (Fin k → Fin N → ℝ) => coshF N k h q.1 q.2 :=
  (continuous_coshF N k h).measurable

lemma measurable_coshF' (h : ℝ) (z₀ : Fin N → ℝ) : Measurable (coshF N k h z₀) :=
  (continuous_coshF' N k h z₀).measurable

lemma measurable_coshG (h : ℝ) :
    Measurable fun q : (Fin N → ℝ) × (Fin k → Fin N → ℝ) => coshG N k h q.1 q.2 := by
  unfold coshG
  exact (Real.continuous_exp.comp (continuous_coshF N k h)).measurable.ennreal_ofReal

lemma measurable_coshG' (h : ℝ) (z₀ : Fin N → ℝ) : Measurable (coshG N k h z₀) := by
  unfold coshG
  exact (Real.continuous_exp.comp (continuous_coshF' N k h z₀)).measurable.ennreal_ofReal

/-- The truncated marks product is `exp F_{k+1}` evaluated along the branch. -/
lemma ofReal_prod_two_cosh_treeMark {M : ℕ} (h : ℝ) (z : MarksSpace N k) (α : TruncBranch k M) :
    ENNReal.ofReal (∏ i, (2 * Real.cosh (h + treeMark N k M z α i)))
      = coshG N k h z.1 (branchMarks k z.2 (truncBranchCoe k M α)) := by
  rw [coshG_eq]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← branchMark_truncBranchCoe, branchMark_eq, add_assoc]

/-! ### Gaussian finiteness -/

/-- Exponential moments of affine forms of the marks are finite. -/
lemma lintegral_sum_ofReal_exp_gaussianMarks (vs : Fin k → ℝ≥0) (A : Config N → ℝ)
    (B : Config N → Fin k → Fin N → ℝ) :
    ∫⁻ x, ∑ σ : Config N, ENNReal.ofReal (Real.exp (A σ + ∑ p, ∑ i, B σ p i * x p i))
        ∂Measure.pi (gaussianMarks N k vs) ≠ ∞ := by
  have hm : ∀ σ : Config N, Measurable fun x : Fin k → Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (∑ p, ∑ i, B σ p i * x p i)) := fun σ =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Finset.measurable_sum _ fun p _ =>
      Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp (measurable_pi_apply p))))
  have hm' : ∀ σ : Config N, Measurable fun x : Fin k → Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (A σ + ∑ p, ∑ i, B σ p i * x p i)) := fun σ =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add
      (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp (measurable_pi_apply p)))))
  rw [lintegral_finsetSum _ fun σ _ => hm' σ]
  refine ENNReal.sum_ne_top.2 fun σ _ => ?_
  simp_rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (hm σ)]
  unfold gaussianMarks
  rw [lintegral_ofReal_exp_sum_mul_pi_pi_gaussianReal]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

lemma branchZX_eq_sum (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    branchZX N k t h H z₀ x
      = ∑ σ : Config N, Real.exp (-(Real.sqrt t * H σ + Real.sqrt (1 - t)
          * ∑ i, isingSpin (σ i) * z₀ i + h * ∑ i, isingSpin (σ i))
          + ∑ p, ∑ i, (-(Real.sqrt (1 - t)) * isingSpin (σ i)) * x p i) := by
  unfold branchZX branchHamX
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∑ i, isingSpin (σ i) * (z₀ i + ∑ p, x p i)
      = ∑ i, isingSpin (σ i) * z₀ i + ∑ p, ∑ i, isingSpin (σ i) * x p i := by
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
  have e2 : ∑ p, ∑ i, (-(Real.sqrt (1 - t)) * isingSpin (σ i)) * x p i
      = -(Real.sqrt (1 - t) * ∑ p, ∑ i, isingSpin (σ i) * x p i) := by
    simp_rw [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, mul_assoc]
  rw [e1, e2]
  ring

lemma hamG_eq_sum (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    hamG N k t h H z₀ x
      = ∑ σ : Config N, ENNReal.ofReal (Real.exp (-(Real.sqrt t * H σ + Real.sqrt (1 - t)
          * ∑ i, isingSpin (σ i) * z₀ i + h * ∑ i, isingSpin (σ i))
          + ∑ p, ∑ i, (-(Real.sqrt (1 - t)) * isingSpin (σ i)) * x p i)) := by
  rw [hamG, branchZX_eq_sum, ENNReal.ofReal_sum_of_nonneg fun σ _ => (Real.exp_pos _).le]

lemma lintegral_hamG_ne_top (vs : Fin k → ℝ≥0) (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    ∫⁻ x, hamG N k t h H z₀ x ∂Measure.pi (gaussianMarks N k vs) ≠ ∞ := by
  simp_rw [hamG_eq_sum]
  exact lintegral_sum_ofReal_exp_gaussianMarks N k vs _ _

lemma coshG_eq_sum (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    coshG N k h z₀ x
      = ∑ σ : Config N, ENNReal.ofReal (Real.exp ((∑ i, (h + z₀ i) * isingSpin (σ i))
          + ∑ p, ∑ i, isingSpin (σ i) * x p i)) := by
  rw [coshG_eq, ← ENNReal.ofReal_sum_of_nonneg fun σ _ => (Real.exp_pos _).le]
  congr 1
  have h1 := sum_exp_sum_spin N fun i => h + z₀ i + ∑ p, x p i
  simp only [spin, spinOf, exp_add_exp_neg_eq_two_cosh] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∑ i, (h + z₀ i + ∑ p, x p i) * isingSpin (σ i)
      = ∑ i, (h + z₀ i) * isingSpin (σ i) + ∑ p, ∑ i, isingSpin (σ i) * x p i := by
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_comm]
  exact e1

lemma lintegral_coshG_ne_top (vs : Fin k → ℝ≥0) (h : ℝ) (z₀ : Fin N → ℝ) :
    ∫⁻ x, coshG N k h z₀ x ∂Measure.pi (gaussianMarks N k vs) ≠ ∞ := by
  simp_rw [coshG_eq_sum]
  exact lintegral_sum_ofReal_exp_gaussianMarks N k vs _ _

/-- The recursion is finite for the branch partition function (Talagrand's (14.4) for (14.78)). -/
lemma cascadeRec_hamG_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    cascadeRec k ms (gaussianMarks N k vs) (hamG N k t h H z₀) ≠ ∞ :=
  ne_top_of_le_ne_top (lintegral_hamG_ne_top N k vs t h H z₀)
    (cascadeRec_le_lintegral_pi k ms _ (measurable_hamG' N k t h H z₀) hpos hle)

/-- The recursion is finite for `exp F_{k+1}` (Talagrand's (14.4) for (14.81)). -/
lemma cascadeRec_coshG_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : ℝ) (z₀ : Fin N → ℝ) :
    cascadeRec k ms (gaussianMarks N k vs) (coshG N k h z₀) ≠ ∞ :=
  ne_top_of_le_ne_top (lintegral_coshG_ne_top N k vs h z₀)
    (cascadeRec_le_lintegral_pi k ms _ (measurable_coshG' N k h z₀) hpos hle)

end

end SpinGlass
