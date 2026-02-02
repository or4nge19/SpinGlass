/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Completion results (vendored)

This file is vendored from mathlib4 PR #26291 (Cameron–Martin theorem), to avoid depending on
an unmerged Mathlib PR while keeping our Lean toolchain pinned.

Placed in `Common/` so both `SpinGlass/` and `GibbsMeasure/` can depend on it without creating
cross-library dependencies.
-/

@[expose] public section

open NormedSpace UniformSpace
open scoped InnerProductSpace

-- `ContinuousConstSMul` does not always get inferred automatically for submodules;
-- we register the subtype instance we need for this vendored development.
instance instContinuousConstSMul_submodule {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousConstSMul R M] (s : Submodule R M) :
    ContinuousConstSMul R s := by
  classical
  refine ⟨fun c => ?_⟩
  -- continuity follows by composing the ambient `c • ·` with the subtype coercion
  simpa using
    ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk fun x : s => s.smul_mem c x.2

lemma InnerProductSpace.norm_le_dual_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ y : E, ⟪x, y⟫_ℝ ≤ M * ‖y‖) :
    ‖x‖ ≤ M := by
  refine NormedSpace.norm_le_dual_bound ℝ _ hMp fun f ↦ ?_
  let y := (InnerProductSpace.toDual ℝ E).symm f
  obtain hy : f x = ⟪x, y⟫_ℝ := by
    unfold y
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [hy]
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · specialize hM (-y)
    simp only [inner_neg_right, norm_neg] at hM
    rw [← neg_le]
    convert hM
    simp [y]
  · convert hM y
    simp [y]

lemma norm_eval_le_norm_mul_ciSup {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [Module ℝ G] [NormSMulClass ℝ G]
    (f : StrongDual ℝ E →ₗ[ℝ] G) {y : E} (hy : ∃ M, ∀ L, ‖f L‖ ≤ 1 → L y ≤ M) (L : StrongDual ℝ E) :
    ‖L y‖ ≤ ‖f L‖ * ⨆ (L') (_ : ‖f L'‖ ≤ 1), L' y := by
  have h_bdd : BddAbove (Set.range fun L' ↦ ⨆ (_ : ‖f L'‖ ≤ 1), L' y) := by
    obtain ⟨M, hM⟩ := hy
    refine ⟨M, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro L
    by_cases hL : ‖f L‖ ≤ 1
    · simpa [hL] using hM L hL
    · simp only [hL, Real.iSup_of_isEmpty]
      simpa using hM 0 (by simp)
  have h L (hL : ‖f L‖ = 1) : ‖L y‖ ≤ ‖f L‖ * ⨆ L', ⨆ (_ : ‖f L'‖ ≤ 1), L' y := by
    rw [hL, one_mul]
    rcases le_total 0 (L y) with hLy | hLy
    · exact le_ciSup_of_le h_bdd L (by simp [hL, abs_of_nonneg hLy])
    · exact le_ciSup_of_le h_bdd (-L) (by simp [hL, abs_of_nonpos hLy])
  have hL_zero_of_L2 (hL : f L = 0) : L y = 0 := by
    have h_smul (r : ℝ) : f (r • L) = 0 := by simp [hL]
    contrapose! hy with hL_zero
    refine fun M ↦ ⟨((M + 1) / L y) • L, by simp [h_smul], ?_⟩
    simp [div_mul_cancel₀ _ hL_zero]
  by_cases hL_zero : L y = 0
  · simp only [hL_zero, norm_zero]
    refine mul_nonneg (by positivity) ?_
    exact le_ciSup_of_le h_bdd 0 (by simp)
  specialize h (‖f L‖⁻¹ • L) ?_
  · simp only [map_smul, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀]
    simp only [ne_eq, norm_eq_zero]
    contrapose! hL_zero
    exact hL_zero_of_L2 hL_zero
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    norm_norm, map_smul, norm_smul] at h
  rwa [mul_assoc, mul_le_mul_iff_of_pos_left] at h
  simp only [inv_pos, norm_pos_iff, ne_eq]
  contrapose! hL_zero
  exact hL_zero_of_L2 hL_zero

/-- Coercion from a submodule to its topological closure. -/
def coeClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s → s.topologicalClosure := fun x =>
  ⟨x.1, (Submodule.le_topologicalClosure s) x.2⟩

-- This coercion existed upstream; we reintroduce it for the vendored development.
instance coeTC_submodule_topologicalClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) : CoeTC s s.topologicalClosure :=
  ⟨coeClosure s⟩

@[simp] lemma coeClosure_apply {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) (x : s) :
    (coeClosure s x : M) = x := rfl

@[simp] lemma coeClosure_add {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) (x y : s) :
    coeClosure s (x + y) = coeClosure s x + coeClosure s y := by
  ext
  rfl

@[simp] lemma coeClosure_smul {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) (c : R) (x : s) :
    coeClosure s (c • x) = c • coeClosure s x := by
  ext
  rfl

/-- Coercion from a submodule to its topological closure as a continuous linear map. -/
def coeClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s →L[R] s.topologicalClosure where
  toFun := coeClosure s
  map_add' := coeClosure_add s
  map_smul' := coeClosure_smul s
  cont := by
    -- continuity is inherited from the subtype map into `M`
    simpa [coeClosure] using
      (continuous_subtype_val.subtype_mk fun x : s => (Submodule.le_topologicalClosure s) x.2)

lemma IsUniformInducing_coeClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [UniformSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    IsUniformInducing (coeClosureCLM s) := by
  classical
  refine ⟨?_⟩
  let v : (s.topologicalClosure × s.topologicalClosure) → (M × M) := fun x ↦ (x.1, x.2)
  let u : (s × s) → (M × M) := fun x ↦ (x.1, x.2)
  let p : (s × s) → (s.topologicalClosure × s.topologicalClosure) :=
    fun x ↦ (coeClosure s x.1, coeClosure s x.2)
  have hp : v ∘ p = u := by
    funext x
    simp [v, u, p, Function.comp, coeClosure]
  calc
    Filter.comap (fun x : s × s ↦ (coeClosureCLM s x.1, coeClosureCLM s x.2)) (uniformity s.topologicalClosure)
        = Filter.comap (v ∘ fun x : s × s ↦ (coeClosure s x.1, coeClosure s x.2)) (uniformity M) := by
            simp [uniformity_subtype, Filter.comap_comap, v, coeClosureCLM, coeClosure]
    _ = Filter.comap u (uniformity M) := by
          simp [p, hp]
    _ = uniformity s := by
          simp [uniformity_subtype, u]

lemma denseRange_coeClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) :
    DenseRange (coeClosureCLM s) := by
  intro y
  refine mem_closure_iff.2 ?_
  intro U hU hyU
  rcases hU with ⟨V, hV, rfl⟩
  have hy_cl : (y : M) ∈ closure (s : Set M) := by
    simp
  rcases (mem_closure_iff.1 hy_cl) V hV hyU with ⟨z, hzV, hzs⟩
  refine ⟨coeClosureCLM s ⟨z, hzs⟩, ?_⟩
  refine ⟨hzV, ?_⟩
  refine ⟨⟨z, hzs⟩, rfl⟩

/-- Functional extensionality on a topological closure of a submodule, by density. -/
theorem funext_topologicalClosure {M R F : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    [TopologicalSpace F] [T2Space F]
    {s : Submodule R M} {f g : s.topologicalClosure → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : s, f (coeClosureCLM s x) = g (coeClosureCLM s x)) :
    f = g := by
  funext y
  have hy : f y = g y :=
    DenseRange.induction_on (e := coeClosureCLM s) (denseRange_coeClosureCLM s)
      (p := fun y => f y = g y) y
      (isClosed_eq hf hg) (fun x => h x)
  exact hy

/-- Induction principle on a topological closure of a submodule, by density. -/
@[elab_as_elim]
theorem induction_topologicalClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    {s : Submodule R M} {p : s.topologicalClosure → Prop} (y : s.topologicalClosure)
    (hp : IsClosed {y | p y}) (ih : ∀ x : s, p (coeClosureCLM s x)) : p y :=
  DenseRange.induction_on (e := coeClosureCLM s) (denseRange_coeClosureCLM s) y hp ih

section Extension

variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
  [UniformContinuousConstSMul R M] [ContinuousConstSMul R M]
  [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
  [IsUniformAddGroup F] [UniformContinuousConstSMul R F] [ContinuousConstSMul R F]
  {s : Submodule R M}

/-- Extension of a linear map `s →L[R] F` on a submodule to a linear map on the topological
closure of the submodule. -/
noncomputable
def closureExtensionCLM (s : Submodule R M) (f : s →L[R] F) : s.topologicalClosure →L[R] F :=
  ContinuousLinearMap.extend f (coeClosureCLM s)

omit [UniformContinuousConstSMul R M] [UniformContinuousConstSMul R F] in
@[simp]
lemma closureExtensionCLM_coe (s : Submodule R M) (f : s →L[R] F) (x : s) :
    closureExtensionCLM s f x = f x :=
  ContinuousLinearMap.extend_eq f (denseRange_coeClosureCLM s) (IsUniformInducing_coeClosureCLM s) _

end Extension
