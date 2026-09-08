/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Continuous bilinear maps are determined by their values on bases

`LinearMap.ext_basis` states that two bilinear maps agreeing on all pairs of basis vectors are
equal. This file records the same statement for *continuous* bilinear maps
`E →L[𝕜] G →L[𝕜] F` between normed spaces, which Mathlib does not provide: it is the
extensionality principle behind "a Gaussian measure on a finite-dimensional space is determined by
its covariance matrix".
-/

namespace ContinuousLinearMap

variable {ι κ 𝕜 E G F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Two continuous bilinear maps agreeing on all pairs of basis vectors are equal.** The
continuous analogue of `LinearMap.ext_basis`. -/
theorem ext_basis₂ (b : Module.Basis ι 𝕜 E) (c : Module.Basis κ 𝕜 G)
    {B B' : E →L[𝕜] G →L[𝕜] F} (h : ∀ i j, B (b i) (c j) = B' (b i) (c j)) : B = B' := by
  have h1 : ∀ i, B (b i) = B' (b i) := fun i =>
    ContinuousLinearMap.ext fun y => LinearMap.congr_fun (c.ext fun j => h i j) y
  exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun (b.ext h1) x

/-- Two continuous bilinear maps are equal iff they agree on all pairs of basis vectors. -/
theorem ext_iff_basis₂ (b : Module.Basis ι 𝕜 E) (c : Module.Basis κ 𝕜 G)
    {B B' : E →L[𝕜] G →L[𝕜] F} :
    B = B' ↔ ∀ i j, B (b i) (c j) = B' (b i) (c j) :=
  ⟨fun h _ _ => h ▸ rfl, ext_basis₂ b c⟩

end ContinuousLinearMap
