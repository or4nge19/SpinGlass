import Mathlib
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def myLin (L : E →L[ℝ] F) (c : F) (x : E) : F := L x + c

-- (a) does plain `exact` bridge delta+eta+Pi.add?
example (L : E →L[ℝ] F) (c : F) : ContDiff ℝ 1 (myLin L c) := by
  have hlin : ContDiff ℝ 1 (L : E → F) := L.contDiff.of_le le_top
  have hconst : ContDiff ℝ 1 (fun _ : E => c) := contDiff_const
  exact hlin.add hconst

-- (b) does `simpa [Pi.add_def]` work?
example (L : E →L[ℝ] F) (c : F) : ContDiff ℝ 1 (myLin L c) := by
  have hlin : ContDiff ℝ 1 (L : E → F) := L.contDiff.of_le le_top
  have hconst : ContDiff ℝ 1 (fun _ : E => c) := contDiff_const
  simpa [myLin, Pi.add_def] using hlin.add hconst

-- (c) the current failing style
example (L : E →L[ℝ] F) (c : F) : ContDiff ℝ 1 (myLin L c) := by
  have hlin : ContDiff ℝ 1 (L : E → F) := L.contDiff.of_le le_top
  have hconst : ContDiff ℝ 1 (fun _ : E => c) := contDiff_const
  simpa [myLin] using hlin.add hconst
