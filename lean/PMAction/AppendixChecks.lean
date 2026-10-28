import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Arithmetic check of the Schwinger-limit appendix

The appendix writes `a_e = (4π/2π)·(g²/4π)` with `g²/4π = α`. That product is `2α`, not
`α/2π`; the two differ for every positive `α`.
-/

namespace PMAction.AppendixChecks

theorem stated_product (α : ℝ) : (4*Real.pi/(2*Real.pi)) * α = 2*α := by
  have := Real.pi_pos; field_simp; ring

theorem not_schwinger {α : ℝ} (hα : 0 < α) : (4*Real.pi/(2*Real.pi)) * α ≠ α/(2*Real.pi) := by
  rw [stated_product]
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  intro h
  have : 2*α*(2*Real.pi) = α := by field_simp at h; linarith
  nlinarith

end PMAction.AppendixChecks
