import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A topological matrix-exponential slope, isolated from the norm used for
unitary stability. All finite-dimensional matrix norm choices induce the
same topology; no equality between those norms is asserted. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.MatrixEvolutionSlope
open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.Operator
local instance {n : Type*} [Fintype n] : TopologicalSpace (Matrix n n ℂ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

theorem exponential_slope {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Tendsto (fun h : ℝ => h⁻¹ • (exp (h • A)-1)) (𝓝[≠] 0) (𝓝 A) := by
  have hd := hasDerivAt_exp_smul_const A (0 : ℝ)
  have h := hd.tendsto_slope_zero
  simpa only [zero_add, zero_smul, exp_zero, one_mul] using h

/-- The derivative stated only through its topological slope, at any time. -/
theorem exponential_slope_at {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (t : ℝ) :
    Tendsto (slope (fun h : ℝ => exp (h • A)) t) (𝓝[≠] t) (𝓝 (exp (t • A)*A)) :=
  (hasDerivAt_exp_smul_const A t).tendsto_slope

end PMAction.MatrixEvolutionSlope
