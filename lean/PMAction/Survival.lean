import PMFramework.Gibbs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-! The finite Gibbs survival model (weights, normalization, ordering, and concentration as the
tolerance grows) is framework mathematics and lives in `PMFramework.Gibbs`. This module keeps
the Paper II limitations stated alongside it. -/
noncomputable section
namespace PMAction
open Finset

/-- Stationarity by itself does not select a minimum. -/
theorem stationary_not_minimal :
    let p : Polynomial ℝ := -Polynomial.X^2
    p.derivative.eval 0 = 0 ∧ p.eval 1 < p.eval 0 := by
  norm_num

/-- A dissipation budget constrains a product without determining each factor. -/
theorem complexity_speed_bound {ξ K f C : ℝ} (hξ : 0 < ξ) (hK : 0 < K)
    (hbudget : ξ * K * f ≤ C) : f ≤ C / (ξ*K) := by
  apply (le_div_iff₀ (mul_pos hξ hK)).mpr
  nlinarith

/-- A positive dissipation density cannot be identified with an unrestricted
Lorentzian quadratic form by algebra alone. -/
theorem lorentzian_cost_not_nonnegative :
    ¬ ∀ t x : ℝ, 0 ≤ -t^2+x^2 := by
  intro h
  have := h 1 0
  norm_num at this

end PMAction
