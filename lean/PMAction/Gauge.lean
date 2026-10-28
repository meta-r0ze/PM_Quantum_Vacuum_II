import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace PMAction.Gauge

/-- Four independently transformed links telescope to conjugation at the base point. -/
theorem plaquette_covariant {G : Type*} [Group G] (a b c d u v w z : G) :
    (a*u*b⁻¹)*(b*v*c⁻¹)*(c*w*d⁻¹)*(d*z*a⁻¹) = a*(u*v*w*z)*a⁻¹ := by
  group

theorem gauge_invariant_score {G : Type*} [Group G] (score : G → ℝ)
    (hscore : ∀ a p, score (a*p*a⁻¹) = score p) (a b c d u v w z : G) :
    score ((a*u*b⁻¹)*(b*v*c⁻¹)*(c*w*d⁻¹)*(d*z*a⁻¹)) = score (u*v*w*z) := by
  rw [plaquette_covariant, hscore]

noncomputable def phaseCost (θ : ℝ) : ℝ := 1 - Real.cos θ

theorem phase_cost_bounds (θ : ℝ) : 0 ≤ phaseCost θ ∧ phaseCost θ ≤ 2 := by
  have := Real.cos_le_one θ
  have := Real.neg_one_le_cos θ
  constructor <;> dsimp [phaseCost] <;> linarith

/-- The exact U(1) Wilson cost is not an exactly quadratic function of curvature. -/
theorem wilson_not_exactly_quadratic :
    phaseCost (2*Real.pi) = 0 ∧ phaseCost (2*Real.pi) ≠ (2*Real.pi)^2/2 := by
  have hz : phaseCost (2*Real.pi) = 0 := by simp [phaseCost, Real.cos_two_pi]
  refine ⟨hz, ?_⟩
  rw [hz]
  have := Real.pi_pos
  nlinarith [sq_pos_of_pos (show 0 < 2*Real.pi by positivity)]

/-- D4 integer points forming a nearest-neighbor triangle: all squared lengths are 2.
This refutes the claimed prohibition of triangles in the D4 root lattice graph. -/
theorem d4_triangle_certificate :
    let a : Fin 4 → ℤ := ![1,-1,0,0]
    let b : Fin 4 → ℤ := ![1,0,-1,0]
    (2 ∣ ∑ i, a i) ∧ (2 ∣ ∑ i, b i) ∧
    (∑ i, (a i)^2) = 2 ∧ (∑ i, (b i)^2) = 2 ∧
    (∑ i, (a i-b i)^2) = 2 := by
  norm_num [Fin.sum_univ_succ]

/-- Link phase alone does not determine g until the field normalization is fixed. -/
theorem phase_normalization_freedom (g A c : ℝ) (hc : c ≠ 0) :
    phaseCost ((g/c)*(c*A)) = phaseCost (g*A) := by
  congr 1
  field_simp

end PMAction.Gauge
