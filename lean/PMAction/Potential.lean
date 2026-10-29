import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section
namespace PMAction.Potential

/-- s denotes |φ|²; μ2 denotes the mass-squared parameter μ². -/
def value (μ2 lam s : ℝ) : ℝ := -μ2*s + lam*s^2

theorem complete_square {μ2 lam s : ℝ} (hlam : lam ≠ 0) :
    value μ2 lam s + μ2^2/(4*lam) = lam*(s-μ2/(2*lam))^2 := by
  unfold value
  field_simp
  ring

theorem global_lower_bound {μ2 lam s : ℝ} (hlam : 0 < lam) :
    -(μ2^2/(4*lam)) ≤ value μ2 lam s := by
  have h := complete_square (μ2 := μ2) (s := s) (ne_of_gt hlam)
  have := mul_nonneg (le_of_lt hlam) (sq_nonneg (s-μ2/(2*lam)))
  linarith

theorem minimum_iff {μ2 lam s : ℝ} (hlam : 0 < lam) :
    value μ2 lam s = -(μ2^2/(4*lam)) ↔ s = μ2/(2*lam) := by
  have h := complete_square (μ2 := μ2) (s := s) (ne_of_gt hlam)
  constructor
  · intro hs
    have hp : lam*(s-μ2/(2*lam))^2 = 0 := by
      rw [← h, hs]
      ring
    have hz : (s-μ2/(2*lam))^2 = 0 :=
      (mul_eq_zero.mp hp).resolve_left (ne_of_gt hlam)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hs
    rw [hs] at h ⊢
    simp only [sub_self] at h
    linarith

/-- With the convention |φ|² = v²/2, μ² = lam v² is the minimum condition. -/
theorem vev_convention (lam v : ℝ) (hlam : 0 < lam) :
    value (lam*v^2) lam (v^2/2) = -((lam*v^2)^2/(4*lam)) := by
  apply (minimum_iff hlam).mpr
  field_simp
 

/-- Four allowed amplitudes already distinguish a sixth-order interaction from
all potentials of the stipulated quadratic-plus-quartic form. -/
theorem finite_states_do_not_force_quartic :
    ¬ ∃ μ2 lam : ℝ, ∀ i : Fin 4, (i.val : ℝ)^6 = value μ2 lam ((i.val : ℝ)^2) := by
  rintro ⟨μ2, lam, h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [value] at h1 h2 h3
  linarith

end PMAction.Potential
