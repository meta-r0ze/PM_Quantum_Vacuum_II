import Mathlib.Tactic

/-!
# Governor: the potential is forced to the Mexican hat

The Governor's potential is a function of the gauge-invariant occupancy `s = |φ|² ≥ 0`. At
operator dimension at most four it is `V(s) = a s + b s²` (normalized so `V(0) = 0`). Two PM
failure modes fix its shape:

* **No starvation**: the empty state is not the resting state; some occupancy `s > 0` costs less
  than `s = 0` (`Pillars.starvation` is the dynamical counterpart).
* **No runaway**: the cost is bounded below and attains its minimum at a nonzero occupancy
  (`Pillars.runaway`).

`governor_selects_hat`: these hold exactly when `a < 0 < b`, i.e. `V = −μ² s + λ s²` with
`μ², λ > 0`, minimized at `s = μ²/(2λ)`.
-/

namespace PMAction.Governor

/-- The potential at occupancy `s`. -/
def V (a b s : ℝ) : ℝ := a * s + b * s ^ 2

theorem governor_selects_hat (a b : ℝ) :
    ((∃ s, 0 < s ∧ V a b s < V a b 0) ∧ (∃ s₀, 0 < s₀ ∧ ∀ s, 0 ≤ s → V a b s₀ ≤ V a b s)) ↔
      a < 0 ∧ 0 < b := by
  constructor
  · rintro ⟨⟨s, hs, hlt⟩, ⟨s₀, hs₀, hmin⟩⟩
    simp only [V] at hlt hmin
    have h2 := hmin (2 * s₀) (by linarith)
    have h0 := hmin 0 le_rfl
    have hb : 0 < b := by
      rcases lt_trichotomy b 0 with hb | hb | hb
      · nlinarith [mul_pos hs₀ hs₀]
      · subst hb
        have ha : a * s₀ = 0 := by nlinarith
        have : a = 0 := by
          rcases mul_eq_zero.mp ha with h | h
          · exact h
          · linarith
        subst this; simp at hlt
      · exact hb
    refine ⟨?_, hb⟩
    nlinarith [mul_pos hb (mul_pos hs hs)]
  · rintro ⟨ha, hb⟩
    have hpos : 0 < -a / (2 * b) := div_pos (by linarith) (by linarith)
    have key : ∀ s, a * s + b * s ^ 2 - (a * (-a / (2 * b)) + b * (-a / (2 * b)) ^ 2) =
        b * (s + a / (2 * b)) ^ 2 := by intro s; field_simp; ring
    have hval : a * (-a / (2 * b)) + b * (-a / (2 * b)) ^ 2 = -(a ^ 2 / (4 * b)) := by
      field_simp; ring
    refine ⟨⟨-a / (2 * b), hpos, ?_⟩, ⟨-a / (2 * b), hpos, ?_⟩⟩
    · simp only [V]
      rw [hval]
      have : 0 < a ^ 2 / (4 * b) := div_pos (by nlinarith) (by linarith)
      simp; linarith
    · intro s _
      simp only [V]
      nlinarith [mul_nonneg hb.le (sq_nonneg (s + a / (2 * b))), key s]

end PMAction.Governor
