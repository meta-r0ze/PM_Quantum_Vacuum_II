import PMAction.TwinTests

/-!
# Speed of the light species in the twin-free walk

With `μ = 0` (`a = −r`, `b = r`) the trace formula gives `tr W = 2(cos² r · cos k + sin² r)`.
A quasi-energy `ω` with `2 cos ω = tr W` therefore satisfies

  `1 − cos ω = cos² r · (1 − cos k)`   (`massless_dispersion`),

so near `k = 0` the light species moves at speed `|cos r|` (`speed_sq`). It equals the
substrate's unit speed only if `sin r = 0`, and then the twin at `k = π` returns to the
gapless quasi-energy `π` (`unit_speed_ungaps_twin`). Within this family, twin gapping and a fermion moving at
the link speed are incompatible unless every field's update shares the reduced speed
`|cos r|`. (Other local families, with momentum-dependent mixing, move faster than one; a
unit-speed, twin-free update is possible only by tuning between them. That is a constraint
to be met, not yet derived.)
-/

noncomputable section
namespace PMAction.WalkSpeed
open PMAction.TwinTests

theorem massless_trace (r k : ℝ) :
    (Wp (-r) r k).trace = 2 * (Real.cos r ^ 2 * Real.cos k + Real.sin r ^ 2) := by
  rw [Wp_trace, Real.cos_neg, Real.sin_neg]; push_cast; ring

theorem massless_dispersion {r k ω : ℝ}
    (h : (2 * Real.cos ω : ℂ) = (Wp (-r) r k).trace) :
    1 - Real.cos ω = Real.cos r ^ 2 * (1 - Real.cos k) := by
  rw [massless_trace] at h
  have h' : 2 * Real.cos ω = 2 * (Real.cos r ^ 2 * Real.cos k + Real.sin r ^ 2) := by
    exact_mod_cast h
  have := Real.sin_sq_add_cos_sq r
  nlinarith

/-- Small-`k` limit: `(1 − cos ω)/(1 − cos k) = cos² r`, i.e. speed `|cos r|`. -/
theorem speed_sq {r k ω : ℝ} (hk : Real.cos k ≠ 1)
    (h : (2 * Real.cos ω : ℂ) = (Wp (-r) r k).trace) :
    (1 - Real.cos ω) / (1 - Real.cos k) = Real.cos r ^ 2 := by
  rw [massless_dispersion h]
  have : 1 - Real.cos k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  field_simp

/-- Unit speed (`cos² r = 1`) puts the twin back at the gapless quasi-energy `π`. -/
theorem unit_speed_ungaps_twin {r : ℝ} (h : Real.cos r ^ 2 = 1) :
    (Wp (0 - r) r Real.pi).trace = -2 := by
  rw [twin_point]
  have hs : Real.sin r ^ 2 = 0 := by have := Real.sin_sq_add_cos_sq r; linarith
  have h2 : Real.cos (2*r - 0) = 1 := by
    rw [sub_zero, Real.cos_two_mul]; linarith
  rw [h2]; push_cast; ring

end PMAction.WalkSpeed
