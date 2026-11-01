import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Distinct frequencies cannot persist on one complex ray

This is a continuous-time diagonal phase statement, independent of any
substrate, particle interpretation or reference choice. Clock-sampled
persistence can alias distinct frequencies and is not the conclusion proved here.
-/
noncomputable section
namespace PMAction.RayPersistence
open Complex

theorem beats (a b : ℂ) (ω₁ ω₂ : ℝ) (hω : ω₁ ≠ ω₂) :
    (∀ t : ℝ, ∃ c : ℂ, a * exp (-((ω₁ * t : ℝ) : ℂ) * I) = c * a ∧
        b * exp (-((ω₂ * t : ℝ) : ℂ) * I) = c * b) ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_contra hab
    push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hd : ω₁ - ω₂ ≠ 0 := sub_ne_zero.mpr hω
    obtain ⟨c, h1, h2⟩ := h (Real.pi / (ω₁ - ω₂))
    have e1 : exp (-((ω₁ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I) = c :=
      mul_left_cancel₀ ha (by rw [h1, mul_comm])
    have e2 : exp (-((ω₂ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I) = c :=
      mul_left_cancel₀ hb (by rw [h2, mul_comm])
    have hq : exp (-((ω₁ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I -
        -((ω₂ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I) = 1 := by
      rw [Complex.exp_sub, e1, e2, div_self]
      rintro rfl
      exact Complex.exp_ne_zero _ e1
    have harg : -((ω₁ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I -
        -((ω₂ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) * I = -(Real.pi * I) := by
      have : ω₁ * (Real.pi / (ω₁ - ω₂)) - ω₂ * (Real.pi / (ω₁ - ω₂)) = Real.pi := by
        field_simp
      have hc : ((ω₁ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) - ((ω₂ * (Real.pi / (ω₁ - ω₂)) : ℝ) : ℂ) =
          (Real.pi : ℂ) := by exact_mod_cast this
      linear_combination (-I) * hc
    rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I] at hq
    norm_num at hq
  · rintro (rfl | rfl) t
    · exact ⟨exp (-((ω₂ * t : ℝ) : ℂ) * I), by simp, by ring⟩
    · exact ⟨exp (-((ω₁ * t : ℝ) : ℂ) * I), by ring, by simp⟩

end PMAction.RayPersistence
