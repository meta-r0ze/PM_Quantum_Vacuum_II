import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Neutral-current normalization for a supplied charge representation

For real couplings with `g² + g'² > 0`, the orthogonal field rotation
`W₃ = c Z + s A`, `B = -s Z + c A` gives a photon coupling `e Q` and a
neutral coupling `r (T₃ - s² Q)`, where `r = sqrt (g² + g'²)`, `e = gg'/r`
and **`Q = T₃ + Yh`**. Here `Yh` denotes the hypercharge generator divided
by two, not the full hypercharge generator.

The result holds in any real module, including complex carrier matrices.
No charge representation, reference, current, mass scale or physical process
is selected here. `mass_combination` concerns the supplied quadratic form
proportional to `(g W₃ - g' B)²`; identifying that form with a substrate
reference is Paper III's separate representation-dependent construction.
-/

noncomputable section
namespace PMAction.NeutralCurrent

def radius (g gp : ℝ) : ℝ := Real.sqrt (g ^ 2 + gp ^ 2)
def cosine (g gp : ℝ) : ℝ := g / radius g gp
def sine (g gp : ℝ) : ℝ := gp / radius g gp
def electric (g gp : ℝ) : ℝ := g * gp / radius g gp
def weight (g gp : ℝ) : ℝ := gp ^ 2 / (g ^ 2 + gp ^ 2)

lemma radius_sq (g gp : ℝ) : radius g gp ^ 2 = g ^ 2 + gp ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma radius_pos {g gp : ℝ} (h : 0 < g ^ 2 + gp ^ 2) : 0 < radius g gp :=
  Real.sqrt_pos.2 h

/-- The field change preserves the two real field components' squared norm. -/
theorem rotation_norm (g gp Z A : ℝ) (h : 0 < g ^ 2 + gp ^ 2) :
    (cosine g gp * Z + sine g gp * A) ^ 2 +
      (-sine g gp * Z + cosine g gp * A) ^ 2 = Z ^ 2 + A ^ 2 := by
  have hr := ne_of_gt (radius_pos h)
  have hs := radius_sq g gp
  unfold cosine sine
  field_simp
  nlinarith [sq_nonneg (g * A - gp * Z)]

/-- The mixing weight is the squared sine, and lies in the probability interval. -/
theorem weight_properties (g gp : ℝ) (h : 0 < g ^ 2 + gp ^ 2) :
    weight g gp = sine g gp ^ 2 ∧ 0 ≤ weight g gp ∧ weight g gp ≤ 1 := by
  refine ⟨?_, by unfold weight; positivity, ?_⟩
  · simp only [weight, sine, div_pow, radius_sq]
  · exact (div_le_one h).2 (by nlinarith [sq_nonneg g])

/-- The photon drops out and the orthogonal component has coefficient `r`.
Squaring this identity diagonalizes any supplied multiple of this mass form. -/
theorem mass_combination (g gp Z A : ℝ) (h : 0 < g ^ 2 + gp ^ 2) :
    g * (cosine g gp * Z + sine g gp * A) -
      gp * (-sine g gp * Z + cosine g gp * A) = radius g gp * Z := by
  have hr := ne_of_gt (radius_pos h)
  have hs := radius_sq g gp
  unfold cosine sine
  field_simp
  linear_combination -Z * hs

/-- Current decomposition with the charge convention `Q = T₃ + Yh`.
This is an algebraic normalization, not a derivation of the representation. -/
theorem decomposition {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T3 Yh : V) (g gp Z A : ℝ) (h : 0 < g ^ 2 + gp ^ 2) :
    g • ((cosine g gp * Z + sine g gp * A) • T3) +
      gp • ((-sine g gp * Z + cosine g gp * A) • Yh) =
    electric g gp • (A • (T3 + Yh)) +
      radius g gp • (Z • (T3 - weight g gp • (T3 + Yh))) := by
  have hr := ne_of_gt (radius_pos h)
  have hs := radius_sq g gp
  have hd : g ^ 2 + gp ^ 2 ≠ 0 := ne_of_gt h
  have ht : g * cosine g gp = radius g gp * (1 - weight g gp) := by
    unfold cosine weight
    field_simp
    nlinarith [hs]
  have hy : gp * sine g gp = radius g gp * weight g gp := by
    unfold sine weight
    field_simp
    nlinarith [hs]
  have ha : g * sine g gp = electric g gp := by unfold sine electric; ring
  have hb : gp * cosine g gp = electric g gp := by unfold cosine electric; ring
  have htc : g * (cosine g gp * Z + sine g gp * A) =
      electric g gp * A + radius g gp * (Z * (1 - weight g gp)) := by
    linear_combination Z * ht + A * ha
  have hyc : gp * (-sine g gp * Z + cosine g gp * A) =
      electric g gp * A - radius g gp * (Z * weight g gp) := by
    linear_combination -Z * hy + A * hb
  simp only [smul_smul]
  rw [htc, hyc]
  module

end PMAction.NeutralCurrent
