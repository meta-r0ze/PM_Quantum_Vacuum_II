import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field

/-!
# Exchange of a massive mediator becomes a contact interaction

A charged-current amplitude exchanges a vector of mass `m` between two currents with coupling
`g/(2√2)` each. Its coefficient at momentum transfer `q²` is `(g/(2√2))²/(m² - q²)`.

* `contact_limit`: as `q² → 0` the coefficient tends to `g²/(8m²)`, the contact (four-fermion)
  coefficient; `at_zero` gives the value.
* `fermi_from_mass`: defining the Fermi constant by `G_F/√2 = g²/(8m²)`, a mediator with
  `m² = g²v²/4` gives `G_F = 1/(√2 v²)` for every `g ≠ 0`. The coupling cancels: the Fermi constant
  measures only the scale `v`.

The mass relation `m² = g²v²/4` is not assumed here; Paper III derives it from the reference
(`PMNested.ReferenceMasses.charged_entry`). Paper V's `MassScaling.mediator_matching` is the same
identity.
-/

noncomputable section
namespace PMAction.ContactMatching
open Filter Topology

def coeff (g m q2 : ℝ) : ℝ := (g / (2 * Real.sqrt 2)) ^ 2 / (m ^ 2 - q2)

theorem at_zero (g m : ℝ) (hm : m ≠ 0) : coeff g m 0 = g ^ 2 / (8 * m ^ 2) := by
  unfold coeff
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sub_zero]
  field_simp; ring

theorem contact_limit (g m : ℝ) (hm : m ≠ 0) :
    Tendsto (coeff g m) (𝓝 0) (𝓝 (g ^ 2 / (8 * m ^ 2))) := by
  rw [← at_zero g m hm]
  unfold coeff
  apply Tendsto.div tendsto_const_nhds (tendsto_const_nhds.sub tendsto_id)
  simp [pow_ne_zero 2 hm]

/-- **The Fermi constant from the mediator mass.** -/
theorem fermi_from_mass (g v m : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (hm : m ^ 2 = g ^ 2 * v ^ 2 / 4) :
    Real.sqrt 2 * (g ^ 2 / (8 * m ^ 2)) = 1 / (Real.sqrt 2 * v ^ 2) := by
  rw [hm]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [hs]

end PMAction.ContactMatching
