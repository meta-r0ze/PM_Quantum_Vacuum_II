import Mathlib.Tactic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Operator dimensions and the dimension-four list

In four dimensions the action is dimensionless, so a Lagrangian term has mass dimension 4.

* `field_dimensions`: a first-order kinetic term (fermions; forced by `Dirac.dispersion_iff_clifford`)
  gives `[ψ] = 3/2`; a second-order one (scalars and the gauge field strength `F = ∂A`) gives
  `[φ] = [A] = 1`. Dimensions follow from the order of the kinetic term, not from a spatial
  footprint.
* `allowed_monomials`: a monomial with `a` scalars, `b` fermions (even, for a Lorentz scalar),
  `c` derivatives and `d` gauge fields has dimension `a + 3b/2 + c + d`. If this is at most 4,
  then `b ≤ 2`, at most one further factor accompanies a fermion bilinear, and at most four
  bosonic factors occur. Four-fermion contact terms and `φ⁶` are excluded.
* `higher_dimension_suppressed`: a term of dimension `4 + k`, `k ≥ 1`, carries a coefficient
  `c ℓᵏ` in units of the substrate spacing `ℓ`; it vanishes as `ℓ → 0`. Higher operators are
  suppressed by powers of the spacing, not forbidden outright.
-/

namespace PMAction.Operators

/-- **Field dimensions from kinetic order.** -/
theorem field_dimensions (ψ φ A : ℚ) (hψ : 2 * ψ + 1 = 4) (hφ : 2 * φ + 2 = 4)
    (hA : 2 * (A + 1) = 4) : ψ = 3 / 2 ∧ φ = 1 ∧ A = 1 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Twice the mass dimension of `φᵃ ψᵇ ∂ᶜ Aᵈ`. -/
def twiceDim (a b c d : ℕ) : ℕ := 2 * a + 3 * b + 2 * c + 2 * d

/-- **The dimension-four list.** -/
theorem allowed_monomials (a b c d : ℕ) (heven : Even b) (h : twiceDim a b c d ≤ 8) :
    b ≤ 2 ∧ (b = 2 → a + c + d ≤ 1) ∧ a + c + d ≤ 4 := by
  unfold twiceDim at h
  obtain ⟨k, rfl⟩ := heven
  refine ⟨by omega, fun h2 => by omega, by omega⟩

theorem four_fermion_excluded : 8 < twiceDim 0 4 0 0 := by decide
theorem phi_six_excluded : 8 < twiceDim 6 0 0 0 := by decide
theorem yukawa_allowed : twiceDim 1 2 0 0 = 8 := by decide
theorem phi_four_allowed : twiceDim 4 0 0 0 = 8 := by decide

/-- **Higher-dimension terms are suppressed by the spacing.** -/
theorem higher_dimension_suppressed (c : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun ℓ : ℝ => c * ℓ ^ k) (nhds 0) (nhds 0) := by
  have hcont : Continuous fun ℓ : ℝ => c * ℓ ^ k := by fun_prop
  have := hcont.tendsto 0
  simpa [zero_pow (by omega : k ≠ 0)] using this

end PMAction.Operators
