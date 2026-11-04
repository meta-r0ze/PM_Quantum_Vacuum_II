import PMAction.RegisterHamiltonian
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# From substrate conservation to the continuity equation

`RegisterHamiltonian.evolution_occupation` (and `evolution_payload`) show that a
homogeneous register cell's total occupation — and each payload bit — is
**conserved** by coherent substrate evolution. This module carries one conserved
comoving charge `N` through the coarse-graining to a density and derives the
continuity equation, so Paper VI's equation of state is a consequence of
conservation plus one per-particle scaling rather than a separate axiom.

The coarse-graining bridge is explicit: a conserved charge `N` spread over
comoving physical volume `a³` has density `homogeneousDensity N a = N / a³`.
Given that (and `a > 0`), the density automatically obeys the pressureless
continuity law.

* `homogeneousDensity_hasDerivAt`, `homogeneousDensity_deriv` — derivative `−3N/a⁴`.
* `matter_continuity` — `a·ρ' + 3·ρ = 0`: the matter continuity equation.
* `matter_w` — the equation-of-state value `w = 0`.
* `radiation_w` — for a conserved `ρ·a⁴`, `w = 1/3`.
* `vacuum_w` — for a constant density, `w = −1`.

These match Paper VI's `PMCosmology.Background.equation_of_state`,
`w = −1 − a ρ'/(3ρ)`. What remains a physical input is *which* per-particle
scaling holds (matter / radiation / vacuum) and the expansion `a` itself; the
continuity relation is no longer assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.Continuity

/-- Density of a conserved comoving charge `N` over physical volume `a³`. -/
def homogeneousDensity (N a : ℝ) : ℝ := N / a ^ 3

/-- `d/da (N/a³) = −3N/a⁴`. -/
theorem homogeneousDensity_hasDerivAt (N a : ℝ) (ha : a ≠ 0) :
    HasDerivAt (homogeneousDensity N) (-(3 * N) / a ^ 4) a := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * a ^ 2) a := by
    simpa using (hasDerivAt_pow (3 : ℕ) a : HasDerivAt (fun x : ℝ => x ^ 3) (3 * a ^ 2) a)
  have hinv : HasDerivAt (fun x : ℝ => (x ^ 3)⁻¹) (-(3 * a ^ 2) / (a ^ 3) ^ 2) a :=
    h3.inv (pow_ne_zero 3 ha)
  have hmul := hinv.const_mul N
  have hd : N * (-(3 * a ^ 2) / (a ^ 3) ^ 2) = -(3 * N) / a ^ 4 := by
    field_simp
  rw [hd] at hmul
  exact hmul

theorem homogeneousDensity_deriv (N a : ℝ) (ha : a ≠ 0) :
    deriv (homogeneousDensity N) a = -(3 * N) / a ^ 4 :=
  (homogeneousDensity_hasDerivAt N a ha).deriv

/-- **Matter continuity.** A conserved comoving charge gives `a·ρ' + 3·ρ = 0`. -/
theorem matter_continuity (N a : ℝ) (ha : a ≠ 0) :
    a * deriv (homogeneousDensity N) a + 3 * homogeneousDensity N a = 0 := by
  rw [homogeneousDensity_deriv N a ha]
  unfold homogeneousDensity
  field_simp
  ring

/-- **Matter equation of state.** For the conserved-charge density,
`w = −1 − a ρ'/(3ρ) = 0`. -/
theorem matter_w (N a : ℝ) (hN : N ≠ 0) (ha : a ≠ 0) :
    -1 - a * deriv (homogeneousDensity N) a / (3 * homogeneousDensity N a) = 0 := by
  rw [homogeneousDensity_deriv N a ha]
  unfold homogeneousDensity
  field_simp
  ring

/-- Radiation-like density `N/a⁴` (e.g. conserved number with energy redshifting
as `1/a`). -/
def radiationDensity (N a : ℝ) : ℝ := N / a ^ 4

theorem radiationDensity_hasDerivAt (N a : ℝ) (ha : a ≠ 0) :
    HasDerivAt (radiationDensity N) (-(4 * N) / a ^ 5) a := by
  have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * a ^ 3) a := by
    simpa using (hasDerivAt_pow (4 : ℕ) a : HasDerivAt (fun x : ℝ => x ^ 4) (4 * a ^ 3) a)
  have hinv : HasDerivAt (fun x : ℝ => (x ^ 4)⁻¹) (-(4 * a ^ 3) / (a ^ 4) ^ 2) a :=
    h4.inv (pow_ne_zero 4 ha)
  have hmul := hinv.const_mul N
  have hd : N * (-(4 * a ^ 3) / (a ^ 4) ^ 2) = -(4 * N) / a ^ 5 := by
    field_simp
  rw [hd] at hmul
  exact hmul

/-- **Radiation equation of state**: for `ρ ∝ a⁻⁴`, `w = 1/3`. -/
theorem radiation_w (N a : ℝ) (hN : N ≠ 0) (ha : a ≠ 0) :
    -1 - a * deriv (radiationDensity N) a / (3 * radiationDensity N a) = 1 / 3 := by
  have hd : deriv (radiationDensity N) a = -(4 * N) / a ^ 5 :=
    (radiationDensity_hasDerivAt N a ha).deriv
  rw [hd]
  unfold radiationDensity
  field_simp
  ring

/-- **Vacuum equation of state**: a constant density gives `w = −1`. -/
theorem vacuum_w (Λ a : ℝ) :
    -1 - a * deriv (fun _ : ℝ => Λ) a / (3 * Λ) = -1 := by
  simp

end PMAction.Continuity
