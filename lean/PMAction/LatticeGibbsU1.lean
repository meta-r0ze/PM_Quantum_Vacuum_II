import PMAction.LatticeGibbs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A concrete lattice quantum measure for gauge group `U(1)`

Each of finitely many link variables is an angle `θ ∈ ℝ/ℤ` (`UnitAddCircle`), with Mathlib's
normalized Haar measure. The link matrix on a directed edge is the `1×1` unitary
`exp(2πi θ_{ℓ(y,v)})`, where `ℓ` assigns each edge its link variable.

* `link_unitary`: every link is unitary.
* `u1_gibbs`: for every finite region `X`, spacing `h` and `β ≥ 0`, PM's survival weight
  `exp(−β S)` with PM's D₄ action `S` (`LatticeGibbs.action`) normalizes the product Haar measure
  to a probability measure on link configurations.

This is a finite Gibbs probability measure for the supplied assignment. The
non-abelian `U(N)` case is `UnitaryHaar`. An arbitrary assignment `ℓ` can identify
distinct edges so that local gauge transformations leave the represented configuration
space. Configuration-space gauge closure and measure invariance are not asserted.
-/

noncomputable section
namespace PMAction.LatticeGibbsU1
open MeasureTheory Matrix

local notation "V4" => (Fin 4 → ℝ)

/-- The `1×1` unitary link for an angle. -/
def linkOf (θ : UnitAddCircle) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (AddCircle.toCircle θ : ℂ)

theorem link_unitary (θ : UnitAddCircle) : linkOf θ ∈ unitary (Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [Unitary.mem_iff]
  have h : (AddCircle.toCircle θ : ℂ) * (starRingEnd ℂ) (AddCircle.toCircle θ : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe]
    simp
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [linkOf, Matrix.mul_apply, Matrix.star_apply, mul_comm, h]

/-- The links of a configuration, given the edge-to-variable assignment `ℓ`. -/
def links {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (θ : Fin m → UnitAddCircle) :
    V4 → V4 → ℝ → Matrix (Fin 1) (Fin 1) ℂ := fun y v h => linkOf (θ (ℓ y v h))

/-- A finite `U(1)` Gibbs probability measure for a supplied edge assignment.
Local gauge closure of that assignment is not asserted. -/
theorem u1_gibbs {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (X : Finset V4) (h β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (LatticeGibbs.gibbs (volume : Measure (Fin m → UnitAddCircle)) β
      (fun θ => LatticeGibbs.action X (links ℓ θ) h)) := by
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by rw [AddCircle.measure_univ]; simp⟩
  have : IsProbabilityMeasure (volume : Measure (Fin m → UnitAddCircle)) := by
    rw [volume_pi]; infer_instance
  exact LatticeGibbs.gibbs_isProbability _ hβ _
    (fun θ => LatticeGibbs.action_bounds X (links ℓ θ) (fun y v h => link_unitary _) h)

end PMAction.LatticeGibbsU1
