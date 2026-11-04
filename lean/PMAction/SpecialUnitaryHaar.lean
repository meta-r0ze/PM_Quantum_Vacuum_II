import PMAction.UnitaryHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `SU(N)` Haar measure and the special-unitary lattice measure

`UnitaryHaar` constructs the `U(N)` finite-volume Gibbs measure but leaves the
closed subgroup `SU(N)` (`det = 1`) to the same argument. This file supplies it.

* `sun`: `SU(N)` as the subgroup of `U(N)` with determinant one.
* `isCompact_sun`: `SU(N)` is compact (closed in compact `U(N)`).
* `haarSU`: normalized Haar measure on `SU(N)`; it is a probability measure and
  is both left and right invariant.
* `suN_gibbs`: PM's D₄ survival weight normalizes product Haar measure on `SU(N)`
  link configurations to a probability measure.

This closes the "`SU(N)` is not constructed" caveat of `YANG-MILLS-STATUS.md`.
It does not select `SU(N)` from the postulates; the gauge group remains an input.
-/

noncomputable section
namespace PMAction.SpecialUnitaryHaar
open MeasureTheory Matrix TopologicalSpace

variable (n : ℕ)

/-- `SU(n)` as the closed subgroup of `U(n)` with determinant one. -/
def sun : Subgroup (UnitaryHaar.UN n) where
  carrier := { U | (U : Matrix (Fin n) (Fin n) ℂ).det = 1 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Submonoid.coe_mul, Matrix.det_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [show (↑(a⁻¹) : Matrix (Fin n) (Fin n) ℂ) = (↑a)ᴴ from rfl,
      Matrix.det_conjTranspose, ha, star_one]

/-- The type `SU(n)`. -/
abbrev SUN := sun n

/-- `SU(n)` is compact, being closed in compact `U(n)`. -/
theorem isCompact_sun : IsCompact (sun n : Set (UnitaryHaar.UN n)) := by
  have hcont : Continuous (fun U : UnitaryHaar.UN n =>
      (U : Matrix (Fin n) (Fin n) ℂ).det) := by
    fun_prop
  have hclosed : IsClosed (sun n : Set (UnitaryHaar.UN n)) :=
    isClosed_eq hcont continuous_const
  exact hclosed.isCompact

instance : CompactSpace (SUN n) := isCompact_iff_compactSpace.mp (isCompact_sun n)

instance : MeasurableSpace (SUN n) := borel _
instance : BorelSpace (SUN n) := ⟨rfl⟩

/-- The normalized Haar measure on `SU(n)`. -/
def haarSU : Measure (SUN n) := Measure.haarMeasure ⊤

instance haarSU_probability : IsProbabilityMeasure (haarSU n) :=
  ⟨by simpa [haarSU] using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (SUN n)))⟩

instance : (haarSU n).IsMulLeftInvariant := by
  unfold haarSU; infer_instance

/-- Right invariance follows from uniqueness of normalized Haar, since right
translation preserves left invariance and probability. -/
instance haarSU_right : (haarSU n).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : IsProbabilityMeasure ((haarSU n).map (· * g)) := inferInstance
    have : (haarSU n).IsHaarMeasure := by
      unfold haarSU
      infer_instance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

local notation "V4" => (Fin 4 → ℝ)

/-- Links of an `SU(n)` configuration under an edge assignment. -/
def linksSU {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (U : Fin m → SUN n) :
    V4 → V4 → ℝ → Matrix (Fin n) (Fin n) ℂ :=
  fun y v h => ((U (ℓ y v h) : UnitaryHaar.UN n) : Matrix (Fin n) (Fin n) ℂ)

/-- The supplied finite edge assignment gives an `SU(n)` Gibbs probability measure.
As with `uN_gibbs`, the assignment is arbitrary, so this alone does not assert
closure under local gauge transformations. -/
theorem suN_gibbs {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (X : Finset V4) (h β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (LatticeGibbs.gibbs (Measure.pi fun _ : Fin m => haarSU n) β
      (fun U => LatticeGibbs.action X (linksSU n ℓ U) h)) := by
  refine LatticeGibbs.gibbs_isProbability _ hβ _
    (fun U => LatticeGibbs.action_bounds X (linksSU n ℓ U) ?_ h)
  intro y v h
  exact (U (ℓ y v h)).1.2

end PMAction.SpecialUnitaryHaar
