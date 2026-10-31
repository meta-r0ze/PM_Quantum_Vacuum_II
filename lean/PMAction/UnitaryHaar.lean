import PMAction.LatticeGibbs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Haar measure on `U(N)` and the non-abelian lattice measure

`LatticeGibbsU1` made the lattice measure concrete for `U(1)`. For a non-abelian group the
reference measure is product Haar measure, which this Mathlib does not supply as instances for the
unitary group. Here it is constructed.

* `isCompact_unitary`: the unitary matrices form a compact set (closed, and inside the product of
  unit balls since unitary entries are bounded by `1`).
* `haar`: the normalized Haar measure on `U(N)`; `haar_probability`; it is left invariant.
* `uN_gibbs`: for any finite set of link variables, edge assignment, finite region `X`, spacing `h`
  and `β ≥ 0`, PM's survival weight with PM's D₄ action normalizes product Haar measure to a
  probability measure on `U(N)` link configurations.

This constructs a finite Gibbs probability measure for the supplied assignment. The
assignment `ℓ` is arbitrary: identifying distinct edges can make its configuration
space fail to be closed under local gauge transformations. Thus this theorem alone
does not construct a locally gauge-invariant lattice model. `D4ActionReflection`
separately supplies geometric shared directed edges and their site-reflection bridge;
`GeometricGauge` proves its configuration-space gauge action and measure invariance;
`ReciprocalReflection` supplies the reciprocal-link version. Also,
`SU(N)` (the closed subgroup `det = 1`) is not constructed, though the same compactness argument
applies.
-/

noncomputable section
namespace PMAction.UnitaryHaar
open MeasureTheory Matrix TopologicalSpace

variable (n : ℕ)

/-- The unitary group `U(n)`. -/
abbrev UN := unitary (Matrix (Fin n) (Fin n) ℂ)

theorem isCompact_unitary : IsCompact (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hsub : (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro M hM i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact entry_norm_bound_of_unitary hM i j
  have hc : IsCompact (Set.pi Set.univ (fun (_ : Fin n) =>
      Set.pi Set.univ (fun (_ : Fin n) => Metric.closedBall (0 : ℂ) 1))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hset : (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) =
      {M | Mᴴ * M = 1} ∩ {M | M * Mᴴ = 1} := by
    ext M
    simp [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  have hcl : IsClosed (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hset]
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  exact hc.of_isClosed_subset hcl hsub

instance : CompactSpace (UN n) := isCompact_iff_compactSpace.mp (isCompact_unitary n)

instance : MeasurableSpace (UN n) := borel _
instance : BorelSpace (UN n) := ⟨rfl⟩

/-- The normalized Haar measure on `U(n)`. -/
def haar : Measure (UN n) := Measure.haarMeasure ⊤

instance haar_probability : IsProbabilityMeasure (haar n) :=
  ⟨by simpa [haar] using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (UN n)))⟩

instance : (haar n).IsMulLeftInvariant := by
  unfold haar; infer_instance

local notation "V4" => (Fin 4 → ℝ)

/-- Links of a `U(n)` configuration under an edge assignment. -/
def links {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (U : Fin m → UN n) :
    V4 → V4 → ℝ → Matrix (Fin n) (Fin n) ℂ := fun y v h => (U (ℓ y v h) : Matrix (Fin n) (Fin n) ℂ)

/-- The supplied finite edge assignment gives a Gibbs probability measure.
This does not assert closure under local gauge transformations. -/
theorem uN_gibbs {m : ℕ} (ℓ : V4 → V4 → ℝ → Fin m) (X : Finset V4) (h β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (LatticeGibbs.gibbs (Measure.pi fun _ : Fin m => haar n) β
      (fun U => LatticeGibbs.action X (links n ℓ U) h)) :=
  LatticeGibbs.gibbs_isProbability _ hβ _
    (fun U => LatticeGibbs.action_bounds X (links n ℓ U) (fun y v h => (U (ℓ y v h)).2) h)

end PMAction.UnitaryHaar
