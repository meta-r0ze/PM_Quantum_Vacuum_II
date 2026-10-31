import PMAction.LinkConsistency
import PMAction.PersistenceSelection
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A lattice quantum measure from PM's survival weight

`YANG-MILLS-STATUS.md` item 1 asks for a finite-volume lattice measure `Z⁻¹ exp(−β S) dν`. PM's
survival law weights a configuration of cost `S` by `exp(−β S)` (`PersistenceSelection`). On a
finite region that weight is a valid Gibbs density, because PM's action is bounded.

* `wilson_bounds`: for unitary `P`, `0 ≤ Re tr(1 − P) ≤ 2N`.
* `action_bounds`: PM's D₄ action on a finite set `X` of sites,
  `S(U) = Σ_{x∈X} Σ_△ Re tr(1 − U_△)`, lies in `[0, 2N·|X|·|tri|]` for unitary links.
* `gibbs`, `gibbs_isProbability`: for any probability reference measure `ν` on configurations (for
  example, product Haar measure on the links), `β ≥ 0` and an action bounded in `[0, M]`,
  `Z⁻¹ exp(−β S) ν` is a probability measure, with `exp(−β M) ≤ Z ≤ 1`.
* `gibbs_ratio`: its density at two configurations has ratio `exp(−β(S ω − S ω'))`, the ratio of
  their survival weights.

So the survival weight defines the finite-volume lattice measure; no ultraviolet or infrared
issue arises on a finite region. The measure-theoretic content is general: any bounded action
normalizes any probability measure. What is PM-specific is the claim that the Wilson action is the
survival cost; that identification, and the identification of PM's real-time update with this
Euclidean measure, are not derived. Concrete reference measures: `LatticeGibbsU1`, `UnitaryHaar`.
-/

noncomputable section
namespace PMAction.LatticeGibbs
open Matrix MeasureTheory ENNReal
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- **The Wilson term of a unitary is in `[0, 2N]`.** -/
theorem wilson_bounds (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    0 ≤ (trace (1 - P)).re ∧ (trace (1 - P)).re ≤ 2 * (N : ℝ) := by
  have hent : ∀ i, -1 ≤ (P i i).re ∧ (P i i).re ≤ 1 := by
    intro i
    have h := entry_norm_bound_of_unitary hP i i
    have h1 := Complex.abs_re_le_norm (P i i)
    constructor <;> linarith [abs_le.mp (h1.trans h)]
  have htr : (trace (1 - P)).re = ∑ i, (1 - (P i i).re) := by
    simp [trace, Matrix.sub_apply]
  rw [htr]
  constructor
  · exact Finset.sum_nonneg fun i _ => by linarith [(hent i).2]
  · calc ∑ i, (1 - (P i i).re) ≤ ∑ _i : Fin N, (2 : ℝ) :=
          Finset.sum_le_sum fun i _ => by linarith [(hent i).1]
      _ = 2 * N := by simp [mul_comm]

local notation "V4" => (Fin 4 → ℝ)

/-- PM's D₄ lattice action on a finite set of sites. -/
def action (X : Finset V4) (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (h : ℝ) : ℝ :=
  ∑ x ∈ X, ∑ p ∈ D4Gauge.tri,
    (trace (1 - LinkConsistency.holonomy U x (VaryingFields.rv p.1) (VaryingFields.rv p.2) h)).re

/-- **PM's finite-region action is bounded.** -/
theorem action_bounds (X : Finset V4) (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary _) (h : ℝ) :
    0 ≤ action X U h ∧ action X U h ≤ X.card * D4Gauge.tri.card * (2 * N) := by
  have hb : ∀ (x : V4) (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)),
      0 ≤ (trace (1 - LinkConsistency.holonomy U x (VaryingFields.rv p.1)
      (VaryingFields.rv p.2) h)).re ∧ (trace (1 - LinkConsistency.holonomy U x
      (VaryingFields.rv p.1) (VaryingFields.rv p.2) h)).re ≤ 2 * (N : ℝ) := fun x p =>
    wilson_bounds _ ((unitary _).mul_mem ((unitary _).mul_mem (hU _ _ _) (hU _ _ _))
      (Unitary.star_mem (hU _ _ _)))
  unfold action
  constructor
  · exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun p _ => (hb x p).1
  · calc _ ≤ ∑ _x ∈ X, ∑ _p ∈ D4Gauge.tri, (2 * N : ℝ) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun p _ => (hb x p).2
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The survival weight as a density. -/
def weight (β : ℝ) (S : Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β * S ω))

/-- The partition function. -/
def Z (ν : Measure Ω) (β : ℝ) (S : Ω → ℝ) : ℝ≥0∞ := ∫⁻ ω, weight β S ω ∂ν

/-- The Gibbs measure `Z⁻¹ exp(−β S) ν`. -/
def gibbs (ν : Measure Ω) (β : ℝ) (S : Ω → ℝ) : Measure Ω :=
  (Z ν β S)⁻¹ • ν.withDensity (weight β S)

theorem Z_bounds (ν : Measure Ω) [IsProbabilityMeasure ν] {β M : ℝ} (hβ : 0 ≤ β) (S : Ω → ℝ)
    (hS : ∀ ω, 0 ≤ S ω ∧ S ω ≤ M) :
    ENNReal.ofReal (Real.exp (-β * M)) ≤ Z ν β S ∧ Z ν β S ≤ 1 := by
  constructor
  · calc ENNReal.ofReal (Real.exp (-β * M)) = ∫⁻ _ω, ENNReal.ofReal (Real.exp (-β * M)) ∂ν := by
          simp
      _ ≤ Z ν β S := lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr (by nlinarith [(hS ω).2]))
  · calc Z ν β S ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂ν := lintegral_mono fun ω => by
          unfold weight
          rw [ENNReal.ofReal_le_one]
          exact Real.exp_le_one_iff.mpr (by nlinarith [(hS ω).1])
      _ = 1 := by simp

/-- **The survival weight defines a probability measure.** -/
theorem gibbs_isProbability (ν : Measure Ω) [IsProbabilityMeasure ν] {β M : ℝ} (hβ : 0 ≤ β)
    (S : Ω → ℝ) (hS : ∀ ω, 0 ≤ S ω ∧ S ω ≤ M) :
    IsProbabilityMeasure (gibbs ν β S) := by
  obtain ⟨hlo, hhi⟩ := Z_bounds ν hβ S hS
  have h0 : Z ν β S ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) hlo).ne'
  have htop : Z ν β S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hhi
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

omit [MeasurableSpace Ω] in
/-- **Relative weights are survival ratios.** -/
theorem gibbs_ratio (β : ℝ) (S : Ω → ℝ) (ω ω' : Ω) :
    weight β S ω = ENNReal.ofReal (Real.exp (-β * (S ω - S ω'))) * weight β S ω' := by
  unfold weight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end PMAction.LatticeGibbs
