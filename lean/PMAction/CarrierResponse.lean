import PMAction.CarrierCost
import PMAction.EventAccounting
import PMAction.InterferenceReadout

/-! One explicit carrier/event/readout cost connection. Primitive repair length,
preparation and phase-sensitive readout semantics remain named model inputs. -/
noncomputable section
namespace PMAction.CarrierResponse
open Matrix Finset CarrierEvents InterferenceReadout
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma perm_unitary (e : Equiv.Perm ι) : e.permMatrix ℂ ∈ unitary (Matrix ι ι ℂ) := by
  constructor
  · change (e.permMatrix ℂ)ᴴ*e.permMatrix ℂ=1
    rw [conjTranspose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  · change e.permMatrix ℂ*(e.permMatrix ℂ)ᴴ=1
    rw [conjTranspose_permMatrix, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]

lemma mean_bounds [Nonempty ι] (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) :
    0 ≤ meanFlag U ∧ meanFlag U ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (sum_nonneg (fun a _ => flag_nonneg U a)) hn.le
  · apply (div_le_iff₀ hn).mpr
    have hs : (∑ a : ι, flagProbability U a) ≤ ∑ _ : ι, (1 : ℝ) :=
      sum_le_sum (fun a _ => (flag_bounds U hu a).2)
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] using hs

/-- The finite binary law is valid, rather than merely an assigned score. -/
theorem readout_law [Nonempty ι] (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) :
    (∑ b, EventAccounting.binaryMass (meanFlag U) b)=1 ∧
      ∀ b, 0 ≤ EventAccounting.binaryMass (meanFlag U) b :=
  ⟨EventAccounting.binary_normalized _,
    EventAccounting.binary_nonnegative (mean_bounds U hu).1 (mean_bounds U hu).2⟩

/-- m primitive repair events share the same flag; no independence is required. -/
def repairCost (toll : ℝ) (m : ℕ) (U : Matrix ι ι ℂ) : ℝ :=
  EventAccounting.cost toll (EventAccounting.binaryMass (meanFlag U))
    (fun _ : Fin m => ({true} : Finset Bool))

lemma repair_cost (toll : ℝ) (m : ℕ) (U : Matrix ι ι ℂ) :
    repairCost toll m U=toll*m*meanFlag U := by
  rw [repairCost, EventAccounting.weighted_linear]
  simp only [EventAccounting.eventMass, sum_singleton, EventAccounting.binaryMass,
    Bool.true_eq_false, Bool.false_eq_true, ite_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem trace_cost [Nonempty ι] (toll : ℝ) (m : ℕ) (U : Matrix ι ι ℂ)
    (hu : U ∈ unitary (Matrix ι ι ℂ)) :
    repairCost toll m U=(toll*m/2)*(1-U.trace.re/Fintype.card ι) := by
  rw [repair_cost, mean_trace U hu]
  ring

/-- State-change and coherent-comparison events are different operational events. -/
theorem permutation_flag [Nonempty ι] (e : Equiv.Perm ι) :
    meanFlag (e.permMatrix ℂ)=PMArch.NetCost.prob (CarrierCost.changed e)/2 := by
  rw [mean_trace _ (perm_unitary e), CarrierCost.changed_probability]

/-- In each actual eight-state class, the reflection has detection probability one quarter. -/
theorem reflection_flag (c : Fin 3) : meanFlag ((reflect c).permMatrix ℂ)=1/4 := by
  letI : Nonempty (Carrier c) := Fintype.card_pos_iff.mp (by rw [carrier_card]; norm_num)
  rw [permutation_flag]
  change PMArch.NetCost.prob (active c)/2=1/4
  rw [uniform_activation]
  norm_num

theorem reflection_repair_cost (c : Fin 3) (toll : ℝ) (m : ℕ) :
    repairCost toll m ((reflect c).permMatrix ℂ)=toll*m/4 := by
  rw [repair_cost, reflection_flag]
  ring

theorem phase_repair_cost (toll θ : ℝ) (m : ℕ) :
    repairCost toll m (phase θ)=(toll*m/2)*(1-Real.cos θ) := by
  rw [repair_cost, phase_probability]
  ring

/-- Phase-independent required work is retained as a baseline, not silently omitted. -/
def totalCost (baseline toll : ℝ) (m : ℕ) (U : Matrix ι ι ℂ) : ℝ :=
  baseline+repairCost toll m U

theorem phase_excess_cost (baseline toll θ : ℝ) (m : ℕ) :
    totalCost baseline toll m (phase θ)-totalCost baseline toll m (phase 0)=
      (toll*m/2)*(1-Real.cos θ) := by
  simp only [totalCost, phase_repair_cost, Real.cos_zero, sub_self, mul_zero, add_zero]
  ring

/-- The stiffness counts both refreshes and primitive events per repair. -/
theorem refreshed_phase_cost (toll θ : ℝ) (m W : ℕ) :
    (∑ _ : Fin W, repairCost toll m (phase θ))=
      (toll*m*W/2)*(1-Real.cos θ) := by
  simp only [phase_repair_cost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The common event law feeds the existing controlled geometric continuum limit. -/
theorem common_response_limit (toll g : ℝ) (m W : ℕ) (F : Fin 4 → Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = -F ν μ) :
    Filter.Tendsto (fun h : ℝ => GaugeContinuum.density h g (toll*m*W/2) F)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((toll*m*W*g^2/4)*(∑ μ, ∑ ν, F μ ν^2))) := by
  convert GaugeContinuum.density_limit g (toll*m*W/2) F hF using 1 <;> congr 1 <;> ring

end PMAction.CarrierResponse
