import PMAction.RootTransferPhase
import PMAction.Survival
import PMAction.PrimitiveRecordBoundary

/-!
# Root-attempt event cost and the transfer/phase distinction

A Bernoulli attempt at the existing reflection has an explicit changed-state
cost under the supplied uniform carrier law and primitive tariff. The real
stochastic transfer is not the coherent unitary phase gate: it contracts its
odd sector. Its event count therefore cannot be silently charged to the
reconstructed real-time preparation.
-/
noncomputable section
namespace PMAction.RootTransferAccounting
open Matrix Finset PMFramework.LawSelection

/-- The two equally counted moving-orbit alternatives have costs zero and cost.
Their choice and multiplicity are explicit history-model inputs. -/
def attemptAction (cost : ℝ) (b : Bool) : ℝ := if b then cost else 0

def gibbsRate (β cost : ℝ) : ℝ :=
  PMFramework.Gibbs.probability β (attemptAction cost) true

lemma gibbsRate_formula (β cost : ℝ) :
    gibbsRate β cost = Real.exp (-β*cost) / (1 + Real.exp (-β*cost)) := by
  simp [gibbsRate, PMFramework.Gibbs.probability, PMFramework.Gibbs.partition,
    PMFramework.Gibbs.weight, attemptAction, add_comm]

/-- Positive action bias makes the transfer reconstructible; no numerical rate is fitted. -/
theorem gibbsRate_range (β cost : ℝ) (hβ : 0 < β) (hc : 0 < cost) :
    0 < gibbsRate β cost ∧ gibbsRate β cost < 1/2 := by
  rw [gibbsRate_formula]
  have hq := Real.exp_pos (-β*cost)
  have hq1 : Real.exp (-β*cost) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    nlinarith
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 1 + Real.exp (-β*cost))).mpr
    linarith

/-- The rate then depends on the pre-existing action bias and equal-history prior. -/
lemma gibbs_residual (β cost : ℝ) :
    RootTransferPhase.residual (gibbsRate β cost) =
      (1 - Real.exp (-β*cost)) / (1 + Real.exp (-β*cost)) := by
  rw [gibbsRate_formula]
  unfold RootTransferPhase.residual
  have hn : 1 + Real.exp (-β*cost) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Attempt choice and sampled carrier are independent in this specified model. -/
def mass (c : Fin 3) (p : ℝ) : Bool × CarrierEvents.Carrier c → ℝ :=
  fun ω => EventAccounting.binaryMass p ω.1 * uniform ω.2

def event (c : Fin 3) : Finset (Bool × CarrierEvents.Carrier c) :=
  univ.filter (fun ω => ω.1 = true ∧ ω.2 ∈ CarrierEvents.active c)

lemma mass_normalized (c : Fin 3) (p : ℝ) : (∑ ω, mass c p ω) = 1 := by
  simp [mass, uniform, Fintype.sum_prod_type, CarrierEvents.carrier_card,
    EventAccounting.binaryMass]
  ring

lemma mass_nonnegative (c : Fin 3) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∀ ω, 0 ≤ mass c p ω := by
  intro ω
  apply mul_nonneg (EventAccounting.binary_nonnegative h0 h1 ω.1)
  unfold uniform
  positivity

/-- Both the actual root activation and the supplied attempt probability are counted. -/
theorem expected_root_cost (c : Fin 3) (p toll : ℝ) :
    EventAccounting.cost toll (mass c p) (fun _ : Fin 1 => event c) = p * toll / 2 := by
  rw [EventAccounting.weighted_linear]
  simp only [Fin.sum_univ_one]
  have hm : EventAccounting.eventMass (mass c p) (event c) = p/2 := by
    simp only [EventAccounting.eventMass, event, Finset.sum_filter, Fintype.sum_prod_type]
    simp [mass, uniform, EventAccounting.binaryMass, ← Finset.sum_filter,
      CarrierEvents.active_card, CarrierEvents.carrier_card]
    ring
  rw [hm]
  ring

section Boundary
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma basis_move (e : Equiv.Perm n) (he : Function.Involutive e) (a : n) :
    e.permMatrix ℂ *ᵥ Pi.single a 1 = Pi.single (e a) 1 := by
  rw [Matrix.permMatrix_mulVec]
  ext x
  by_cases hx : x = e a
  · subst x
    simp [he a]
  · have ha : e x ≠ a := by
      intro h
      apply hx
      have hh := congrArg e h
      simpa only [he x] using hh
    simp [hx, ha]

open scoped Matrix.Norms.Operator in
/-- The quarter preparation now comes from the specified root transfer's
phase evolution, with its scalar phase retained and no arbitrary mixer basis. -/
theorem reconstructed_preparation (e : Equiv.Perm n) (he : Function.Involutive e)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (a : n) :
    RootTransferPhase.phase e p (RootTransferPhase.quarterTime p) *ᵥ Pi.single a 1 =
      Complex.exp (-(Real.pi/4 : ℝ) * Complex.I) •
        PrimitiveRecordBoundary.quarterState a (e a) := by
  rw [RootTransferPhase.quarter_pulse e he p hp hp1, Matrix.smul_mulVec]
  congr 1
  rw [LocalUnitary.rotation, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, basis_move e he]
  have hs : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four, hs]
  unfold PrimitiveRecordBoundary.quarterState
  simp only [smul_add, smul_smul]
  module

def oddVector (e : Equiv.Perm n) (a : n) : n → ℂ := Pi.single a 1 - Pi.single (e a) 1

lemma odd_eigenvector (e : Equiv.Perm n) (he : Function.Involutive e) (a : n) :
    e.permMatrix ℂ *ᵥ oddVector e a = -oddVector e a := by
  rw [oddVector, Matrix.mulVec_sub, basis_move e he, basis_move e he, he a]
  abel

lemma odd_population (e : Equiv.Perm n) (a : n) (ha : e a ≠ a) :
    CommonResponse.nsq (oddVector e a) = 2 := by
  unfold CommonResponse.nsq oddVector
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp [dotProduct, Pi.single_apply, ha, Ne.symm ha]
  norm_num

lemma odd_transfer (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ) (a : n) :
    RootTransferPhase.transfer e p *ᵥ oddVector e a =
      (RootTransferPhase.residual p : ℂ) • oddVector e a := by
  rw [RootTransferPhase.transfer, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
    odd_eigenvector e he]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, RootTransferPhase.residual]
  push_cast
  ring

/-- The statistical one-step transfer loses odd-sector squared norm for 0<p<1/2. -/
theorem transfer_not_unitary (e : Equiv.Perm n) (he : Function.Involutive e)
    (a : n) (ha : e a ≠ a) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.transfer e p ∉ unitary (Matrix n n ℂ) := by
  intro hu
  have h := congrArg Complex.re (CommonResponse.unitary_nsq _ hu (oddVector e a))
  change CommonResponse.nsq (RootTransferPhase.transfer e p *ᵥ oddVector e a) =
      CommonResponse.nsq (oddVector e a) at h
  rw [odd_transfer e he, ControllerHamiltonian.nsq_smul, odd_population e a ha] at h
  have h0 := RootTransferPhase.residual_positive p hp1
  have h1 : RootTransferPhase.residual p < 1 := by unfold RootTransferPhase.residual; linarith
  simp only [Complex.normSq_ofReal] at h
  nlinarith

/-- Distinct admissible rates on an actual moving root orbit remain distinguishable. -/
theorem actual_rate_freedom (c : Fin 3) :
    RootTransfer.transfer (CarrierEvents.reflect c) (1/4) ≠
      RootTransfer.transfer (CarrierEvents.reflect c) (1/3) := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < (CarrierEvents.active c).card by
    rw [CarrierEvents.active_card]; norm_num)
  have hm : CarrierEvents.reflect c a ≠ a := (Finset.mem_filter.mp ha).2
  exact RootTransfer.rates_distinct _ a hm _ _ (by norm_num)

end Boundary
end PMAction.RootTransferAccounting
