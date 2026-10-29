import PMAction.RootTransferAccounting

/-!
# Which event does a reconstructed root pulse charge?

Under the existing squared-amplitude readout, endpoint carrier-label change
and coherent comparison are distinct events. For the reconstructed actual-root
phase, label change is exactly twice the comparison flag, at every time.
This prices the specified readouts, not unobserved microscopic trajectories.
-/
noncomputable section
namespace PMAction.RootPulseEvents
open Matrix Finset InterferenceReadout
open scoped Matrix.Norms.Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Endpoint label test after a basis input. This is not a path event count. -/
def labelChange (U : Matrix n n ℂ) (a : n) : ℝ :=
  ∑ b ∈ univ.filter (fun b => b ≠ a), Complex.normSq (U b a)

lemma labelChange_formula (U : Matrix n n ℂ) (hu : U ∈ unitary (Matrix n n ℂ)) (a : n) :
    labelChange U a = 1 - Complex.normSq (U a a) := by
  have h := column_population U hu a
  have hs := sum_filter_add_sum_filter_not (s := (univ : Finset n))
    (p := fun b => b = a) (f := fun b => Complex.normSq (U b a))
  simp only [sum_filter, sum_ite_eq', mem_univ, ite_true] at hs
  unfold labelChange
  rw [sum_filter]
  rw [h] at hs
  linarith

lemma phase_diagonal (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) (a : n) :
    RootTransferPhase.phase e p t a a =
      if e a = a then 1 else
        (1 + Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I))/2 := by
  rw [RootTransferPhase.phase_formula e he]
  by_cases ha : e a = a <;>
    simp [InvolutionSpectral.plus, InvolutionSpectral.minus,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, ha] <;> ring

lemma exp_normSq (s : ℝ) : Complex.normSq (Complex.exp (-(s : ℂ)*Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := Complex.norm_exp_ofReal_mul_I (-s)
  have hn : ‖Complex.exp (-(s : ℂ)*Complex.I)‖ = 1 := by
    simpa only [Complex.ofReal_neg, neg_mul] using h
  rw [hn]
  norm_num

lemma coefficient_population (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq ((1+z)/2) = (1+z.re)/2 := by
  rw [Complex.normSq_div, Complex.normSq_add, hz]
  norm_num
  ring

/-- The label-changing probability of the actual phase, including fixed carriers. -/
theorem phase_labelChange (e : Equiv.Perm n) (he : Function.Involutive e)
    (p t : ℝ) (a : n) :
    labelChange (RootTransferPhase.phase e p t) a =
      if e a = a then 0 else (1-Real.cos (RootTransferPhase.gap p*t))/2 := by
  rw [labelChange_formula _ (RootTransferPhase.phase_unitary e he p t) a,
    phase_diagonal e he]
  by_cases ha : e a = a
  · simp [ha]
  · simp only [ha, ite_false]
    rw [coefficient_population _ (exp_normSq _)]
    simp only [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring

/-- The coherent comparator has half the endpoint label-change probability. -/
theorem phase_flag (e : Equiv.Perm n) (he : Function.Involutive e)
    (p t : ℝ) (a : n) :
    flagProbability (RootTransferPhase.phase e p t) a =
      if e a = a then 0 else (1-Real.cos (RootTransferPhase.gap p*t))/4 := by
  rw [flag_formula _ (RootTransferPhase.phase_unitary e he p t), phase_diagonal e he]
  by_cases ha : e a = a
  · simp [ha]
  · simp only [ha, ite_false, Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring

theorem event_ratio (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) (a : n) :
    labelChange (RootTransferPhase.phase e p t) a =
      2 * flagProbability (RootTransferPhase.phase e p t) a := by
  rw [phase_labelChange e he, phase_flag e he]
  split_ifs <;> ring

/-- Uniform actual-carrier label test, with the derived four-of-eight activation. -/
theorem actual_mean_change (c : Fin 3) (p t : ℝ) :
    (∑ a : CarrierEvents.Carrier c,
      labelChange (RootTransferPhase.phase (CarrierEvents.reflect c) p t) a) /
      Fintype.card (CarrierEvents.Carrier c) =
        (1-Real.cos (RootTransferPhase.gap p*t))/4 := by
  simp_rw [phase_labelChange _ (CarrierEvents.reflection_involutive c)]
  have hs (q : ℝ) : (∑ a : CarrierEvents.Carrier c,
      if CarrierEvents.reflect c a = a then 0 else q) = 4*q := by
    simp_rw [show ∀ a : CarrierEvents.Carrier c,
      (if CarrierEvents.reflect c a = a then 0 else q) =
      (if CarrierEvents.reflect c a ≠ a then q else 0) by
        intro a; by_cases h : CarrierEvents.reflect c a = a <;> simp [h]]
    rw [← sum_filter]
    change ∑ _ ∈ CarrierEvents.active c, q = 4*q
    simp [CarrierEvents.active_card]
  rw [hs, CarrierEvents.carrier_card]
  push_cast
  ring

theorem actual_mean_flag (c : Fin 3) (p t : ℝ) :
    meanFlag (RootTransferPhase.phase (CarrierEvents.reflect c) p t) =
      (1-Real.cos (RootTransferPhase.gap p*t))/8 := by
  have h := actual_mean_change c p t
  simp_rw [event_ratio _ (CarrierEvents.reflection_involutive c)] at h
  rw [← mul_sum] at h
  unfold meanFlag
  rw [CarrierEvents.carrier_card] at h ⊢
  norm_num at h ⊢
  linarith

/-- A single flagged endpoint event is priced by its own law, not the comparison law. -/
theorem label_price (p t toll : ℝ) :
    EventAccounting.cost toll
      (EventAccounting.binaryMass ((1-Real.cos (RootTransferPhase.gap p*t))/4))
      (fun _ : Fin 1 => ({true} : Finset Bool)) =
      toll*(1-Real.cos (RootTransferPhase.gap p*t))/4 := by
  rw [EventAccounting.binary_flag_cost]
  ring

/-- Positive label-change readout is not the one-event comparator price. -/
theorem price_ratio (c : Fin 3) (p t toll : ℝ) :
    toll * ((1-Real.cos (RootTransferPhase.gap p*t))/4) =
      2 * CarrierResponse.repairCost toll 1
        (RootTransferPhase.phase (CarrierEvents.reflect c) p t) := by
  rw [CarrierResponse.repair_cost, actual_mean_flag]
  norm_num
  ring

/-- The endpoint label readout is a normalized binary law. -/
theorem label_law (p t : ℝ) :
    (∑ b, EventAccounting.binaryMass ((1-Real.cos (RootTransferPhase.gap p*t))/4) b) = 1 ∧
      ∀ b, 0 ≤ EventAccounting.binaryMass ((1-Real.cos (RootTransferPhase.gap p*t))/4) b := by
  constructor
  · exact EventAccounting.binary_normalized _
  · apply EventAccounting.binary_nonnegative
    · linarith [Real.cos_le_one (RootTransferPhase.gap p*t)]
    · linarith [Real.neg_one_le_cos (RootTransferPhase.gap p*t)]

lemma quarter_angle (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.gap p * RootTransferPhase.quarterTime p = Real.pi/2 := by
  have hn := ne_of_gt (RootTransferPhase.gap_positive p hp hp1)
  unfold RootTransferPhase.quarterTime
  field_simp [hn]

/-- The two readouts of the same reconstructed quarter pulse have different probabilities. -/
theorem actual_quarter_events (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    (∑ a : CarrierEvents.Carrier c,
      labelChange (RootTransferPhase.phase (CarrierEvents.reflect c) p
        (RootTransferPhase.quarterTime p)) a) / Fintype.card (CarrierEvents.Carrier c) = 1/4 ∧
      meanFlag (RootTransferPhase.phase (CarrierEvents.reflect c) p
        (RootTransferPhase.quarterTime p)) = 1/8 := by
  rw [actual_mean_change, actual_mean_flag, quarter_angle p hp hp1]
  norm_num

/-- One statistical root attempt cannot be assigned the quarter pulse's endpoint
label-test price: even those supplied event laws disagree for every admissible p. -/
theorem one_attempt_price_lt_quarter_label (c : Fin 3) (p toll : ℝ)
    (hp : p < 1/2) (ht : 0 < toll) :
    EventAccounting.cost toll (RootTransferAccounting.mass c p)
      (fun _ : Fin 1 => RootTransferAccounting.event c) < toll/4 := by
  rw [RootTransferAccounting.expected_root_cost]
  nlinarith

end PMAction.RootPulseEvents
