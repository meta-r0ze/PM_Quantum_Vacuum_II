import PMAction.ParityReadoutCircuit

/-!
# The existing E8 root reflection is an in-band parity readout

Coordinate 2 is the accumulator, the other seven coordinates are data, and
the existing independent phase clock schedules read/undo. The lattice norm and
glue are preserved by the actual root reflection. This realizes a conditional
matched readout without a separate abstract bit gate. Preparation and mandatory
execution are not selected here. Larger pairings must not be priced as a single
nearest-neighbour displacement.
-/
noncomputable section
namespace PMAction.InBandRootReadout
open Matrix PMArch.Lattices SubstrateReflection

def record (z : Lattice) : Bool := ParityReadoutCircuit.coordinateBit (z 2)

/-- Unimodularity supplies an integral substrate probe for the accumulator
itself. This is an observable certificate, not a zero-cost detector circuit. -/
def recordProbe : Lattice := gramInverse *ᵥ Pi.single 2 1

theorem record_is_intrinsic (z : Lattice) :
    record z = MatchedLatticeProbe.outcome recordProbe z := by
  have hg : gram * gramInverse = 1 := mul_eq_one_comm.mp gram_inverse
  have hp : pairing z recordProbe = z 2 := by
    simp only [pairing, recordProbe, mulVec_mulVec, hg, one_mulVec, dotProduct_single, mul_one]
  simp only [MatchedLatticeProbe.outcome, hp, record, ParityReadoutCircuit.coordinateBit]

theorem accumulator_update (z : Lattice) : (reflect z) 2 = z 2 + pairing z root := by
  simp [reflect_coordinates, MatchedLatticeProbe.root_pairing]
  ring

theorem data_retained (z : Lattice) (i : Fin 8) (hi : i ≠ 2) : (reflect z) i = z i := by
  rw [reflect_coordinates]
  simp [hi]

theorem record_update (z : Lattice) :
    record (reflect z) = Bool.xor (record z) (MatchedLatticeProbe.outcome root z) := by
  unfold record
  rw [accumulator_update, ← ParityReadoutCircuit.parity_sum]
  rfl

theorem clean_record_reads (z : Lattice) (hz : record z = false) :
    record (reflect z) = MatchedLatticeProbe.outcome root z := by
  rw [record_update, hz]
  simp

theorem read_undo (z : Lattice) : reflect (reflect z) = z := SubstrateReflection.involutive z

theorem displacement (z : Lattice) : reflect z - z = Pi.single 2 (pairing z root) := by
  ext i
  by_cases hi : i = 2
  · subst i
    simp only [Pi.sub_apply, accumulator_update, Pi.single_eq_same]
    ring
  · simp [Pi.sub_apply, data_retained z i hi, Pi.single_eq_of_ne hi]

theorem displacement_norm (z : Lattice) :
    pairing (reflect z - z) (reflect z - z) = 2 * (pairing z root)^2 := by
  rw [displacement]
  simp [pairing, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem changed_iff (z : Lattice) : reflect z ≠ z ↔ pairing z root ≠ 0 := by
  constructor
  · intro hn hp
    apply hn
    simp [reflect, hp]
  · intro hp he
    have hh := congrArg (fun w : Lattice => w 2) he
    rw [accumulator_update] at hh
    exact hp (by linarith)

def UnitCoupled (z : Lattice) : Prop := pairing z root = -1 ∨ pairing z root = 0 ∨ pairing z root = 1

theorem norm_shift (z : Lattice) (a : ℤ) :
    pairing (z + a • root) (z + a • root) =
      pairing z z + 2 * a * pairing z root + 2 * a^2 := by
  simp [pairing, root_coordinates, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The least nonzero quadratic level is two. This is a lattice-cost fact,
not identification of that norm with a physical excitation energy. -/
theorem minimum_nonzero_norm : IsLeast {n : ℤ | ∃ z : Lattice, z ≠ 0 ∧ pairing z z = n} 2 := by
  constructor
  · refine ⟨root, ?_, SubstrateReflection.root_norm⟩
    intro h
    have hh := SubstrateReflection.root_norm
    rw [h] at hh
    norm_num [pairing] at hh
  · rintro n ⟨z, hz, rfl⟩
    have hp := positive_norm z hz
    obtain ⟨k, hk⟩ := even_norm z
    omega

/-- On the least nonzero shell, a clean parity accumulator excludes the two
extremal states ±root. Positivity then forces the coupling to be 0 or ±1. -/
theorem minimal_clean_unit_coupled (z : Lattice) (hn : pairing z z = 2)
    (hz : record z = false) : UnitCoupled z := by
  have hneq (a : ℤ) (ha : a = 1 ∨ a = -1) : z + a • root ≠ 0 := by
    intro he
    have hh := congrFun he 2
    simp [root_coordinates] at hh
    have hi : z 2 = a := by omega
    have heven : (2 : ℤ) ∣ z 2 := by simpa [record, ParityReadoutCircuit.coordinateBit] using hz
    rcases ha with ha | ha
    · have hi1 : z 2 = 1 := by omega
      norm_num [hi1] at heven
    · have hi1 : z 2 = -1 := by omega
      norm_num [hi1] at heven
  have hp := positive_norm (z + (1 : ℤ) • root) (hneq 1 (by simp))
  have hm := positive_norm (z + (-1 : ℤ) • root) (hneq (-1) (by simp))
  rw [norm_shift, hn] at hp hm
  unfold UnitCoupled
  omega

theorem elementary_step (z : Lattice) (hu : UnitCoupled z) (hm : reflect z ≠ z) :
    pairing (reflect z - z) (reflect z - z) = 2 := by
  rw [displacement_norm]
  have hn := (changed_iff z).mp hm
  rcases hu with h | h | h <;> simp_all

theorem unit_activity_iff_bit (z : Lattice) (hu : UnitCoupled z) :
    reflect z ≠ z ↔ MatchedLatticeProbe.outcome root z = true := by
  rw [changed_iff]
  rcases hu with h | h | h <;> norm_num [MatchedLatticeProbe.outcome, h]

theorem minimal_clean_probe (z : Lattice) (hn : pairing z z = 2) (hz : record z = false) :
    record (reflect z) = MatchedLatticeProbe.outcome root z ∧
      (reflect z ≠ z ↔ MatchedLatticeProbe.outcome root z = true) ∧
      (reflect z ≠ z → pairing (reflect z-z) (reflect z-z) = 2) := by
  have hu := minimal_clean_unit_coupled z hn hz
  exact ⟨clean_record_reads z hz, unit_activity_iff_bit z hu, elementary_step z hu⟩

theorem undo_active_iff (z : Lattice) : reflect (reflect z) ≠ reflect z ↔ reflect z ≠ z := by
  rw [read_undo]
  exact ne_comm

/-- Both actual root events are included. The input law is supplied; no
independence between the read and undo events is asserted. -/
def events {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (sample : Ω → Lattice)
    (i : Fin 2) : Finset Ω :=
  Finset.univ.filter fun ω => if i = 0 then reflect (sample ω) ≠ sample ω
    else reflect (reflect (sample ω)) ≠ reflect (sample ω)

theorem events_are_observed_bit {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (sample : Ω → Lattice) (hn : ∀ ω, pairing (sample ω) (sample ω) = 2)
    (hz : ∀ ω, record (sample ω) = false) (i : Fin 2) :
    events sample i = Finset.univ.filter fun ω => MatchedLatticeProbe.outcome root (sample ω) = true := by
  ext ω
  simp only [events, Finset.mem_filter, Finset.mem_univ, true_and, undo_active_iff]
  split_ifs <;> exact (minimal_clean_probe (sample ω) (hn ω) (hz ω)).2.1

theorem expected_read_undo_cost {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (sample : Ω → Lattice) (hn : ∀ ω, pairing (sample ω) (sample ω) = 2)
    (hz : ∀ ω, record (sample ω) = false) (mass : Ω → ℝ) (toll : ℝ) :
    EventAccounting.cost toll mass (events sample) =
      2 * toll * EventAccounting.eventMass mass
        (Finset.univ.filter fun ω => MatchedLatticeProbe.outcome root (sample ω) = true) := by
  rw [EventAccounting.weighted_linear]
  simp_rw [events_are_observed_bit sample hn hz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A false parity output does not generally mean zero physical displacement. -/
theorem even_response_moves :
    let z : Lattice := Pi.single 0 2
    record z = false ∧ MatchedLatticeProbe.outcome root z = false ∧
      reflect z ≠ z ∧ pairing (reflect z - z) (reflect z - z) = 8 := by decide +kernel

theorem scheduled_read (z : Lattice) (hz : record z = false) :
    record (ClockControlledRoot.update CarrierReferenceCycle.excursionMask (z,0)).1 =
      MatchedLatticeProbe.outcome root z := by
  change record (if ClockControlledRoot.fire CarrierReferenceCycle.excursionMask 0 then reflect z else z) = _
  have hf : ClockControlledRoot.fire CarrierReferenceCycle.excursionMask 0 = true := by decide +kernel
  rw [hf]
  exact clean_record_reads z hz

theorem schedule_closes (s : ClockControlledRoot.State) :
    (ClockControlledRoot.update CarrierReferenceCycle.excursionMask)^[43] s = s :=
  ClockControlledRoot.cycle_closes _ s

end PMAction.InBandRootReadout
