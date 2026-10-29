import PMAction.MatchedLatticeProbe

/-!
# Repeatable matched readout with an independent clock

The input and substrate probe are retained lattice registers. A separate bit
is the temporary readout, and a separate 43-phase clock always advances. The
read/undo coupling is explicit but is not yet derived as a physical E8 gate.
Both a reading schedule and an idle schedule preserve the lattice data and
close after 43 ticks. Static one-bit readability does not choose between them.
-/
noncomputable section
namespace PMAction.ScheduledReadout
open Matrix PMArch.Lattices SubstrateReflection

abbrev Memory := Lattice × (Lattice × Bool)
abbrev State := Memory × Fin 43

def record (s : State) : Bool := s.1.2.2

/-- Reversible compute/undo of the actual modulo-two pairing. -/
def readGate : Equiv.Perm Memory where
  toFun m := (m.1, m.2.1, if MatchedLatticeProbe.outcome m.2.1 m.1 then !m.2.2 else m.2.2)
  invFun m := (m.1, m.2.1, if MatchedLatticeProbe.outcome m.2.1 m.1 then !m.2.2 else m.2.2)
  left_inv m := by cases h : MatchedLatticeProbe.outcome m.2.1 m.1 <;> simp [h]
  right_inv m := by cases h : MatchedLatticeProbe.outcome m.2.1 m.1 <;> simp [h]

@[simp] theorem readGate_twice (m : Memory) : readGate (readGate m) = m := readGate.left_inv m

def rebase (mask : Fin 43 → Bool) : Equiv.Perm State where
  toFun s := (if mask s.2 then readGate s.1 else s.1, s.2)
  invFun s := (if mask s.2 then readGate s.1 else s.1, s.2)
  left_inv s := by cases h : mask s.2 <;> simp [h]
  right_inv s := by cases h : mask s.2 <;> simp [h]

@[simp] theorem rebase_twice (mask : Fin 43 → Bool) (s : State) : rebase mask (rebase mask s) = s :=
  (rebase mask).left_inv s

def clock : Equiv.Perm State := Equiv.prodCongr (Equiv.refl _) (finRotate 43)
def tick (mask : Fin 43 → Bool) : Equiv.Perm State := (rebase mask).trans (clock.trans (rebase mask))
def readCycle : Equiv.Perm State := tick CarrierReferenceCycle.excursionMask
def prepared (x y : Lattice) : State := ((x,y,false),0)

def ReadsRoot (F : State → State) : Prop :=
  ∀ x : Lattice, record (F (prepared x root)) = MatchedLatticeProbe.outcome root x

theorem phase_advances (mask : Fin 43 → Bool) (s : State) : (tick mask s).2 = finRotate 43 s.2 := rfl

theorem tick_gate_form (mask : Fin 43 → Bool) (s : State) :
    tick mask s =
      (if mask (finRotate 43 s.2) ≠ mask s.2 then readGate s.1 else s.1, finRotate 43 s.2) := by
  change (if mask (finRotate 43 s.2) then readGate (if mask s.2 then readGate s.1 else s.1)
    else (if mask s.2 then readGate s.1 else s.1), finRotate 43 s.2) = _
  cases h0 : mask s.2 <;> cases h1 : mask (finRotate 43 s.2) <;> simp_all

theorem input_preserved (mask : Fin 43 → Bool) (s : State) : (tick mask s).1.1 = s.1.1 := by
  rw [tick_gate_form]
  split <;> rfl

theorem probe_preserved (mask : Fin 43 → Bool) (s : State) : (tick mask s).1.2.1 = s.1.2.1 := by
  rw [tick_gate_form]
  split <;> rfl

theorem norms_preserved (mask : Fin 43 → Bool) (s : State) :
    pairing (tick mask s).1.1 (tick mask s).1.1 = pairing s.1.1 s.1.1 ∧
      pairing (tick mask s).1.2.1 (tick mask s).1.2.1 = pairing s.1.2.1 s.1.2.1 := by
  rw [input_preserved, probe_preserved]
  exact ⟨rfl,rfl⟩

theorem encoded_step (mask : Fin 43 → Bool) (m : Memory) (t : Fin 43) :
    tick mask (rebase mask (m,t)) = rebase mask (m,finRotate 43 t) := by
  change rebase mask (clock (rebase mask (rebase mask (m,t)))) = _
  rw [rebase_twice]
  rfl

theorem iterate_encoded (mask : Fin 43 → Bool) (m : Memory) (t : Fin 43) (n : ℕ) :
    (tick mask)^[n] (rebase mask (m,t)) = rebase mask (m,(finRotate 43)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, encoded_step, Function.iterate_succ_apply']

theorem cycle_closes (mask : Fin 43 → Bool) (s : State) : (tick mask)^[43] s = s := by
  obtain ⟨u, hu⟩ := (rebase mask).surjective s
  rw [← hu, iterate_encoded, CarrierReferenceCycle.clock_closes]

theorem cycles_repeat (mask : Fin 43 → Bool) (s : State) (n : ℕ) : (tick mask)^[43*n] s = s := by
  have hc : (tick mask)^[43] = id := funext (cycle_closes mask)
  rw [Function.iterate_mul, hc]
  simp

theorem read_after_one (x y : Lattice) :
    readCycle (prepared x y) = ((x,y,MatchedLatticeProbe.outcome y x),1) := by
  rw [readCycle, tick_gate_form]
  cases h : MatchedLatticeProbe.outcome y x <;>
    simp [prepared, CarrierReferenceCycle.excursionMask, readGate, h]

theorem readCycle_reads : ReadsRoot readCycle := by
  intro x
  rw [read_after_one]
  rfl

theorem record_reused (x y : Lattice) : (readCycle^[2] (prepared x y)) = ((x,y,false),2) := by
  have he : rebase CarrierReferenceCycle.excursionMask ((x,y,false),0) = prepared x y := by
    simp [rebase, CarrierReferenceCycle.excursionMask, prepared]
  rw [← he, readCycle, iterate_encoded]
  simp [Function.iterate_succ_apply, rebase, CarrierReferenceCycle.excursionMask]

/-- A norm-preserving idle schedule has the same independent clock and memory. -/
theorem idle_form (s : State) : tick (fun _ => false) s = clock s := by
  rw [tick_gate_form]
  rfl

theorem fixed_record_cannot_read (F : State → State) (hf : ∀ s, record (F s) = record s) :
    ¬ ReadsRoot F := by
  intro hread
  have hh := hread (Pi.single 0 1)
  rw [hf, MatchedLatticeProbe.root_example.2.2.2] at hh
  change false = true at hh
  cases hh

theorem idle_does_not_read : ¬ ReadsRoot (tick (fun _ => false)) := by
  apply fixed_record_cannot_read
  intro s
  rw [idle_form]
  rfl

theorem e8_bit_readable : PMArch.SelfReadable.BitReadable gram := by
  rw [PMArch.SelfReadable.bitReadable_iff_odd]
  rcases Int.isUnit_iff.mp gram_unimodular with h | h <;> rw [h] <;> decide

/-- Exact scope: static matched readability, norm preservation and 43-tick
closure coexist with no operational readout in this scheduled register model. -/
theorem readable_idle_witness :
    PMArch.SelfReadable.BitReadable gram ∧
      (∀ s : State, (tick (fun _ => false))^[43] s = s) ∧
      (∀ s : State, (tick (fun _ => false) s).2 = finRotate 43 s.2) ∧
      ¬ ReadsRoot (tick (fun _ => false)) :=
  ⟨e8_bit_readable, cycle_closes _, phase_advances _, idle_does_not_read⟩

end PMAction.ScheduledReadout
