import PMAction.CarrierReferenceCycle

/-!
# Clock-controlled E8 root action

At each fixed clock phase the selected lattice map is identity or the actual
integral E8 root reflection. It preserves the quadratic form and glue code.
The resulting clock/lattice update closes after 43 ticks for a mask excursion.
This is a family of phase-dependent lattice isometries, not one phase-independent
E8 isometry on a proved physical encoding of the complete clock/carrier state.

On the finite carrier shell, moving reflection steps have a norm-two D4-root
displacement in undoubled coordinates. This controls internal carrier geometry;
it is not a spatial finite-propagation theorem for the whole E8 lattice.
-/
noncomputable section
namespace PMAction.ClockControlledRoot
open Matrix PMArch.Lattices SubstrateReflection

abbrev State := Lattice × Fin 43

def controlled (fire : Fin 43 → Bool) : Equiv.Perm State where
  toFun s := (if fire s.2 then reflect s.1 else s.1, s.2)
  invFun s := (if fire s.2 then reflect s.1 else s.1, s.2)
  left_inv s := by cases h : fire s.2 <;> simp [h, SubstrateReflection.involutive s.1]
  right_inv s := by cases h : fire s.2 <;> simp [h, SubstrateReflection.involutive s.1]

@[simp] theorem controlled_twice (fire : Fin 43 → Bool) (s : State) :
    controlled fire (controlled fire s) = s := (controlled fire).left_inv s

def clock : Equiv.Perm State := Equiv.prodCongr (Equiv.refl _) (finRotate 43)
def fire (mask : Fin 43 → Bool) (t : Fin 43) : Bool := decide (mask (finRotate 43 t) ≠ mask t)
def update (mask : Fin 43 → Bool) : Equiv.Perm State := (controlled (fire mask)).trans clock

theorem norm_preserved (mask : Fin 43 → Bool) (s : State) :
    pairing (update mask s).1 (update mask s).1 = pairing s.1 s.1 := by
  change pairing (if fire mask s.2 then reflect s.1 else s.1)
    (if fire mask s.2 then reflect s.1 else s.1) = _
  cases fire mask s.2 <;> simp [SubstrateReflection.preserves_norm]

theorem glue_preserved (mask : Fin 43 → Bool) (s : State) :
    glueCode (update mask s).1 = glueCode s.1 := by
  change glueCode (if fire mask s.2 then reflect s.1 else s.1) = _
  cases fire mask s.2 <;> simp [SubstrateReflection.preserves_glue]

theorem update_conjugate (mask : Fin 43 → Bool) :
    update mask = (controlled mask).trans (clock.trans (controlled mask)) := by
  apply Equiv.ext
  intro s
  change (if fire mask s.2 then reflect s.1 else s.1, finRotate 43 s.2) =
    (if mask (finRotate 43 s.2) then reflect (if mask s.2 then reflect s.1 else s.1)
      else (if mask s.2 then reflect s.1 else s.1), finRotate 43 s.2)
  cases h0 : mask s.2 <;> cases h1 : mask (finRotate 43 s.2) <;>
    simp_all [fire, SubstrateReflection.involutive s.1]

theorem encoded_step (mask : Fin 43 → Bool) (z : Lattice) (t : Fin 43) :
    update mask (controlled mask (z,t)) = controlled mask (z,finRotate 43 t) := by
  rw [update_conjugate]
  change controlled mask (clock (controlled mask (controlled mask (z,t)))) = _
  rw [controlled_twice]
  rfl

theorem iterate_encoded (mask : Fin 43 → Bool) (z : Lattice) (t : Fin 43) (n : ℕ) :
    (update mask)^[n] (controlled mask (z,t)) = controlled mask (z,(finRotate 43)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, encoded_step, Function.iterate_succ_apply']

theorem cycle_closes (mask : Fin 43 → Bool) (s : State) : (update mask)^[43] s = s := by
  obtain ⟨u, hu⟩ := (controlled mask).surjective s
  rw [← hu, iterate_encoded, CarrierReferenceCycle.clock_closes]

/-- The same phase control commutes with the existing D4-to-E8 embedding
calculation; no new root or coefficient is selected by the clock. -/
theorem embedding_intertwines (gate : Fin 43 → Bool) (t : Fin 43) (w : Lattice) :
    (controlled gate (d4Embedding *ᵥ w,t)).1 =
      d4Embedding *ᵥ (if gate t then rootCoordinates w else w) := by
  cases h : gate t <;> simp [controlled, h, SubstrateReflection.embedding_intertwines]

theorem carrier_gate_matches (c : Fin 3) (mask : Fin 43 → Bool)
    (s : CarrierReferenceCycle.State c) :
    (CarrierReferenceCycle.tick c mask s).1 =
      if fire mask s.2 then CarrierEvents.reflect c s.1 else s.1 := by
  rw [CarrierReferenceCycle.tick_gate_form]
  simp [fire]

/-- Carrier coordinates were doubled to be integral. Divide their even
coordinate displacement by two to obtain the actual coset-root step. -/
def displacement {c : Fin 3} (v : CarrierEvents.Carrier c) : Fin 4 → ℤ :=
  fun i => (CarrierEvents.vector (CarrierEvents.reflect c v) i - CarrierEvents.vector v i) / 2

theorem moving_step_is_root (c : Fin 3) : ∀ v ∈ CarrierEvents.active c,
    PMArch.Channels.norm4 (displacement v) = 2 ∧
      (∑ i, displacement v i) = 0 ∧
      (∀ i, CarrierEvents.vector (CarrierEvents.reflect c v) i - CarrierEvents.vector v i =
        2 * displacement v i) := by
  fin_cases c <;> decide +kernel

end PMAction.ClockControlledRoot
