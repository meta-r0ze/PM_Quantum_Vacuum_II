import PMAction.CarrierReferenceCycle

/-!
# Operational readout requires coupling, not a carrier excursion

A readout must put a nonconstant carrier distinction into a probe output. The
autonomous clock history of `CarrierReferenceCycle` does not do this, even for
non-idle root excursions. An explicit reversible conditional clock shift reads
one root-orientation bit without moving the carrier and can be uncomputed.

The supplied finite probe operation is not derived as an E8 primitive. The bit
below is a finite carrier observable, not an identification with Paper I's
matched-resolution lattice pairing or a complete carrier readout.
-/
noncomputable section
namespace PMAction.CarrierProbe
open Matrix CarrierEvents CarrierReferenceCycle

/-- A finite distinction associated with the chosen root's orientation. -/
def bit {c : Fin 3} (v : Carrier c) : Bool := decide (vector v 0 < vector v 1)

theorem bit_distinguishes_active (c : Fin 3) : ∀ v ∈ active c,
    bit (reflect c v) ≠ bit v := by fin_cases c <;> decide +kernel

theorem bit_nonconstant (c : Fin 3) : ∃ u v : Carrier c, bit u ≠ bit v := by
  fin_cases c <;> decide +kernel

/-- Input phase zero is the prepared probe. The output labels 0 and 1 encode
the chosen Boolean distinction; their physical preparation/readout is input. -/
def ReadsBit (c : Fin 3) (F : State c → State c) : Prop :=
  ∀ v : Carrier c, (F (v,0)).2 = if bit v then 1 else 0

def Uncoupled (c : Fin 3) (F : State c → State c) : Prop :=
  ∀ (u v : Carrier c) (t : Fin 43), (F (u,t)).2 = (F (v,t)).2

theorem readout_requires_coupling (c : Fin 3) (F : State c → State c)
    (hread : ReadsBit c F) : ¬ Uncoupled c F := by
  intro hu
  obtain ⟨u,v,hbit⟩ := bit_nonconstant c
  have he := hu u v 0
  rw [hread u, hread v] at he
  cases h0 : bit u <;> cases h1 : bit v <;> simp_all

/-- A correct prepared-probe readout must produce actual probe motion on
some input. The existence of a suitable probe is not a schedule requiring
that it be run once per vacuum cycle. -/
theorem readout_requires_probe_motion (c : Fin 3) (F : State c → State c)
    (hread : ReadsBit c F) : ∃ v : Carrier c, (F (v,0)).2 ≠ 0 := by
  have htrue : ∃ v : Carrier c, bit v = true := by fin_cases c <;> decide +kernel
  obtain ⟨v, hv⟩ := htrue
  refine ⟨v, ?_⟩
  rw [hread v]
  simp [hv]

theorem cycle_phase_iterate (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) (n : ℕ) :
    ((tick c mask)^[n] s).2 = (finRotate 43)^[n] s.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', phase_advances, ih, Function.iterate_succ_apply']

theorem cycle_uncoupled (c : Fin 3) (mask : Fin 43 → Bool) (n : ℕ) :
    Uncoupled c ((tick c mask)^[n]) := by
  intro u v t
  rw [cycle_phase_iterate, cycle_phase_iterate]

/-- No time in this clock-only observation history reads the carrier bit.
This does not say a separate observation of the carrier cannot distinguish it. -/
theorem cycle_does_not_read (c : Fin 3) (mask : Fin 43 → Bool) (n : ℕ) :
    ¬ ReadsBit c ((tick c mask)^[n]) := by
  intro h
  exact readout_requires_coupling c _ h (cycle_uncoupled c mask n)

/-- A nondemolition finite probe: shift its phase conditionally on the bit.
It is a reversible register coupling; no physical elementary gate cost is claimed. -/
def probe (c : Fin 3) : Equiv.Perm (State c) where
  toFun s := (s.1, if bit s.1 then finRotate 43 s.2 else s.2)
  invFun s := (s.1, if bit s.1 then (finRotate 43).symm s.2 else s.2)
  left_inv s := by cases hb : bit s.1 <;> simp [hb]
  right_inv s := by cases hb : bit s.1 <;> simp [hb]

theorem probe_reads (c : Fin 3) : ReadsBit c (probe c) := by
  intro v
  change (if bit v then finRotate 43 0 else 0) = _
  simp

theorem probe_preserves_carrier (c : Fin 3) (s : State c) : (probe c s).1 = s.1 := rfl

theorem probe_uncompute (c : Fin 3) (s : State c) : (probe c).symm (probe c s) = s :=
  (probe c).symm_apply_apply s

theorem probe_reusable (c : Fin 3) (s : State c) (n : ℕ) :
    ((probe c).trans (probe c).symm)^[n] s = s := by
  have he : (probe c).trans (probe c).symm = Equiv.refl _ := by
    apply Equiv.ext
    intro u
    exact (probe c).symm_apply_apply u
  rw [he]
  simp

theorem probe_unitary (c : Fin 3) :
    (probe c).permMatrix ℂ ∈ unitary (Matrix (State c) (State c) ℂ) :=
  CarrierResponse.perm_unitary _

/-- Reading this distinction requires interaction, but its reversibility and
distinguishing power do not require moving the carrier itself. -/
theorem readout_without_carrier_motion (c : Fin 3) :
    ReadsBit c (probe c) ∧ ¬ Uncoupled c (probe c) ∧
      (∀ s : State c, (probe c s).1 = s.1) :=
  ⟨probe_reads c, readout_requires_coupling c _ (probe_reads c), probe_preserves_carrier c⟩

end PMAction.CarrierProbe
