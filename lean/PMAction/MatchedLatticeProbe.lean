import PMAction.ClockControlledRoot
import PMArch.SelfReadable

/-! A reversible register realization of the exact modulo-two pairing used
by Paper I's one-bit readability postulate. The conditional clock coupling and
its preparation/cost/local implementation remain supplied. This is not a
derivation of an execution rate or of the coherent comparison readout. -/
noncomputable section
namespace PMAction.MatchedLatticeProbe
open Matrix PMArch.Lattices SubstrateReflection

/-- Input lattice state, retained substrate probe state, writable phase register. -/
abbrev State := Lattice × (Lattice × Fin 43)

def outcome (y x : Lattice) : Bool := decide (¬ (2 : ℤ) ∣ pairing x y)

/-- The observable uses exactly the postulate's paired one-bit resolution. -/
theorem same_resolution (y x : Lattice) : outcome y x = false ↔
    (2 : ℤ) ∣ x ⬝ᵥ (gram *ᵥ y) := by simp [outcome, pairing]

def probe : Equiv.Perm State where
  toFun s := (s.1, s.2.1, if outcome s.2.1 s.1 then finRotate 43 s.2.2 else s.2.2)
  invFun s := (s.1, s.2.1, if outcome s.2.1 s.1 then (finRotate 43).symm s.2.2 else s.2.2)
  left_inv s := by cases h : outcome s.2.1 s.1 <;> simp [h]
  right_inv s := by cases h : outcome s.2.1 s.1 <;> simp [h]

def ReadsPairing (y : Lattice) (F : State → State) : Prop :=
  ∀ x : Lattice, (F (x,y,0)).2.2 = if outcome y x then 1 else 0

theorem probe_reads (y : Lattice) : ReadsPairing y probe := by
  intro x
  change (if outcome y x then finRotate 43 0 else 0) = _
  simp

theorem input_preserved (s : State) : (probe s).1 = s.1 := rfl

theorem probe_state_preserved (s : State) : (probe s).2.1 = s.2.1 := rfl

theorem norm_preserved (s : State) :
    pairing (probe s).1 (probe s).1 = pairing s.1 s.1 ∧
      pairing (probe s).2.1 (probe s).2.1 = pairing s.2.1 s.2.1 := ⟨rfl,rfl⟩

theorem glue_preserved (s : State) :
    glueCode (probe s).1 = glueCode s.1 ∧ glueCode (probe s).2.1 = glueCode s.2.1 := ⟨rfl,rfl⟩

theorem probe_uncompute (s : State) : probe.symm (probe s) = s := probe.symm_apply_apply s

/-- The existing norm-two E8 root is itself an informative substrate probe:
it separates zero from a norm-two basis root. The probe register is retained;
its preparation and storage are not priced here. -/
theorem root_example : pairing root root = 2 ∧
    pairing (Pi.single 0 1) (Pi.single 0 1) = 2 ∧
    outcome root 0 = false ∧ outcome root (Pi.single 0 1) = true := by decide +kernel

theorem root_pairing (x : Lattice) : pairing x root = x 0 + x 3 - 2 * x 2 := by
  simp [pairing, root_coordinates, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- At one-bit resolution the even diagonal term vanishes. The specified
root probe reads only its two neighbours in the E8 Gram diagram. This is
coordinate/readout locality, not a spatial propagation or gate-cost theorem. -/
theorem root_resolution (x : Lattice) :
    outcome root x = decide (¬ (2 : ℤ) ∣ (x 0 + x 3)) := by
  unfold outcome
  rw [root_pairing]
  have hh : (2 : ℤ) ∣ (x 0 + x 3 - 2 * x 2) ↔ (2 : ℤ) ∣ (x 0 + x 3) := by
    simp only [Int.dvd_iff_emod_eq_zero]
    omega
  simp only [hh]

/-- Any implementation reading this actual lattice pairing must couple the
input to the probe output. This is a task theorem, not a vacuum schedule. -/
theorem root_readout_requires_coupling (F : State → State) (hread : ReadsPairing root F) :
    ¬ ∀ (x : Lattice) (t : Fin 43), (F (x,root,t)).2.2 = (F (0,root,t)).2.2 := by
  intro h
  have hh := h (Pi.single 0 1) 0
  rw [hread (Pi.single 0 1), hread 0, root_example.2.2.1, root_example.2.2.2] at hh
  norm_num at hh

end PMAction.MatchedLatticeProbe
