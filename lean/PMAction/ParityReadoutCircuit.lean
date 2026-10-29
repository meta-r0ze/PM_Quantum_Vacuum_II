import PMAction.ReadoutGateBoundary
import PMArch.PersistenceEvents

/-!
# A parity-readout circuit using Paper I's three-leg witness

The six-gate word is an algebraic implementation in a specified bit library.
Role-addressed single-bit relabelings and exchange are supplied. Admissibility,
embedding and elementary physical tolls for these gates are not derived here.
The circuit makes four non-identity gate transitions on every input, although
its net effect can be the identity on that input. No minimal-cost claim is made.
-/
noncomputable section
namespace PMAction.ParityReadoutCircuit
open PMArch.Arity

abbrev Bits := Bool × Bool × Bool

inductive Gate | vertex | flip0 | flip1 | flip2 | exchange01
  deriving DecidableEq

def action : Gate → Bits → Bits
  | .vertex => PMArch.Arity.vertex
  | .flip0 => fun s => (!s.1,s.2.1,s.2.2)
  | .flip1 => fun s => (s.1,!s.2.1,s.2.2)
  | .flip2 => fun s => (s.1,s.2.1,!s.2.2)
  | .exchange01 => PMArch.Arity.s12

theorem action_involutive : ∀ g : Gate, Function.Involutive (action g) := by
  intro g
  change ∀ s : Bits, action g (action g s) = s
  cases g <;> decide +kernel

def execute : List Gate → Bits → Bits
  | [], s => s
  | g :: L, s => execute L (action g s)

def transitions : List Gate → Bits → ℕ
  | [], _ => 0
  | g :: L, s => (if action g s = s then 0 else 1) + transitions L (action g s)

def circuit : List Gate := [.vertex,.flip0,.flip1,.vertex,.flip2,.exchange01]

/-- The first two bits are retained; their parity is written into the third. -/
theorem circuit_correct : ∀ a b r : Bool,
    execute circuit (a,b,r) = (a,b,Bool.xor r (Bool.xor a b)) := by decide +kernel

theorem prepared_read (a b : Bool) : execute circuit (a,b,false) = (a,b,Bool.xor a b) := by
  rw [circuit_correct]
  simp

theorem circuit_uncompute : Function.Involutive (execute circuit) := by
  intro s
  rcases s with ⟨a,b,r⟩
  cases a <;> cases b <;> cases r <;> decide +kernel

theorem four_transitions : ∀ s : Bits, transitions circuit s = 4 := by decide +kernel

theorem six_instructions : circuit.length = 6 := by decide

/-- Net change is not an executed-work counter. Even inputs with zero parity
undergo four transitions in this implementation. -/
theorem net_idle_but_worked :
    execute circuit (false,false,false) = (false,false,false) ∧
      transitions circuit (false,false,false) = 4 := by decide +kernel

/-- Conditional ledger: one common supplied toll per changed bit gate, not
an identification of those gates with elementary E8 events. -/
def executionCost (toll : ℝ) (mass : Bits → ℝ) : ℝ :=
  ∑ s : Bits, mass s * (toll * (transitions circuit s : ℝ))

theorem law_independent_cost (toll : ℝ) (mass : Bits → ℝ) (hm : ∑ s, mass s = 1) :
    executionCost toll mass = 4 * toll := by
  unfold executionCost
  simp only [four_transitions, Nat.cast_ofNat]
  rw [← Finset.sum_mul, hm]
  ring

def coordinateBit (x : ℤ) : Bool := decide (¬ (2 : ℤ) ∣ x)

theorem parity_sum (a b : ℤ) :
    Bool.xor (coordinateBit a) (coordinateBit b) = coordinateBit (a+b) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    norm_num [coordinateBit, Int.dvd_iff_emod_eq_zero, Int.add_emod, ha, hb]

/-- The circuit's input bits are exactly those of the matched E8 root probe.
This identifies the Boolean function, not a physical encoding of the wires. -/
theorem matched_root_readout (x : SubstrateReflection.Lattice) :
    execute circuit (coordinateBit (x 0),coordinateBit (x 3),false) =
      (coordinateBit (x 0),coordinateBit (x 3),MatchedLatticeProbe.outcome SubstrateReflection.root x) := by
  rw [prepared_read, parity_sum, MatchedLatticeProbe.root_resolution]
  rfl

theorem matched_root_update (x : SubstrateReflection.Lattice) (r : Bool) :
    execute circuit (coordinateBit (x 0),coordinateBit (x 3),r) =
      (coordinateBit (x 0),coordinateBit (x 3),
        Bool.xor r (MatchedLatticeProbe.outcome SubstrateReflection.root x)) := by
  rw [circuit_correct, parity_sum, MatchedLatticeProbe.root_resolution]
  rfl

end PMAction.ParityReadoutCircuit
