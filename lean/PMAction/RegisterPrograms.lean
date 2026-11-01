import PMAction.IndependentRegisters
import PMAction.TensorObservation

/-! Coherent operator expressions built from actual bank relabelings.
The expressions preserve exact configuration readout under sums, products,
adjoints and evolution. Coherent admission and event costs are not inferred
from this algebra, and sums are not charged as single permutation events. -/
noncomputable section
namespace PMAction.RegisterPrograms
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker

inductive Program (a b : Type*) where
  | one
  | gate (e : Equiv.Perm a) (f : Equiv.Perm b)
  | add (p q : Program a b)
  | mul (p q : Program a b)
  | smul (z : ℂ) (p : Program a b)
  | adjoint (p : Program a b)

variable {a b : Type*}

def evaluate {n : Type*} [Fintype n] [DecidableEq n]
    (gates : Equiv.Perm a → Equiv.Perm b → Matrix n n ℂ) : Program a b → Matrix n n ℂ
  | .one => 1
  | .gate e f => gates e f
  | .add p q => evaluate gates p + evaluate gates q
  | .mul p q => evaluate gates p * evaluate gates q
  | .smul z p => z • evaluate gates p
  | .adjoint p => (evaluate gates p)ᴴ

theorem evaluate_observed {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (E : Matrix n m ℂ)
    (gates : Equiv.Perm a → Equiv.Perm b → Matrix n n ℂ)
    (targets : Equiv.Perm a → Equiv.Perm b → Matrix m m ℂ)
    (h : ∀ e f, Obs E (gates e f) (targets e f)) (p : Program a b) :
    Obs E (evaluate gates p) (evaluate targets p) := by
  induction p with
  | one => exact NativeObservation.one
  | gate e f => exact h e f
  | add p q hp hq => exact NativeObservation.add hp hq
  | mul p q hp hq => exact NativeObservation.mul hp hq
  | smul z p hp => exact NativeObservation.smul z hp
  | adjoint p hp => exact NativeObservation.star hp

variable [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def configuration (p : Program a b) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  evaluate (fun e f => (update e f).permMatrix ℂ) p

def product (p : Program a b) : Matrix (a × b) (a × b) ℂ :=
  evaluate (fun e f => e.permMatrix ℂ ⊗ₖ f.permMatrix ℂ) p

theorem observed (p : Program a b) : Obs embedding (configuration p) (product p) :=
  evaluate_observed _ _ _ tensor_observed p

/-- Evolution has exact readout on every ambient configuration amplitude. -/
theorem evolution_readout (p : Program a b) (z : ℂ) (ψ : Configuration a b → ℂ) :
    embeddingᴴ *ᵥ (NormedSpace.exp (z • configuration p) *ᵥ ψ) =
      NormedSpace.exp (z • product p) *ᵥ (embeddingᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (observed p) z) ψ

end PMAction.RegisterPrograms
