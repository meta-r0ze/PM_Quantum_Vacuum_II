import PMAction.ScheduledReadout

/-!
# The missing observing-register coupling

Even arbitrary independent permutations of the two lattice registers and the
clock cannot write the separate readout bit. Thus the scheduled reading cycle
is not a word in that library. This is a result about the explicit product
encoding, not about every possible encoding into a larger E8 configuration.
-/
noncomputable section
namespace PMAction.ReadoutGateBoundary
open ScheduledReadout SubstrateReflection

/-- This contains the independent E8 root actions as a sublibrary; arbitrary
lattice permutations are allowed to make the restriction on the record clear. -/
inductive Gate
  | input (e : Equiv.Perm Lattice)
  | probe (e : Equiv.Perm Lattice)
  | clock (e : Equiv.Perm (Fin 43))

def root : Equiv.Perm Lattice where
  toFun := SubstrateReflection.reflect
  invFun := SubstrateReflection.reflect
  left_inv := SubstrateReflection.involutive
  right_inv := SubstrateReflection.involutive

def action : Gate → Equiv.Perm State
  | .input e => Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl _)) (Equiv.refl _)
  | .probe e => Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr e (Equiv.refl _))) (Equiv.refl _)
  | .clock e => Equiv.prodCongr (Equiv.refl _) e

def run : List Gate → Equiv.Perm State
  | [] => Equiv.refl _
  | g :: L => (action g).trans (run L)

theorem action_preserves_record (g : Gate) (s : State) : record (action g s) = record s := by
  cases g <;> rfl

theorem word_preserves_record (L : List Gate) (s : State) : record (run L s) = record s := by
  induction L generalizing s with
  | nil => rfl
  | cons g L ih =>
    change record (run L (action g s)) = record s
    rw [ih, action_preserves_record]

theorem known_words_cannot_read (L : List Gate) : ¬ ReadsRoot (run L) :=
  fixed_record_cannot_read _ (word_preserves_record L)

/-- The new coupling cannot be priced as one of these known root/clock gates,
or as a word of them, without a further encoding/interaction theorem. -/
theorem readCycle_not_generated (L : List Gate) : run L ≠ readCycle := by
  intro h
  have hn := known_words_cannot_read L
  rw [h] at hn
  exact hn readCycle_reads

end PMAction.ReadoutGateBoundary
