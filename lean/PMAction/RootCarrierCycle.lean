import PMAction.RootCarrierWalk
import PMAction.WalkReferenceCycle

/-!
# The finite prepared-reference horizon in actual carrier amplitudes

The old exact stream interpreter is now realized through the actual-carrier
walk. N prepared ring references support N repairs; the next trial returns
old input. The representation change cannot create or renew a clean record.
-/
noncomputable section
namespace PMAction.RootCarrierCycle
open Matrix
variable {X : Type*} [Fintype X] [DecidableEq X]

def amplitude (s : WalkReferenceCycle.State X) : X × ActualRootRepair.C → ℂ :=
  RootCarrierWalk.field (fun x => (s x).1) (fun x => (s x).2)

lemma encoding (s : WalkReferenceCycle.State X) :
    RootCarrierWalk.embedding *ᵥ WalkReferenceCycle.amplitude s = amplitude s :=
  RootCarrierWalk.encoded_field _ _

theorem state_step (o : X) (e : Equiv.Perm X) (s : WalkReferenceCycle.State X) :
    RootCarrierWalk.update o e *ᵥ amplitude s = amplitude (WalkReferenceCycle.advance o e s) := by
  rw [← encoding, RootCarrierWalk.encoded_step, WalkReferenceCycle.intertwining, encoding]

theorem iterations (o : X) (e : Equiv.Perm X) (t : ℕ) (s : WalkReferenceCycle.State X) :
    (fun ψ => RootCarrierWalk.update o e *ᵥ ψ)^[t] (amplitude s) =
      amplitude ((WalkReferenceCycle.advance o e)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, state_step, Function.iterate_succ_apply']

theorem ring_restores (R t : ℕ) (ht0 : 0<t) (ht : t≤R+1)
    (s : WalkReferenceCycle.State (Fin (R+1))) (reference : Fin 2 → ℂ)
    (hr : ∀ x, (s x).2=reference) (i : Fin 2) :
    ((fun ψ => RootCarrierWalk.update 0 (finRotate (R+1)) *ᵥ ψ)^[t] (amplitude s))
      (0,ActualRootRepair.label (.inl i)) = reference i := by
  rw [iterations]
  change ActualRootRepair.pack _ _ (ActualRootRepair.label (.inl i)) = reference i
  rw [ActualRootRepair.pack, ActualRootRepair.encoded_coordinate]
  exact congrFun (WalkReferenceCycle.ring_restores R t ht0 ht s reference hr) i

theorem first_return (R : ℕ) (s : WalkReferenceCycle.State (Fin (R+1))) (i : Fin 2) :
    ((fun ψ => RootCarrierWalk.update 0 (finRotate (R+1)) *ᵥ ψ)^[R+2] (amplitude s))
      (0,ActualRootRepair.label (.inl i)) = (s ((finRotate (R+1))⁻¹ 0)).1 i := by
  rw [iterations]
  change ActualRootRepair.pack _ _ (ActualRootRepair.label (.inl i)) = _
  rw [ActualRootRepair.pack, ActualRootRepair.encoded_coordinate]
  exact congrFun (WalkReferenceCycle.first_return R s) i

end PMAction.RootCarrierCycle
