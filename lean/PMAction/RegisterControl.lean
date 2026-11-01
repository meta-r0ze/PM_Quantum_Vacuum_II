import PMAction.RegisterPrograms
import PMAction.InvolutionComparison
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Joint controls on the occupied two-bank sector

Any supplied permutation of the complete label pair extends to a reversible
Boolean configuration update and is observed exactly. Invalid occupation
configurations are fixed. Thus a controlled operation may depend jointly on
spinor/spatial and payload/reference labels without adding an abstract tensor
factor; any extra branch must occur in the actual first-bank label space.
Spectral phases of involutions have exact readout and are unitary on every
configuration. This is a finite construction, not primitive E8 admission,
geometric locality, branch preparation, or a minimum implementation price.
-/
noncomputable section
namespace PMAction.RegisterControl
open Matrix NativeObservation IndependentRegisters InvolutionComparison
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def ports : (a × b) ↪ Configuration a b := ⟨encode, encode_injective⟩
def extend (e : Equiv.Perm (a × b)) : Equiv.Perm (Configuration a b) := e.viaEmbedding ports

omit [Fintype a] [Fintype b] in
theorem extend_encode (e : Equiv.Perm (a × b)) (p : a × b) :
    extend e (encode p) = encode (e p) := Equiv.Perm.viaEmbedding_apply e ports p

theorem observed (e : Equiv.Perm (a × b)) :
    Obs embedding ((extend e).permMatrix ℂ) (e.permMatrix ℂ) :=
  ⟨FiniteEncoding.intertwining encode e _ (extend_encode e),
   FiniteEncoding.readout_intertwining encode e _ (extend_encode e)⟩

omit [Fintype a] [Fintype b] in
theorem outside_fixed (e : Equiv.Perm (a × b)) (q : Configuration a b) (h : ¬ Valid q) :
    extend e q = q := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨p,hp⟩
  exact h ((valid_iff q).mpr ⟨p,hp⟩)

theorem occupation_conserved (e : Equiv.Perm (a × b)) (q : Configuration a b) :
    occupied (extend e q) = occupied q := by
  classical
  by_cases hq : Valid q
  · obtain ⟨p, rfl⟩ := (valid_iff q).mp hq
    rw [extend_encode, occupied_encode, occupied_encode]
  · rw [outside_fixed e q hq]

omit [Fintype a] [Fintype b] in
theorem extend_involutive (e : Equiv.Perm (a × b)) (he : Function.Involutive e) :
    Function.Involutive (extend e) := by
  have hs : e * e = 1 := by apply Equiv.ext; intro i; exact he i
  have hh := congrArg (Equiv.Perm.viaEmbeddingHom ports) hs
  simp only [map_mul, map_one, Equiv.Perm.viaEmbeddingHom_apply] at hh
  intro q
  exact congrArg (fun d : Equiv.Perm (Configuration a b) => d q) hh

theorem phase_observed (e : Equiv.Perm (a × b)) (z : ℂ) :
    Obs embedding (phase ((extend e).permMatrix ℂ) z) (phase (e.permMatrix ℂ) z) := by
  have he := observed e
  exact NativeObservation.add
    (NativeObservation.smul (1/2) (NativeObservation.add NativeObservation.one he))
    (NativeObservation.smul z
      (NativeObservation.smul (1/2) (NativeObservation.sub NativeObservation.one he)))

theorem phase_unitary (e : Equiv.Perm (a × b)) (he : Function.Involutive e)
    (z : ℂ) (hz : star z * z = 1) :
    phase ((extend e).permMatrix ℂ) z ∈ unitary (Matrix (Configuration a b) (Configuration a b) ℂ) :=
  InvolutionComparison.phase_unitary _
    (RootTransferPhase.permutation_square _ (extend_involutive e he))
    (RootTransferPhase.permutation_hermitian _ (extend_involutive e he)) z hz

end PMAction.RegisterControl
