import PMAction.RegisterInteraction
import PMAction.TensorKernel
import PMAction.ChiralityConvention
import PMAction.GaugeRecordEmbedding

/-!
# Chiral charge action on zero modes and on the existing reference

The native two-bank chiral-charge operator has the specified projector × charge
readout for all amplitudes. On the actual zero kernel this is second-wall
selection, also for entangled spinor/payload states, and it preserves that kernel.
The exchanged reference is retained on the spinor side while its supplied
payload transforms by the charge. No global identification of wall and packet
tags is imposed. The charge, reference value/source and physical weak-current
attachment remain supplied; no mediator, statistics or event tariff is selected.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ChiralRegisterCurrent
open Matrix ConcreteFermion WallChiralCurrent
open scoped Kronecker
variable {b : Type*} [Fintype b] [DecidableEq b]

def wallSelector : Matrix Sites Sites ℂ := fromBlocks 0 0 0 1

theorem wall_action (ψ : Sites → ℂ) : wallSelector *ᵥ ψ = secondWall ψ := by
  ext s
  cases s <;> simp [wallSelector, fromBlocks_mulVec, secondWall]

theorem action_on_zero (B : Matrix b b ℂ) (ψ : Sites × b → ℂ)
    (h : (hamiltonian 0 0 ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0) :
    (projector ⊗ₖ B) *ᵥ ψ = (wallSelector ⊗ₖ B) *ᵥ ψ := by
  apply TensorKernel.agree_on_kernel (hamiltonian 0 0) projector wallSelector B _ ψ h
  intro v hv
  exact (kernel_projector v hv).trans (wall_action v).symm

theorem preserves_zero (B : Matrix b b ℂ) (ψ : Sites × b → ℂ)
    (h : (hamiltonian 0 0 ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0) :
    (hamiltonian 0 0 ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ((projector ⊗ₖ B) *ᵥ ψ) = 0 :=
  TensorKernel.map_kernel _ _ B projected_zero_mode ψ h

theorem native_readout_on_zero (c : Fin 3) (B : Matrix b b ℂ) (hB : B.IsHermitian)
    (ψ : RegisterVacuum.Config (b := b) c → ℂ)
    (h : (hamiltonian 0 0 ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ
      ((RegisterVacuum.embedding c)ᴴ *ᵥ ψ) = 0) :
    (RegisterVacuum.embedding c)ᴴ *ᵥ (RegisterInteraction.current c B *ᵥ ψ) =
      (wallSelector ⊗ₖ B) *ᵥ ((RegisterVacuum.embedding c)ᴴ *ᵥ ψ) := by
  rw [NativeObservation.readout (RegisterInteraction.current_observed c B hB) ψ]
  exact action_on_zero B _ h

def referenceInput (r : Fin 2 → ℂ) (w : b → ℂ) : Sites × b → ℂ :=
  fun q => ChiralityConvention.physicalBackground r q.1 * w q.2

omit [DecidableEq b] in
/-- The existing reference is retained by the chiral projector, while its
payload charge is allowed to act. Neither input is prepared for free here. -/
theorem reference_action (B : Matrix b b ℂ) (r : Fin 2 → ℂ) (w : b → ℂ) :
    (projector ⊗ₖ B) *ᵥ referenceInput r w = referenceInput r (B *ᵥ w) := by
  ext ⟨i,j⟩
  change ((projector ⊗ₖ B) *ᵥ
    (fun q : Sites × b => ChiralityConvention.physicalBackground r q.1 * w q.2)) (i,j) = _
  rw [GaugeRecordEmbedding.tensor_packet, ChiralityConvention.weak_acts_on_reference]
  rfl

theorem native_reference_action (c : Fin 3) (B : Matrix b b ℂ) (hB : B.IsHermitian)
    (r : Fin 2 → ℂ) (w : b → ℂ) :
    RegisterInteraction.current c B *ᵥ (RegisterVacuum.embedding c *ᵥ referenceInput r w) =
      RegisterVacuum.embedding c *ᵥ referenceInput r (B *ᵥ w) := by
  rw [mulVec_mulVec, (RegisterInteraction.current_observed c B hB).1,
    ← mulVec_mulVec, reference_action]

end PMAction.ChiralRegisterCurrent
