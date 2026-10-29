import PMAction.IsometricDynamics
import PMAction.RootWalkEncoding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The existing reference walk in actual carrier modes

The on-site carrier/spinor interface extends the constructed two-stream walk
unitarily, with identity on unused modes. Its exact packet evolution, all
iterates, norm and comparison response agree. This is the reference protocol,
not an identification with the complete two-wall corrected vacuum split.
The coherent frame and transported controls are not priced as free gates.
-/
noncomputable section
namespace PMAction.RootCarrierWalk
open Matrix CommonResponse
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X]
abbrev C := ActualRootRepair.C

def embedding : Matrix (X × C) (X × Fin 4) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ RootWalkEncoding.interface

theorem isometry : (embedding (X := X))ᴴ * (embedding (X := X)) = (1 : Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
  simp [embedding, conjTranspose_kronecker, ← mul_kronecker_mul, RootWalkEncoding.isometry]

lemma embedding_action (ψ : X × Fin 4 → ℂ) (x : X) (c : C) :
    (embedding *ᵥ ψ) (x,c) = (RootWalkEncoding.interface *ᵥ (fun a => ψ (x,a))) c := by
  simp [embedding, mulVec, dotProduct, Fintype.sum_prod_type, one_apply]

def field (live record : X → Fin 2 → ℂ) : X × C → ℂ :=
  fun p => ActualRootRepair.pack (live p.1) (record p.1) p.2

lemma encoded_field (live record : X → Fin 2 → ℂ) :
    embedding *ᵥ WalkReferenceProtocol.field live record = field live record := by
  ext p
  rcases p with ⟨x,c⟩
  rw [embedding_action]
  exact congrFun (RootWalkEncoding.encoded_packet (live x) (record x)) c

def update (o : X) (e : Equiv.Perm X) : Matrix (X × C) (X × C) ℂ :=
  IsometricDynamics.extend embedding (WalkReferenceProtocol.update o e)

theorem update_unitary (o : X) (e : Equiv.Perm X) :
    update o e ∈ unitary (Matrix (X × C) (X × C) ℂ) :=
  IsometricDynamics.unitary _ isometry _ (WalkReferenceProtocol.update_unitary o e)

theorem intertwining (o : X) (e : Equiv.Perm X) :
    update o e * embedding = embedding * WalkReferenceProtocol.update o e :=
  IsometricDynamics.intertwining _ isometry _

theorem encoded_step (o : X) (e : Equiv.Perm X) (ψ : X × Fin 4 → ℂ) :
    update o e *ᵥ (embedding *ᵥ ψ) = embedding *ᵥ (WalkReferenceProtocol.update o e *ᵥ ψ) := by
  rw [mulVec_mulVec, intertwining, ← mulVec_mulVec]

theorem iterations (o : X) (e : Equiv.Perm X) (N : ℕ) :
    (update o e)^N * embedding = embedding * (WalkReferenceProtocol.update o e)^N :=
  IsometricDynamics.iterations _ isometry _ N

theorem population (ψ : X × Fin 4 → ℂ) : nsq (embedding *ᵥ ψ) = nsq ψ :=
  IsometricDynamics.population _ isometry ψ

theorem response (o : X) (e : Equiv.Perm X) (ψ : X × Fin 4 → ℂ) :
    stateFlag (update o e) (embedding *ᵥ ψ) = stateFlag (WalkReferenceProtocol.update o e) ψ :=
  IsometricDynamics.response _ isometry _ ψ

lemma walk_field_step (o : X) (e : Equiv.Perm X) (live record : X → Fin 2 → ℂ) :
    WalkReferenceProtocol.update o e *ᵥ WalkReferenceProtocol.field live record =
      WalkReferenceProtocol.field
        (fun x => if x=o then record (e x) else live (e⁻¹ x))
        (fun x => if x=o then live (e⁻¹ x) else record (e x)) := by
  ext p
  rcases p with ⟨x,a⟩
  rw [WalkReferenceProtocol.update_action]
  by_cases hx : x=o <;> simp [WalkReferenceProtocol.field, hx]

/-- Exactly the same two incoming streams and retained record, now on actual carriers. -/
theorem field_step (o : X) (e : Equiv.Perm X) (live record : X → Fin 2 → ℂ) :
    update o e *ᵥ field live record =
      field (fun x => if x=o then record (e x) else live (e⁻¹ x))
        (fun x => if x=o then live (e⁻¹ x) else record (e x)) := by
  rw [← encoded_field, encoded_step, walk_field_step, encoded_field]

/-- The local repair uses an arriving reference; no clean record is created by encoding. -/
theorem reference_arrival (o : X) (e : Equiv.Perm X) (live record : X → Fin 2 → ℂ)
    (r : Fin 2 → ℂ) (hclean : record (e o)=r) :
    (fun c => (update o e *ᵥ field live record) (o,c)) =
      ActualRootRepair.pack r (live (e⁻¹ o)) := by
  rw [field_step]
  simp [field, hclean]

/-- An on-site frame cannot create a new off-site dependency. The identity
extension may add only an on-site term. -/
theorem offsite_zero (U : Matrix (X × Fin 4) (X × Fin 4) ℂ) (x y : X) (hxy : x ≠ y)
    (hU : ∀ a b, U (x,a) (y,b)=0) (c d : C) :
    IsometricDynamics.extend embedding U (x,c) (y,d) = 0 := by
  have hmain : ((embedding (X := X)) * U * (embedding (X := X))ᴴ) (x,c) (y,d) = 0 := by
    simp [embedding, mul_apply, conjTranspose_apply, Fintype.sum_prod_type, one_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : y=z
    · subst z
      simp [hU]
    · simp [hz]
  have hp : (embedding (X := X)) * embeddingᴴ =
      (1 : Matrix X X ℂ) ⊗ₖ (RootWalkEncoding.interface * RootWalkEncoding.interfaceᴴ) := by
    simp [embedding, conjTranspose_kronecker, ← mul_kronecker_mul]
  have hk : IsometricDynamics.complement embedding (x,c) (y,d) = 0 := by
    rw [IsometricDynamics.complement, hp]
    simp [one_apply, hxy]
  simp only [IsometricDynamics.extend, Matrix.add_apply, hmain, hk, add_zero]

end PMAction.RootCarrierWalk
