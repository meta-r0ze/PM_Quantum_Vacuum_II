import PMAction.StateIdentification

/-! The four-phase schedule is unitary even on coherent clock amplitudes.
This is a finite clock register construction; initialization, capacity, clock
calibration and event prices are not inferred by the unitary identities. -/
noncomputable section
namespace PMAction.ClockDynamics
open Matrix
variable {a : Type*} [Fintype a] [DecidableEq a]

def phaseBack : Equiv.Perm (Fin 4 × a) where
  toFun q := (q.1 - 1, q.2)
  invFun q := (q.1 + 1, q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

def controlled (F : Fin 4 → Matrix a a ℂ) : Matrix (Fin 4 × a) (Fin 4 × a) ℂ :=
  (blockDiagonal F).submatrix (Equiv.prodComm (Fin 4) a) (Equiv.prodComm (Fin 4) a)

theorem controlled_unitary (F : Fin 4 → Matrix a a ℂ)
    (h : ∀ j, F j ∈ unitary (Matrix a a ℂ)) : controlled F ∈ unitary _ := by
  have hl : (fun j => (F j)ᴴ * F j) = 1 := funext (fun j => (h j).1)
  have hr : (fun j => F j * (F j)ᴴ) = 1 := funext (fun j => (h j).2)
  constructor
  · change (controlled F)ᴴ * controlled F = 1
    rw [controlled, conjTranspose_submatrix, blockDiagonal_conjTranspose,
      submatrix_mul_equiv, ← blockDiagonal_mul, hl, blockDiagonal_one, submatrix_one_equiv]
  · change controlled F * (controlled F)ᴴ = 1
    rw [controlled, conjTranspose_submatrix, blockDiagonal_conjTranspose,
      submatrix_mul_equiv, ← blockDiagonal_mul, hr, blockDiagonal_one, submatrix_one_equiv]

theorem clock_factorization (F : Fin 4 → Matrix a a ℂ) :
    Clock.clocked F = (phaseBack (a := a)).permMatrix ℂ * controlled F := by
  ext q r
  change _ = ((phaseBack (a := a)).permMatrix ℂ *ᵥ (fun s => controlled F s r)) q
  rw [permMatrix_mulVec]
  change (if q.1 = r.1 + 1 then F r.1 q.2 r.2 else 0) =
    if q.1 - 1 = r.1 then F (q.1 - 1) q.2 r.2 else 0
  by_cases h : q.1 = r.1 + 1
  · simp [h]
  · have hn : q.1 - 1 ≠ r.1 := by
      intro he
      exact h (sub_eq_iff_eq_add.mp he)
    simp [h, hn]

theorem clocked_unitary (F : Fin 4 → Matrix a a ℂ)
    (h : ∀ j, F j ∈ unitary (Matrix a a ℂ)) : Clock.clocked F ∈ unitary _ := by
  have hp : (phaseBack (a := a)).permMatrix ℂ ∈ unitary (Matrix (Fin 4 × a) (Fin 4 × a) ℂ) := by
    constructor <;> simp [star_eq_conjTranspose, ← permMatrix_mul]
  rw [clock_factorization]
  exact (unitary _).mul_mem hp (controlled_unitary F h)

end PMAction.ClockDynamics
