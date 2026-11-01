import PMAction.TensorObservation

/-! Evolution on independent finite tensor factors. These are exact finite
matrix identities, with no continuum or physical factor-selection premise. -/
noncomputable section
namespace PMAction.TensorEvolution
open Matrix
open scoped Kronecker Matrix.Norms.Operator
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def rightHom : Matrix a a ℂ →+* Matrix (a × b) (a × b) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix b b ℂ)
  map_one' := one_kronecker_one
  map_zero' := by simp
  map_add' A B := by simp [add_kronecker]
  map_mul' A B := by simp [← mul_kronecker_mul]

def leftHom : Matrix b b ℂ →+* Matrix (a × b) (a × b) ℂ where
  toFun A := (1 : Matrix a a ℂ) ⊗ₖ A
  map_one' := one_kronecker_one
  map_zero' := by simp
  map_add' A B := by simp [kronecker_add]
  map_mul' A B := by simp [← mul_kronecker_mul]

theorem right_continuous : Continuous (rightHom (a := a) (b := b)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun A : Matrix a a ℂ => A i.1 j.1 * (1 : Matrix b b ℂ) i.2 j.2)
  fun_prop

theorem left_continuous : Continuous (leftHom (a := a) (b := b)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun A : Matrix b b ℂ => (1 : Matrix a a ℂ) i.1 j.1 * A i.2 j.2)
  fun_prop

theorem exp_right (A : Matrix a a ℂ) :
    NormedSpace.exp (A ⊗ₖ (1 : Matrix b b ℂ)) = NormedSpace.exp A ⊗ₖ 1 :=
  (NormedSpace.map_exp (rightHom (a := a) (b := b)) right_continuous A).symm

theorem exp_left (A : Matrix b b ℂ) :
    NormedSpace.exp ((1 : Matrix a a ℂ) ⊗ₖ A) = 1 ⊗ₖ NormedSpace.exp A :=
  (NormedSpace.map_exp (leftHom (a := a) (b := b)) left_continuous A).symm

theorem scaled_right (A : Matrix a a ℂ) (z : ℂ) :
    NormedSpace.exp (z • (A ⊗ₖ (1 : Matrix b b ℂ))) = NormedSpace.exp (z • A) ⊗ₖ 1 := by
  rw [← smul_kronecker, exp_right]

theorem scaled_left (A : Matrix b b ℂ) (z : ℂ) :
    NormedSpace.exp (z • ((1 : Matrix a a ℂ) ⊗ₖ A)) = 1 ⊗ₖ NormedSpace.exp (z • A) := by
  rw [← kronecker_smul, exp_left]

end PMAction.TensorEvolution
