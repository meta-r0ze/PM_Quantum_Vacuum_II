import PMAction.ConcreteFermion
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Star.Unitary

/-! Finite, exactly unitary neighboring-site factors for a split update.
The full finite-tick spectrum is not inferred from the Hamiltonian spectrum. -/
noncomputable section
namespace PMAction.LocalUnitary
open Matrix ConcreteFermion
open scoped Kronecker

/-- Neighbor coefficient for cos(k) beta - sin(k) alpha_j. -/
def coefficient (j : Fin 3) : Spin :=
  (1/2 : ℂ) • beta + (Complex.I/2) • alpha j

set_option maxHeartbeats 1000000 in
theorem coefficient_relations (j : Fin 3) :
    coefficient j*coefficient j=0 ∧
    coefficient j*(coefficient j)ᴴ+(coefficient j)ᴴ*coefficient j=1 := by
  constructor <;> fin_cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [coefficient, beta, alpha, mul_apply, vecMul, dotProduct,
      conjTranspose_apply, Fin.sum_univ_four] <;> ring_nf <;> norm_num [Complex.I_sq, map_ofNat]

/-- A chosen spatial permutation and its inverse, with internal nilpotent links. -/
def neighbor {X : Type*} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) (j : Fin 3) :
    Matrix (X × Fin 4) (X × Fin 4) ℂ :=
  e.permMatrix ℂ ⊗ₖ coefficient j + (e.permMatrix ℂ)ᴴ ⊗ₖ (coefficient j)ᴴ

theorem neighbor_hermitian {X : Type*} [Fintype X] [DecidableEq X]
    (e : Equiv.Perm X) (j : Fin 3) : (neighbor e j).IsHermitian := by
  simp [IsHermitian, neighbor, conjTranspose_add, conjTranspose_kronecker, add_comm]

theorem neighbor_square {X : Type*} [Fintype X] [DecidableEq X]
    (e : Equiv.Perm X) (j : Fin 3) : neighbor e j*neighbor e j=1 := by
  have hc := coefficient_relations j
  have hcc : (coefficient j)ᴴ*(coefficient j)ᴴ=0 := by
    rw [← conjTranspose_mul, hc.1, conjTranspose_zero]
  have hs : e.permMatrix ℂ*(e.permMatrix ℂ)ᴴ=1 := by
    rw [conjTranspose_permMatrix, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  have ht : (e.permMatrix ℂ)ᴴ*e.permMatrix ℂ=1 := by
    rw [conjTranspose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  simp only [neighbor, add_mul, mul_add, ← mul_kronecker_mul, hc.1, hcc,
    kronecker_zero, zero_add, add_zero, hs, ht]
  rw [← kronecker_add, add_comm, hc.2, one_kronecker_one]

/-- Closed-form unitary rotation of a Hermitian involution. -/
def rotation {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (τ : ℝ) : Matrix n n ℂ :=
  (Real.cos τ : ℂ) • 1 + (Complex.I*(Real.sin τ : ℂ)) • B

theorem rotation_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (τ : ℝ) (hb : B.IsHermitian) (h2 : B*B=1) :
    rotation B τ ∈ unitary (Matrix n n ℂ) := by
  let c : ℂ := Real.cos τ
  let d : ℂ := Complex.I*(Real.sin τ : ℂ)
  have ht : c^2-d^2=1 := by
    dsimp [c,d]
    have h : (Real.sin τ : ℂ)^2+(Real.cos τ : ℂ)^2=1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq τ
    calc
      _ = (Real.sin τ : ℂ)^2+(Real.cos τ : ℂ)^2 := by ring_nf; simp
      _ = 1 := h
  have hadj : (rotation B τ)ᴴ=c • 1-d • B := by
    dsimp [c,d]
    simp only [rotation, conjTranspose_add, conjTranspose_smul, conjTranspose_one,
      hb.eq, RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_smul, sub_eq_add_neg]
    ext i j
    simp [Complex.real_smul]
  have hleft : (c • (1 : Matrix n n ℂ)-d • B)*(c • 1+d • B)=1 := by
    calc
      _ = (c^2-d^2) • (1 : Matrix n n ℂ) := by
        simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
          one_mul, mul_one, h2]
        module
      _ = 1 := by rw [ht, one_smul]
  have hright : (c • (1 : Matrix n n ℂ)+d • B)*(c • 1-d • B)=1 := by
    calc
      _ = (c^2-d^2) • (1 : Matrix n n ℂ) := by
        simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
          one_mul, mul_one, h2]
        module
      _ = 1 := by rw [ht, one_smul]
  exact ⟨by change (rotation B τ)ᴴ*rotation B τ=1; rw [hadj]; exact hleft,
    by change rotation B τ*(rotation B τ)ᴴ=1; rw [hadj]; exact hright⟩

def step {X : Type*} [Fintype X] [DecidableEq X]
    (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) := rotation (neighbor e j) τ

theorem step_unitary {X : Type*} [Fintype X] [DecidableEq X]
    (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    step e j τ ∈ unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) :=
  rotation_unitary _ _ (neighbor_hermitian e j) (neighbor_square e j)

/-- Only the current site and the two permutation neighbors are read. -/
theorem step_local {X : Type*} [Fintype X] [DecidableEq X]
    (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ)
    (ψ φ : X × Fin 4 → ℂ) (x : X)
    (h : ∀ y, y=x ∨ y=e x ∨ y=e.symm x → ∀ a, ψ (y,a)=φ (y,a)) :
    ∀ a, (step e j τ*ᵥψ) (x,a)=(step e j τ*ᵥφ) (x,a) := by
  intro a
  simp only [mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y.1=x ∨ y.1=e x ∨ y.1=e.symm x
  · rw [h y.1 hy y.2]
  · have h0 : (step e j τ) (x,a) y=0 := by
      have hx : x ≠ y.1 := fun hh => hy (Or.inl hh.symm)
      have hp : e x ≠ y.1 := fun hh => hy (Or.inr (Or.inl hh.symm))
      have hm : e.symm x ≠ y.1 := fun hh => hy (Or.inr (Or.inr hh.symm))
      simp [step, rotation, neighbor, kronecker_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, hx, hp, hm, conjTranspose_permMatrix,
        Equiv.toPEquiv_apply, Prod.ext_iff]
    rw [h0, zero_mul, zero_mul]

end PMAction.LocalUnitary
