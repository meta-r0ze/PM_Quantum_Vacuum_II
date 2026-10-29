import PMAction.LocalUnitary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Exact composition and transport identities for the split's involution rotations. -/
noncomputable section
namespace PMAction.RotationAlgebra
open Matrix LocalUnitary
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem rotation_zero (B : Matrix n n ℂ) : rotation B 0=1 := by simp [rotation]

theorem rotation_add (B : Matrix n n ℂ) (hB : B*B=1) (s t : ℝ) :
    rotation B s*rotation B t=rotation B (s+t) := by
  simp only [rotation, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hB,
    Real.cos_add, Real.sin_add, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  match_scalars <;> (ring_nf; all_goals simp [sub_eq_add_neg])

theorem rotation_nsmul (B : Matrix n n ℂ) (hB : B*B=1) (t : ℝ) (m : ℕ) :
    rotation B t^m=rotation B ((m : ℝ)*t) := by
  induction m with
  | zero => simp [rotation_zero]
  | succ m ih =>
    rw [pow_succ, ih, rotation_add B hB]
    congr 1
    push_cast
    ring

theorem rotation_neg (B : Matrix n n ℂ) (t : ℝ) : rotation B (-t)=rotation (-B) t := by
  simp only [rotation, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, mul_neg,
    neg_smul, smul_neg]

theorem rotation_adjoint (B : Matrix n n ℂ) (hB : B.IsHermitian) (t : ℝ) :
    (rotation B t)ᴴ=rotation B (-t) := by
  simp only [rotation, conjTranspose_add, conjTranspose_smul, conjTranspose_one,
    hB.eq, RCLike.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, mul_neg, neg_smul]

theorem rotation_transport (B A : Matrix n n ℂ) (hBA : B*A=-(A*B)) (t : ℝ) :
    rotation B (-t)*A=A*rotation B t := by
  simp only [rotation, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, mul_neg,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hBA,
    neg_smul, neg_mul, smul_neg, neg_neg]

end PMAction.RotationAlgebra
