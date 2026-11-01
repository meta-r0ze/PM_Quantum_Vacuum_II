import PMAction.StateIdentification

/-! Exact readout under independent tensor factors and successive encodings.
These identities do not supply the physical factors or their preparation. -/
noncomputable section
namespace PMAction.NativeObservation
open Matrix
open scoped Kronecker
variable {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]

theorem tensor {E : Matrix a b ℂ} {F : Matrix c d ℂ}
    {A : Matrix a a ℂ} {B : Matrix b b ℂ}
    {C : Matrix c c ℂ} {D : Matrix d d ℂ}
    (h : Obs E A B) (k : Obs F C D) : Obs (E ⊗ₖ F) (A ⊗ₖ C) (B ⊗ₖ D) := by
  constructor
  · simp only [← mul_kronecker_mul, h.1, k.1]
  · simp only [conjTranspose_kronecker, ← mul_kronecker_mul, h.2, k.2]

theorem compose {E : Matrix a b ℂ} {F : Matrix b c ℂ}
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} {C : Matrix c c ℂ}
    (h : Obs E A B) (k : Obs F B C) : Obs (E * F) A C := by
  constructor
  · rw [← Matrix.mul_assoc, h.1, Matrix.mul_assoc, k.1, ← Matrix.mul_assoc]
  · rw [conjTranspose_mul, Matrix.mul_assoc, h.2, ← Matrix.mul_assoc, k.2,
      Matrix.mul_assoc]

/-- Exact readout is unchanged by bijective changes of native/observed labels. -/
theorem relabel {E : Matrix a b ℂ} {A : Matrix a a ℂ} {B : Matrix b b ℂ}
    (e : c ≃ a) (f : d ≃ b) (h : Obs E A B) :
    Obs (E.submatrix e f) (A.submatrix e e) (B.submatrix f f) := by
  constructor
  · rw [submatrix_mul_equiv, submatrix_mul_equiv, h.1]
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, h.2]

omit [Fintype b] [Fintype d] in
theorem tensor_isometry [DecidableEq b] [DecidableEq d]
    (E : Matrix a b ℂ) (F : Matrix c d ℂ) (h : Eᴴ * E = 1) (k : Fᴴ * F = 1) :
    (E ⊗ₖ F)ᴴ * (E ⊗ₖ F) = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, h, k, one_kronecker_one]

omit [Fintype c] [Fintype d] in
theorem compose_isometry [DecidableEq b] [DecidableEq c]
    (E : Matrix a b ℂ) (F : Matrix b c ℂ) (h : Eᴴ * E = 1) (k : Fᴴ * F = 1) :
    (E * F)ᴴ * (E * F) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ E, h, Matrix.one_mul, k]

end PMAction.NativeObservation
