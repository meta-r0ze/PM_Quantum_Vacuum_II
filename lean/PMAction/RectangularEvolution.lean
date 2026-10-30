import PMAction.ControllerHamiltonian

/-! Exact evolution transports through a rectangular intertwiner.
No continuum limit or surjectivity of the representation is assumed. -/
noncomputable section
namespace PMAction.RectangularEvolution
open Matrix
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def blockHom : (Matrix a a ℂ × Matrix b b ℂ) →+* Matrix (a ⊕ b) (a ⊕ b) ℂ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_one' := fromBlocks_one
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_add' p q := by ext i j; cases i <;> cases j <;> simp
  map_mul' p q := by simp [fromBlocks_multiply]

lemma blockHom_continuous : Continuous (blockHom (a := a) (b := b)) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j
  · exact continuous_fst.matrix_elem _ _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_snd.matrix_elem _ _

open scoped Matrix.Norms.Operator

lemma exp_block (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    NormedSpace.exp (fromBlocks A 0 0 B) =
      fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  have he := NormedSpace.map_exp (blockHom (a := a) (b := b)) blockHom_continuous (A,B)
  change fromBlocks (NormedSpace.exp (A,B)).1 0 0 (NormedSpace.exp (A,B)).2 =
    NormedSpace.exp (fromBlocks A 0 0 B) at he
  have hf : (NormedSpace.exp (A,B)).1=NormedSpace.exp A :=
    NormedSpace.map_exp (RingHom.fst (Matrix a a ℂ) (Matrix b b ℂ)) continuous_fst (A,B)
  have hg : (NormedSpace.exp (A,B)).2=NormedSpace.exp B :=
    NormedSpace.map_exp (RingHom.snd (Matrix a a ℂ) (Matrix b b ℂ)) continuous_snd (A,B)
  rw [hf,hg] at he
  exact he.symm

/-- Functional calculus follows the actual rectangular operator identity. -/
theorem exponential (A : Matrix a a ℂ) (B : Matrix b b ℂ) (E : Matrix a b ℂ)
    (h : A*E=E*B) : NormedSpace.exp A * E = E * NormedSpace.exp B := by
  let D : Matrix (a ⊕ b) (a ⊕ b) ℂ := fromBlocks A 0 0 B
  let X : Matrix (a ⊕ b) (a ⊕ b) ℂ := fromBlocks 0 E 0 0
  have hc : SemiconjBy X D D := by
    change X*D=D*X
    simp [X,D,fromBlocks_multiply,h]
  have he := hc.exp_right
  change X*NormedSpace.exp D=NormedSpace.exp D*X at he
  rw [show D=fromBlocks A 0 0 B from rfl,exp_block] at he
  have hab := congrArg Matrix.toBlocks₁₂ he
  simpa [X,fromBlocks_multiply] using hab.symm

/-- Real-time phases, or real transfer parameters, use the same exact bridge. -/
theorem scaled (A : Matrix a a ℂ) (B : Matrix b b ℂ) (E : Matrix a b ℂ)
    (h : A*E=E*B) (z : ℂ) :
    NormedSpace.exp (z • A) * E = E * NormedSpace.exp (z • B) := by
  apply exponential
  simp [Matrix.smul_mul, Matrix.mul_smul, h]

end PMAction.RectangularEvolution
