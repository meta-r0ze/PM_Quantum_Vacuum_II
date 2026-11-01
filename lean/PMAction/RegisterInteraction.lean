import PMAction.RegisterVacuum

/-!
# Two-bank coherent interactions and a native chiral-current construction

Swapping the bank names supplies a genuine second-bank hopping generator.
Hermitian products realize any supplied Hermitian tensor interaction, with
exact all-state readout, unitary evolution and total-occupation conservation.
The native gamma word supplies the spinor chiral projector; the payload charge
is supplied separately. This constructs a current operator, not a constraint
identifying the packet tag with the spinor wall, nor a physical charge selection.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RegisterInteraction
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def bankSwap : Configuration a b ≃ Configuration b a where
  toFun q := q ∘ Equiv.sumComm b a
  invFun q := q ∘ Equiv.sumComm a b
  left_inv q := by funext x; cases x <;> rfl
  right_inv q := by funext x; cases x <;> rfl

omit [Fintype a] [Fintype b] in
theorem swap_encode (p : a × b) : bankSwap (encode p) = encode p.swap := by
  funext x
  cases x <;> rfl

private theorem swap_embedding :
    (embedding (a := b) (b := a)).submatrix bankSwap (Equiv.prodComm a b) =
      embedding (a := a) (b := b) := by
  ext q p
  have hh : bankSwap q = encode p.swap ↔ q = encode p := by
    rw [← swap_encode]
    exact bankSwap.injective.eq_iff
  simp [IndependentRegisters.embedding, FiniteEncoding.matrix, hh]

omit [Fintype a] [Fintype b] [DecidableEq b] in
private theorem swap_tensor (B : Matrix b b ℂ) :
    (B ⊗ₖ (1 : Matrix a a ℂ)).submatrix (Equiv.prodComm a b) (Equiv.prodComm a b) =
      (1 : Matrix a a ℂ) ⊗ₖ B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [mul_comm]

def payload (B : Matrix b b ℂ) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  (RegisterHamiltonian.generator (b := a) B).submatrix bankSwap bankSwap

theorem payload_hermitian (B : Matrix b b ℂ) : (payload (a := a) B).IsHermitian := by
  unfold IsHermitian payload
  rw [conjTranspose_submatrix, (RegisterHamiltonian.generator_hermitian B).eq]

theorem payload_observed (B : Matrix b b ℂ) (hB : B.IsHermitian) :
    Obs (embedding (a := a) (b := b)) (payload B) ((1 : Matrix a a ℂ) ⊗ₖ B) := by
  have hh := NativeObservation.relabel bankSwap (Equiv.prodComm a b)
    (RegisterHamiltonian.generator_observed (b := a) B hB)
  rwa [swap_embedding, swap_tensor] at hh

omit [DecidableEq a] [DecidableEq b] in
theorem occupied_swap (q : Configuration a b) : occupied (bankSwap q) = occupied q := by
  exact (Equiv.sumComm b a).sum_comp (fun x : a ⊕ b => if q x then 1 else 0)

theorem payload_occupation_zero (B : Matrix b b ℂ) (q r : Configuration a b)
    (h : occupied q ≠ occupied r) : payload B q r = 0 := by
  apply RegisterHamiltonian.generator_occupation_zero
  simpa only [occupied_swap] using h

/-- Hermitian completion of the independent spinor and payload generators. -/
def interaction (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    Matrix (Configuration a b) (Configuration a b) ℂ :=
  let C := RegisterHamiltonian.generator A * payload B
  (1/2 : ℂ) • (C + Cᴴ)

private theorem product_occupation_zero (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (q r : Configuration a b) (h : occupied q ≠ occupied r) :
    (RegisterHamiltonian.generator (b := b) A * payload (a := a) B) q r = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : occupied q = occupied s
  · have hr : occupied s ≠ occupied r := fun he => h (hs.trans he)
    rw [payload_occupation_zero B s r hr, mul_zero]
  · rw [RegisterHamiltonian.generator_occupation_zero A q s hs, zero_mul]

theorem occupation_zero (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (q r : Configuration a b) (h : occupied q ≠ occupied r) : interaction A B q r = 0 := by
  simp only [interaction, Matrix.smul_apply, Matrix.add_apply, conjTranspose_apply]
  rw [product_occupation_zero A B q r h, product_occupation_zero A B r q (Ne.symm h)]
  simp

theorem evolution_occupation (A : Matrix a a ℂ) (B : Matrix b b ℂ) (z : ℂ) :
    NormedSpace.exp (z • interaction A B) * diagonal (fun q => (occupied q : ℂ)) =
      diagonal (fun q => (occupied q : ℂ)) * NormedSpace.exp (z • interaction A B) := by
  apply RectangularEvolution.scaled
  ext q r
  rw [mul_diagonal, diagonal_mul]
  by_cases h : occupied q = occupied r
  · rw [h, mul_comm]
  · rw [occupation_zero A B q r h, zero_mul, mul_zero]

theorem hermitian (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    (interaction A B).IsHermitian := by
  unfold IsHermitian interaction
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  norm_num

theorem observed (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Obs embedding (interaction A B) (A ⊗ₖ B) := by
  have hh := NativeObservation.mul (RegisterHamiltonian.generator_observed A hA)
    (payload_observed B hB)
  simp only [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul] at hh
  apply NativeObservation.herm hh
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

theorem evolution_unitary (A : Matrix a a ℂ) (B : Matrix b b ℂ) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • interaction A B) ∈ unitary _ :=
  NativeObservation.exp_unitary _ (hermitian A B) t

theorem evolution_readout (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) (ψ : Configuration a b → ℂ) :
    embeddingᴴ *ᵥ (NormedSpace.exp (z • interaction A B) *ᵥ ψ) =
      NormedSpace.exp (z • (A ⊗ₖ B)) *ᵥ (embeddingᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (observed A B hA hB) z) ψ

section Current
variable (c : Fin 3)

def current (B : Matrix b b ℂ) :
    Matrix (RegisterVacuum.Config (b := b) c) (RegisterVacuum.Config (b := b) c) ℂ :=
  interaction (RegisterVacuum.nativeProjector c) B

theorem current_observed (B : Matrix b b ℂ) (hB : B.IsHermitian) :
    Obs (RegisterVacuum.embedding (b := b) c) (current c B)
      (WallChiralCurrent.projector ⊗ₖ B) := by
  apply NativeObservation.compose (observed _ B (RegisterVacuum.projector_hermitian c) hB)
  exact NativeObservation.tensor (RegisterVacuum.native_projector_observed c)
    (show Obs (1 : Matrix b b ℂ) B B from ⟨by simp, by simp⟩)

theorem current_unitary (B : Matrix b b ℂ) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • current c B) ∈ unitary _ :=
  evolution_unitary _ B t

end Current
end PMAction.RegisterInteraction
