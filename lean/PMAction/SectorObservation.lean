import PMAction.StateIdentification

/-!
# Exact observation on finite families of native sectors

An isometric readout and observed update in each native sector combine into a
single isometric readout and observed update on their direct sum, including
different carrier index types. The full ambient state is retained. Sector
admission, preparation, inter-sector interactions and prices are not selected.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.SectorObservation
open Matrix NativeObservation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → Type*} [∀ i, Fintype (a i)] [∀ i, DecidableEq (a i)]
    [∀ i, Fintype (b i)] [∀ i, DecidableEq (b i)]

def encoding (E : ∀ i, Matrix (a i) (b i) ℂ) := blockDiagonal' E

omit [∀ i, DecidableEq (a i)] [∀ i, Fintype (b i)] in
theorem isometry (E : ∀ i, Matrix (a i) (b i) ℂ) (hE : ∀ i, (E i)ᴴ * E i = 1) :
    (encoding E)ᴴ * encoding E = 1 := by
  simp only [encoding, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, hE]
  exact blockDiagonal'_one

omit [∀ i, DecidableEq (a i)] [∀ i, DecidableEq (b i)] in
theorem observed (E : ∀ i, Matrix (a i) (b i) ℂ)
    (A : ∀ i, Matrix (a i) (a i) ℂ) (B : ∀ i, Matrix (b i) (b i) ℂ)
    (h : ∀ i, Obs (E i) (A i) (B i)) :
    Obs (encoding E) (blockDiagonal' A) (blockDiagonal' B) := by
  constructor
  · simp only [encoding, ← blockDiagonal'_mul]
    congr 1
    funext i
    exact (h i).1
  · simp only [encoding, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    congr 1
    funext i
    exact (h i).2

omit [Fintype ι] [∀ i, Fintype (a i)] [∀ i, DecidableEq (a i)] in
theorem hermitian (A : ∀ i, Matrix (a i) (a i) ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (blockDiagonal' A).IsHermitian := by
  change (blockDiagonal' A)ᴴ = blockDiagonal' A
  rw [blockDiagonal'_conjTranspose]
  congr 1
  funext i
  exact (hA i).eq

theorem unitary (A : ∀ i, Matrix (a i) (a i) ℂ)
    (hA : ∀ i, A i ∈ unitary (Matrix (a i) (a i) ℂ)) :
    blockDiagonal' A ∈ unitary (Matrix (Σ i, a i) (Σ i, a i) ℂ) := by
  have hl (i) : (A i)ᴴ * A i = 1 := by
    simpa only [star_eq_conjTranspose] using (hA i).1
  have hr (i) : A i * (A i)ᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using (hA i).2
  constructor
  · change (blockDiagonal' A)ᴴ * blockDiagonal' A = 1
    simp only [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, hl]
    exact blockDiagonal'_one
  · change blockDiagonal' A * (blockDiagonal' A)ᴴ = 1
    simp only [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, hr]
    exact blockDiagonal'_one

omit [∀ i, DecidableEq (a i)] in
/-- Block action on arbitrary ambient amplitudes is exactly fibrewise action. -/
theorem action_fibre (A : ∀ i, Matrix (a i) (a i) ℂ)
    (ψ : (Σ i, a i) → ℂ) (i : ι) (x : a i) :
    (blockDiagonal' A *ᵥ ψ) ⟨i, x⟩ = (A i *ᵥ fun y => ψ ⟨i, y⟩) x := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp only [blockDiagonal'_apply_eq]
  · intro j hj
    apply Finset.sum_eq_zero
    intro y _
    rw [blockDiagonal'_apply_ne A x y hj.symm, zero_mul]

end PMAction.SectorObservation
