import PMAction.TensorObservation

/-! Kernel and readout identities for arbitrary, possibly entangled, finite
tensor states. No factorization of an initial amplitude is assumed. -/
noncomputable section
namespace PMAction.TensorKernel
open Matrix
open scoped Kronecker
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

omit [DecidableEq a] in
theorem fibre_action (A : Matrix a a ℂ) (ψ : a × b → ℂ) (i : a) (j : b) :
    ((A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ) (i,j) = (A *ᵥ (fun k => ψ (k,j))) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

omit [DecidableEq a] in
theorem kernel_fibres (A : Matrix a a ℂ) (ψ : a × b → ℂ) :
    (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0 ↔ ∀ j, A *ᵥ (fun i => ψ (i,j)) = 0 := by
  constructor
  · intro h j
    ext i
    simpa only [fibre_action, Pi.zero_apply] using congrFun h (i,j)
  · intro h
    ext ⟨i,j⟩
    simpa only [fibre_action, Pi.zero_apply] using congrFun (h j) i

theorem payload_preserves (A : Matrix a a ℂ) (G : Matrix b b ℂ) (ψ : a × b → ℂ)
    (h : (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0) :
    (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ (((1 : Matrix a a ℂ) ⊗ₖ G) *ᵥ ψ) = 0 := by
  have hc : (A ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ G) =
      ((1 : Matrix a a ℂ) ⊗ₖ G) * (A ⊗ₖ (1 : Matrix b b ℂ)) := by
    simp [← mul_kronecker_mul]
  rw [mulVec_mulVec, hc, ← mulVec_mulVec, h, mulVec_zero]

theorem map_kernel (A P : Matrix a a ℂ) (G : Matrix b b ℂ)
    (hP : ∀ v, A *ᵥ v = 0 → A *ᵥ (P *ᵥ v) = 0)
    (ψ : a × b → ℂ) (h : (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0) :
    (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ((P ⊗ₖ G) *ᵥ ψ) = 0 := by
  let φ := ((1 : Matrix a a ℂ) ⊗ₖ G) *ᵥ ψ
  have hf := (kernel_fibres A φ).mp (payload_preserves A G ψ h)
  have he : (P ⊗ₖ G) *ᵥ ψ = (P ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ φ := by
    simp [φ, mulVec_mulVec, ← mul_kronecker_mul]
  rw [he, kernel_fibres]
  intro j
  have ht : (fun i => ((P ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ φ) (i,j)) =
      P *ᵥ (fun i => φ (i,j)) := funext (fun i => fibre_action P φ i j)
  rw [ht]
  exact hP _ (hf j)

theorem agree_on_kernel (A P Q : Matrix a a ℂ) (G : Matrix b b ℂ)
    (hPQ : ∀ v, A *ᵥ v = 0 → P *ᵥ v = Q *ᵥ v)
    (ψ : a × b → ℂ) (h : (A ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ ψ = 0) :
    (P ⊗ₖ G) *ᵥ ψ = (Q ⊗ₖ G) *ᵥ ψ := by
  let φ := ((1 : Matrix a a ℂ) ⊗ₖ G) *ᵥ ψ
  have hf := (kernel_fibres A φ).mp (payload_preserves A G ψ h)
  have he (B : Matrix a a ℂ) : (B ⊗ₖ G) *ᵥ ψ =
      (B ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ φ := by
    simp [φ, mulVec_mulVec, ← mul_kronecker_mul]
  rw [he P, he Q]
  ext ⟨i,j⟩
  rw [fibre_action, fibre_action]
  exact congrFun (hPQ _ (hf j)) i

end PMAction.TensorKernel
