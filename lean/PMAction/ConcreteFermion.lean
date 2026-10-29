import PMAction.DomainWallSpectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A concrete four-component chiral representation of the chosen two-wall model.
This verifies a representation; it does not derive its physical gauge content.
The full state has eight complex components before selecting low-energy modes. -/
noncomputable section
namespace PMAction.ConcreteFermion
open Matrix

abbrev Spin := Matrix (Fin 4) (Fin 4) ℂ
abbrev Sites := Fin 4 ⊕ Fin 4

def beta : Spin := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
def gamma : Spin := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
def alpha : Fin 3 → Spin := ![
  !![0,1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,-1,0],
  !![0,-Complex.I,0,0; Complex.I,0,0,0; 0,0,0,Complex.I; 0,0,-Complex.I,0],
  !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]]

theorem beta_square : beta*beta=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [beta, mul_apply, Fin.sum_univ_four]

theorem gamma_square : gamma*gamma=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [gamma, mul_apply, Fin.sum_univ_four]

theorem beta_gamma : beta*gamma=-(gamma*beta) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [beta, gamma, mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 1000000 in
theorem clifford : Dirac.Clifford alpha beta := by
  refine ⟨?_, beta_square, ?_, ?_⟩
  · intro k; fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [alpha, mul_apply, Fin.sum_univ_four]
  · intro k l h; fin_cases k <;> fin_cases l <;> try contradiction
    all_goals ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [alpha, mul_apply, Fin.sum_univ_four]
  · intro k; fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [alpha, beta, mul_apply, Fin.sum_univ_four]

theorem alpha_gamma : ∀ k, alpha k*gamma=gamma*alpha k := by
  intro k; fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [alpha, gamma, mul_apply, Fin.sum_univ_four]

theorem beta_hermitian : beta.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [beta, conjTranspose_apply]

theorem gamma_hermitian : gamma.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamma, conjTranspose_apply]

theorem alpha_hermitian : ∀ k, (alpha k).IsHermitian := by
  intro k; fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [alpha, conjTranspose_apply]

def hamiltonian (k : Fin 3 → ℝ) (δ : ℝ) : Matrix Sites Sites ℂ :=
  DomainWallSpectrum.H (DomainWallSpectrum.momentum alpha k) beta gamma δ

theorem momentum_hermitian (k : Fin 3 → ℝ) :
    (DomainWallSpectrum.momentum alpha k).IsHermitian := by
  simp only [DomainWallSpectrum.momentum, Fin.sum_univ_three]
  exact (((alpha_hermitian 0).smul (IsSelfAdjoint.all (Real.sin (k 0)))).add
    ((alpha_hermitian 1).smul (IsSelfAdjoint.all (Real.sin (k 1))))).add
      ((alpha_hermitian 2).smul (IsSelfAdjoint.all (Real.sin (k 2))))

theorem hamiltonian_hermitian (k : Fin 3 → ℝ) (δ : ℝ) :
    (hamiltonian k δ).IsHermitian := by
  have hd := (momentum_hermitian k).add (beta_hermitian.smul (IsSelfAdjoint.all δ))
  have hh : (DomainWallSpectrum.hop beta gamma)ᴴ=DomainWallSpectrum.back beta gamma := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [DomainWallSpectrum.hop, DomainWallSpectrum.back,
        DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma,
        conjTranspose_apply, mul_apply, vecMul, dotProduct, Matrix.add_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four]
  have hb : (DomainWallSpectrum.back beta gamma)ᴴ=DomainWallSpectrum.hop beta gamma := by
    rw [← hh, conjTranspose_conjTranspose]
  change (fromBlocks _ _ _ _)ᴴ=fromBlocks _ _ _ _
  rw [fromBlocks_conjTranspose, hd.eq, hh, hb]

/-- The concrete positive/negative chirality spaces each have dimension two. -/
theorem projector_ranks : (DomainWallSpectrum.plus gamma).rank=2 ∧
    (DomainWallSpectrum.minus gamma).rank=2 := by
  have hp : DomainWallSpectrum.plus gamma=diagonal (![1,1,0,0] : Fin 4 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [DomainWallSpectrum.plus, gamma]
  have hm : DomainWallSpectrum.minus gamma=diagonal (![0,0,1,1] : Fin 4 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [DomainWallSpectrum.minus, gamma]
  rw [hp, hm, rank_diagonal, rank_diagonal]
  simp only [Fintype.card_subtype]
  constructor
  · have hs : (Finset.univ.filter (fun i : Fin 4 => (![1,1,0,0] i : ℂ) ≠ 0)) = {0,1} := by
      ext i; fin_cases i <;> norm_num
    rw [hs]; norm_num
  · have hs : (Finset.univ.filter (fun i : Fin 4 => (![0,0,1,1] i : ℂ) ≠ 0)) = {2,3} := by
      ext i; fin_cases i <;> norm_num
    rw [hs]; norm_num

def zeroState (u : Fin 4 → ℂ) : Sites → ℂ :=
  Sum.elim ![u 0,u 1,0,0] ![0,0,u 2,u 3]

/-- The exact four constrained coordinates of the zero-momentum kernel. -/
theorem kernel_coordinates (v : Sites → ℂ) : hamiltonian 0 0*ᵥ v=0 ↔
    v (.inl 2)=0 ∧ v (.inl 3)=0 ∧ v (.inr 0)=0 ∧ v (.inr 1)=0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := congrFun h (.inr 0)
      simpa [hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
        DomainWallSpectrum.minus, beta, gamma, mulVec, dotProduct, vecMul,
        mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four] using hh
    · have hh := congrFun h (.inr 1)
      simpa [hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
        DomainWallSpectrum.minus, beta, gamma, mulVec, dotProduct, vecMul,
        mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four] using hh
    · have hh := congrFun h (.inl 2)
      simpa [hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
        DomainWallSpectrum.minus, beta, gamma, mulVec, dotProduct, vecMul,
        mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four] using hh
    · have hh := congrFun h (.inl 3)
      simpa [hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
        DomainWallSpectrum.minus, beta, gamma, mulVec, dotProduct, vecMul,
        mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four] using hh
  · rintro ⟨h2,h3,h0,h1⟩
    ext i; cases i with
    | inl i => fin_cases i <;> simp [hamiltonian, DomainWallSpectrum.H,
        DomainWallSpectrum.momentum, DomainWallSpectrum.hop, DomainWallSpectrum.back,
        DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma, mulVec,
        dotProduct, vecMul, Fintype.sum_sum_type, Fin.sum_univ_four,h0,h1]
    | inr i => fin_cases i <;> simp [hamiltonian, DomainWallSpectrum.H,
        DomainWallSpectrum.momentum, DomainWallSpectrum.hop, DomainWallSpectrum.back,
        DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma, mulVec,
        dotProduct, vecMul, Fintype.sum_sum_type, Fin.sum_univ_four, h2,h3]

/-- An explicit linear parametrization, not only a list of possible roots. -/
def zeroKernelEquiv : LinearMap.ker (hamiltonian 0 0).mulVecLin ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![v.1 (.inl 0),v.1 (.inl 1),v.1 (.inr 2),v.1 (.inr 3)]
  invFun u := ⟨zeroState u, (kernel_coordinates _).mpr (by simp [zeroState])⟩
  left_inv v := by
    apply Subtype.ext
    have hc := (kernel_coordinates v.1).mp v.2
    funext i; cases i with
    | inl i => fin_cases i <;> simp [zeroState, hc.1, hc.2.1]
    | inr i => fin_cases i <;> simp [zeroState, hc.2.2.1, hc.2.2.2]
  right_inv u := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

theorem zero_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker (hamiltonian 0 0).mulVecLin)=4 := by
  rw [zeroKernelEquiv.finrank_eq]
  simp

/-- Left and right wall components have opposite chirality exactly at zero. -/
theorem wall_chirality (u : Fin 4 → ℂ) :
    gamma*ᵥ (fun i => zeroState u (.inl i)) = (fun i => zeroState u (.inl i)) ∧
    gamma*ᵥ (fun i => zeroState u (.inr i)) = -(fun i => zeroState u (.inr i)) := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [zeroState, gamma, mulVec, dotProduct, Fin.sum_univ_four]

end PMAction.ConcreteFermion
