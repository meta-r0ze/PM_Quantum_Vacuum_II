import PMAction.SplitGenerator
import PMAction.SplitSymbol

/-! A vacuum-preserving factor ordering. Spatial propagation is unchanged;
the on-site beta rotation is separated from the wall hopping. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.VacuumSplit
open Matrix ConcreteFermion NormedSpace

def beta8 : Matrix Sites Sites ℂ := fromBlocks beta 0 0 beta
def wall : Matrix Sites Sites ℂ := hamiltonian 0 0
def vacuumProjector : Matrix Sites Sites ℂ :=
  fromBlocks (DomainWallSpectrum.plus gamma) 0 0 (DomainWallSpectrum.minus gamma)

lemma beta8_hermitian : beta8.IsHermitian := by
  simp [IsHermitian, beta8, fromBlocks_conjTranspose, beta_hermitian.eq]
lemma beta8_square : beta8*beta8=1 := by
  simp [beta8, fromBlocks_multiply, beta_square, fromBlocks_one]

lemma direction_zero (j : Fin 3) : WilsonSplit.directionSymbol j 0=beta8 := by
  simp [WilsonSplit.directionSymbol, beta8]

def rotation (τ : ℝ) := LocalUnitary.rotation beta8 τ
lemma rotation_unitary (τ : ℝ) : rotation τ ∈ unitary (Matrix Sites Sites ℂ) :=
  LocalUnitary.rotation_unitary _ _ beta8_hermitian beta8_square

def wallCoin (τ : ℝ) : Matrix Sites Sites ℂ := exp ((-Complex.I*(τ : ℂ)) • wall)

/-- The proof applies to any Hermitian finite internal matrix. -/
lemma exp_unitary (A : Matrix Sites Sites ℂ) (ha : A.IsHermitian) (τ : ℝ) :
    exp ((-Complex.I*(τ : ℂ)) • A) ∈ unitary (Matrix Sites Sites ℂ) := by
  have hs : ((-Complex.I*(τ : ℂ)) • A)ᴴ = -((-Complex.I*(τ : ℂ)) • A) := by
    simp only [conjTranspose_neg, conjTranspose_smul, ha.eq, RCLike.star_def, map_mul,
      Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_smul, neg_mul]
  have he : (exp ((-Complex.I*(τ : ℂ)) • A))ᴴ =
      exp (-((-Complex.I*(τ : ℂ)) • A)) := by rw [← Matrix.exp_conjTranspose, hs]
  constructor
  · change (exp _)ᴴ*exp _=1
    rw [he, ← Matrix.exp_add_of_commute _ _
      (Commute.refl ((-Complex.I*(τ : ℂ)) • A)).neg_left]
    simp
  · change exp _*(exp _)ᴴ=1
    rw [he, ← Matrix.exp_add_of_commute _ _
      (Commute.refl ((-Complex.I*(τ : ℂ)) • A)).neg_right]
    simp

lemma wallCoin_unitary (τ : ℝ) : wallCoin τ ∈ unitary (Matrix Sites Sites ℂ) :=
  exp_unitary wall (hamiltonian_hermitian 0 0) τ

/-- Reverse exactly the three spatial beta rotations before the wall coin. -/
def onsiteCoin (τ : ℝ) : Matrix Sites Sites ℂ := wallCoin τ * ((rotation τ)ᴴ)^3

lemma onsiteCoin_unitary (τ : ℝ) : onsiteCoin τ ∈ unitary (Matrix Sites Sites ℂ) :=
  (unitary _).mul_mem (wallCoin_unitary τ)
    ((unitary _).pow_mem (Unitary.star_mem (rotation_unitary τ)) 3)

def momentumUpdate (k : Fin 3 → ℝ) (τ : ℝ) : Matrix Sites Sites ℂ :=
  onsiteCoin τ * LocalUnitary.rotation (WilsonSplit.directionSymbol 0 (k 0)) τ *
    LocalUnitary.rotation (WilsonSplit.directionSymbol 1 (k 1)) τ *
    LocalUnitary.rotation (WilsonSplit.directionSymbol 2 (k 2)) τ

/-- Exact cancellation at the origin, for every tick size. -/
theorem origin_update (τ : ℝ) : momentumUpdate 0 τ = wallCoin τ := by
  have hu := (unitary _).pow_mem (rotation_unitary τ) 3
  have hc : ((rotation τ)ᴴ)^3 * (rotation τ)^3=1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_pow] using hu.1
  simp only [momentumUpdate, Pi.zero_apply, direction_zero, onsiteCoin]
  change wallCoin τ * ((rotation τ)ᴴ)^3 * rotation τ * rotation τ * rotation τ = wallCoin τ
  calc
    _ = wallCoin τ * (((rotation τ)ᴴ)^3 * (rotation τ)^3) := by noncomm_ring
    _ = wallCoin τ := by rw [hc, mul_one]

set_option maxHeartbeats 1000000 in
lemma wall_projector : wall*vacuumProjector=0 := by
  ext x y
  cases x with
  | inl i => cases y with
    | inl j => simp [wall, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        vacuumProjector, fromBlocks_multiply]
    | inr j => fin_cases i <;> fin_cases j <;>
        norm_num [wall, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          vacuumProjector, DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, beta, gamma, mul_apply, vecMul, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]
  | inr i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;>
        norm_num [wall, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          vacuumProjector, DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, beta, gamma, mul_apply, vecMul, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]
    | inr j => simp [wall, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
        vacuumProjector, fromBlocks_multiply]

lemma projector_fixes_kernel (v : Sites → ℂ) (hv : wall*ᵥv=0) : vacuumProjector*ᵥv=v := by
  have h := (kernel_coordinates v).mp hv
  ext x; cases x with
  | inl i => fin_cases i <;> norm_num [vacuumProjector, DomainWallSpectrum.plus,
      DomainWallSpectrum.minus, gamma, mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_four, h.1, h.2.1]
  | inr i => fin_cases i <;> norm_num [vacuumProjector, DomainWallSpectrum.plus,
      DomainWallSpectrum.minus, gamma, mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_four, h.2.2.1, h.2.2.2]

lemma wallCoin_projector (τ : ℝ) : wallCoin τ*vacuumProjector=vacuumProjector := by
  have ha : ((-Complex.I*(τ : ℂ)) • wall)*vacuumProjector=0 := by
    rw [smul_mul_assoc, wall_projector, smul_zero]
  have hs : SemiconjBy vacuumProjector (0 : Matrix Sites Sites ℂ)
      ((-Complex.I*(τ : ℂ)) • wall) := by
    change vacuumProjector*0 = ((-Complex.I*(τ : ℂ)) • wall)*vacuumProjector
    rw [mul_zero, ha]
  have he : vacuumProjector*exp (0 : Matrix Sites Sites ℂ) =
      exp ((-Complex.I*(τ : ℂ)) • wall)*vacuumProjector := by
    open scoped Matrix.Norms.Operator in
      exact hs.exp_right
  simpa only [SemiconjBy, exp_zero, mul_one, wallCoin] using he.symm

/-- Every Hamiltonian vacuum mode is fixed exactly, not merely to first order. -/
theorem vacuum_preserved (τ : ℝ) (v : Sites → ℂ) (hv : wall*ᵥv=0) :
    momentumUpdate 0 τ*ᵥv=v := by
  rw [origin_update, ← projector_fixes_kernel v hv, mulVec_mulVec, wallCoin_projector]

def update (N : ℕ) (τ : ℝ) := SplitUpdate.cubicUpdate N (onsiteCoin τ) τ

theorem update_unitary (N : ℕ) (τ : ℝ) :
    update N τ ∈ unitary (Matrix ((Fin 3 → Fin N) × Sites) ((Fin 3 → Fin N) × Sites) ℂ) :=
  SplitUpdate.cubicUpdate_unitary _ _ _ (onsiteCoin_unitary τ)

theorem update_population (N : ℕ) (τ : ℝ) (ψ : (Fin 3 → Fin N) × Sites → ℂ) :
    ∑ z, Complex.normSq ((update N τ*ᵥψ) z) = ∑ z, Complex.normSq (ψ z) :=
  SplitUpdate.update_population _ _ _ (onsiteCoin_unitary τ) ψ

theorem update_local (N : ℕ) (τ : ℝ) (ψ φ : (Fin 3 → Fin N) × Sites → ℂ)
    (x : Fin 3 → Fin N)
    (h : ∀ y, SplitUpdate.Reach (SplitUpdate.axisShift N) x y → ∀ a, ψ (y,a)=φ (y,a)) :
    ∀ a, (update N τ*ᵥψ) (x,a)=(update N τ*ᵥφ) (x,a) :=
  SplitUpdate.update_local _ _ _ _ _ _ h

end PMAction.VacuumSplit
