import PMAction.PropagationBounds
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! A concrete on-site coin and its exactly local split-step completion.
Hamiltonian and finite-step spectra are distinct proof obligations. -/
noncomputable section
namespace PMAction.WilsonSplit
open Matrix ConcreteFermion
open NormedSpace

/-- The momentum-independent part of the chosen Wilson Hamiltonian. -/
def onsiteHamiltonian : Matrix Sites Sites ℂ := hamiltonian 0 3

/-- Only eight internal components are exponentiated, never the spatial stencil. -/
def onsiteCoin (τ : ℝ) : Matrix Sites Sites ℂ :=
  exp ((-Complex.I*(τ : ℂ)) • onsiteHamiltonian)

theorem onsiteCoin_unitary (τ : ℝ) :
    onsiteCoin τ ∈ unitary (Matrix Sites Sites ℂ) := by
  have hh : onsiteHamiltonian.IsHermitian := hamiltonian_hermitian 0 3
  have ha : ((-Complex.I*(τ : ℂ)) • onsiteHamiltonian)ᴴ =
      -((-Complex.I*(τ : ℂ)) • onsiteHamiltonian) := by
    simp only [conjTranspose_neg, conjTranspose_smul, hh.eq, RCLike.star_def, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_smul, neg_mul]
  have hadj : (onsiteCoin τ)ᴴ = exp (-((-Complex.I*(τ : ℂ)) • onsiteHamiltonian)) := by
    rw [onsiteCoin, ← Matrix.exp_conjTranspose, ha]
  constructor
  · change (onsiteCoin τ)ᴴ*onsiteCoin τ=1
    rw [hadj, onsiteCoin]
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl
      ((-Complex.I*(τ : ℂ)) • onsiteHamiltonian)).neg_left]
    simp
  · change onsiteCoin τ*(onsiteCoin τ)ᴴ=1
    rw [hadj, onsiteCoin]
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl
      ((-Complex.I*(τ : ℂ)) • onsiteHamiltonian)).neg_right]
    simp

def update (N : ℕ) (τ : ℝ) := SplitUpdate.cubicUpdate N (onsiteCoin τ) τ

theorem update_unitary (N : ℕ) (τ : ℝ) :
    update N τ ∈ unitary (Matrix ((Fin 3 → Fin N) × Sites) ((Fin 3 → Fin N) × Sites) ℂ) :=
  SplitUpdate.cubicUpdate_unitary _ _ _ (onsiteCoin_unitary τ)

theorem update_population (N : ℕ) (τ : ℝ) (ψ : (Fin 3 → Fin N) × Sites → ℂ) :
    ∑ z, Complex.normSq ((update N τ*ᵥψ) z) = ∑ z, Complex.normSq (ψ z) :=
  SplitUpdate.update_population _ _ _ (onsiteCoin_unitary τ) ψ

/-- No read outside the three successive coordinate-neighbor choices. -/
theorem update_local (N : ℕ) (τ : ℝ) (ψ φ : (Fin 3 → Fin N) × Sites → ℂ)
    (x : Fin 3 → Fin N)
    (h : ∀ y, SplitUpdate.Reach (SplitUpdate.axisShift N) x y → ∀ a, ψ (y,a)=φ (y,a)) :
    ∀ a, (update N τ*ᵥψ) (x,a)=(update N τ*ᵥφ) (x,a) :=
  SplitUpdate.update_local _ _ _ _ _ _ h

/-- Momentum symbol of the real-space directional neighbor involution. -/
def directionSymbol (j : Fin 3) (q : ℝ) : Matrix Sites Sites ℂ :=
  fromBlocks ((Real.cos q : ℝ) • beta - (Real.sin q : ℝ) • alpha j) 0 0
    ((Real.cos q : ℝ) • beta - (Real.sin q : ℝ) • alpha j)

set_option maxHeartbeats 2000000 in
/-- The sum of the split generators is exactly the stated Wilson Hamiltonian. -/
theorem generator_identity (k : Fin 3 → ℝ) :
    onsiteHamiltonian - ∑ j, directionSymbol j (k j) =
      hamiltonian k (DomainWallSpectrum.wilson k) := by
  ext x y
  cases x with
  | inl i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;>
        simp [onsiteHamiltonian, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.wilson, directionSymbol, beta, alpha, Fin.sum_univ_three] <;> module
    | inr j => simp [onsiteHamiltonian, hamiltonian, DomainWallSpectrum.H,
        directionSymbol, Fin.sum_univ_three]
  | inr i => cases y with
    | inl j => simp [onsiteHamiltonian, hamiltonian, DomainWallSpectrum.H,
        directionSymbol, Fin.sum_univ_three]
    | inr j => fin_cases i <;> fin_cases j <;>
        simp [onsiteHamiltonian, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.wilson, directionSymbol, beta, alpha, Fin.sum_univ_three] <;> module

end PMAction.WilsonSplit
