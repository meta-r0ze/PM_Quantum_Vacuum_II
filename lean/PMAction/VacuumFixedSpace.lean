import PMAction.FixedSpace
import PMAction.VacuumSplit
import PMAction.EnergyCounts

/-! Complete fixed-space statements for the exact Wilson exponential, and at
the origin for the actual vacuum-preserving split update. The nonzero-momentum
split product is not the Hamiltonian exponential and is not covered here. -/
noncomputable section
namespace PMAction.VacuumFixedSpace
open Matrix ConcreteFermion

theorem eigenphase_bound (k : Fin 3 → ℝ) (τ : ℝ) (hstep : |τ| ≤ 1/2) :
    ∀ j, |τ * (hamiltonian_hermitian k (DomainWallSpectrum.wilson k)).eigenvalues j| <
      2 * Real.pi := by
  intro j
  let hH := hamiltonian_hermitian k (DomainWallSpectrum.wilson k)
  let v : Sites → ℂ := hH.eigenvectorBasis j
  have hv : v ≠ 0 := by
    intro hz
    apply hH.eigenvectorBasis.orthonormal.ne_zero j
    ext i
    exact congrFun hz i
  have hb := DomainWallSpectrum.energy_bandwidth alpha beta gamma k clifford gamma_square
    beta_gamma alpha_gamma v hv (hH.eigenvalues j) (hH.mulVec_eigenvectorBasis j)
  rw [abs_mul]
  have hm := mul_le_mul_of_nonneg_right hstep (abs_nonneg (hH.eigenvalues j))
  change |τ| * |hH.eigenvalues j| < 2 * Real.pi
  nlinarith [Real.pi_gt_three]

/-- A full-vector statement, not just a scalar eigenphase test. -/
theorem exact_fixed_iff (k : Fin 3 → ℝ) (τ : ℝ) (hτ : τ ≠ 0)
    (hstep : |τ| ≤ 1/2) (v : Sites → ℂ) :
    NormedSpace.exp ((((-τ : ℝ) : ℂ) * Complex.I) •
      hamiltonian k (DomainWallSpectrum.wilson k)) *ᵥ v = v ↔
      hamiltonian k (DomainWallSpectrum.wilson k) *ᵥ v = 0 :=
  FixedSpace.exponential_fixed_iff (hamiltonian_hermitian _ _) τ hτ
    (eigenphase_bound k τ hstep) v

theorem exact_fixed_only_at_origin (k : Fin 3 → ℝ)
    (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi) (τ : ℝ) (hτ : τ ≠ 0)
    (hstep : |τ| ≤ 1/2) (v : Sites → ℂ) (hv : v ≠ 0)
    (hf : NormedSpace.exp ((((-τ : ℝ) : ℂ) * Complex.I) •
      hamiltonian k (DomainWallSpectrum.wilson k)) *ᵥ v = v) : k = 0 :=
  DomainWallSpectrum.wilson_point_zero_only_at_origin alpha beta gamma k clifford
    gamma_square beta_gamma alpha_gamma hcell v hv ((exact_fixed_iff k τ hτ hstep v).mp hf)

/-- At zero momentum the corrected split has exactly the four-dimensional
Hamiltonian vacuum kernel in the stated tick range. -/
theorem origin_split_fixed_iff (τ : ℝ) (hτ : τ ≠ 0) (hstep : |τ| ≤ 1/2)
    (v : Sites → ℂ) :
    VacuumSplit.momentumUpdate 0 τ *ᵥ v = v ↔ VacuumSplit.wall *ᵥ v = 0 := by
  rw [VacuumSplit.origin_update, VacuumSplit.wallCoin]
  have hs : -Complex.I * (τ : ℂ) = (((-τ : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hs]
  have h := exact_fixed_iff 0 τ hτ hstep v
  simpa [DomainWallSpectrum.wilson, VacuumSplit.wall] using h

theorem origin_fixed_coordinates (τ : ℝ) (hτ : τ ≠ 0) (hstep : |τ| ≤ 1/2)
    (v : Sites → ℂ) :
    VacuumSplit.momentumUpdate 0 τ *ᵥ v = v ↔
      v (.inl 2) = 0 ∧ v (.inl 3) = 0 ∧ v (.inr 0) = 0 ∧ v (.inr 1) = 0 := by
  rw [origin_split_fixed_iff τ hτ hstep]
  exact kernel_coordinates v

end PMAction.VacuumFixedSpace
