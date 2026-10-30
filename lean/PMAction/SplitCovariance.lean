import PMAction.VacuumSplit
import PMAction.WallExchange
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Wall-parity covariance of the ordered split update

`WallExchange` proves that the continuous domain-wall Hamiltonian satisfies
`P H_Y(k) P = H_{Yᴴ}(-k)` under the combined wall exchange and spinor parity `P`.
This module specializes that symmetry to the actual sine-momentum Wilson Hamiltonian
and proves that the actual ordered finite-tick update `VacuumSplit.momentumUpdate`
shares the exact wall-parity covariance:

  `P₈ (momentumUpdate k τ) P₈ = momentumUpdate (-k) τ`.

This bridges the gap between the continuous linear-momentum covariance and the
actual discrete finite-tick Wilson split. It concerns the supplied flavour-free
Hamiltonian and ordering; physical parity selection and general flavour-link or
mass-phase conclusions remain separate.
-/

noncomputable section
namespace PMAction.SplitCovariance
open Matrix ConcreteFermion VacuumSplit
open scoped Matrix.Norms.Operator

/-- Parity combined with wall exchange on the eight internal sites. -/
def P8 : Matrix Sites Sites ℂ := fromBlocks 0 beta beta 0

theorem P8_involution : P8 * P8 = 1 := by
  rw [P8, fromBlocks_multiply]
  simp [beta_square, fromBlocks_one]

theorem P8_hermitian : P8.IsHermitian := by
  change P8ᴴ = P8
  have hb : betaᴴ = beta := beta_hermitian.eq
  rw [P8, fromBlocks_conjTranspose]
  simp [hb]

lemma P8_sandwich_mul (A B : Matrix Sites Sites ℂ) :
    (P8 * A * P8) * (P8 * B * P8) = P8 * (A * B) * P8 := by
  calc
    (P8 * A * P8) * (P8 * B * P8) = P8 * A * (P8 * P8) * B * P8 := by noncomm_ring
    _ = P8 * A * 1 * B * P8 := by rw [P8_involution]
    _ = P8 * (A * B) * P8 := by noncomm_ring

lemma P8_sandwich_diag (A : Spin) :
    P8 * fromBlocks A 0 0 A * P8 = fromBlocks (beta * A * beta) 0 0 (beta * A * beta) := by
  rw [P8, fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero]

lemma P8_sandwich_block (A B C D : Spin) :
    P8 * fromBlocks A B C D * P8 = fromBlocks (beta * D * beta) (beta * C * beta)
      (beta * B * beta) (beta * A * beta) := by
  rw [P8, fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero]

/-- Sine momentum term used by the concrete Wilson Hamiltonian. -/
lemma beta_momentum (k : Fin 3 → ℝ) :
    beta * DomainWallSpectrum.momentum alpha k * beta =
      DomainWallSpectrum.momentum alpha (-k) := by
  simp only [DomainWallSpectrum.momentum, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, WallExchange.beta_alpha, Pi.neg_apply, Real.sin_neg,
    neg_smul, smul_neg]

lemma hop_eq_exchange : DomainWallSpectrum.hop beta gamma = WallExchange.hop := by
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [DomainWallSpectrum.hop, DomainWallSpectrum.plus, WallExchange.hop,
      beta, gamma, mul_apply, vecMul, dotProduct, Fin.sum_univ_four]

lemma back_eq_exchange : DomainWallSpectrum.back beta gamma = WallExchange.back := by
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [DomainWallSpectrum.back, DomainWallSpectrum.minus, WallExchange.back,
      beta, gamma, mul_apply, vecMul, dotProduct, Fin.sum_univ_four]

lemma beta_hop_beta : beta * DomainWallSpectrum.hop beta gamma * beta =
    DomainWallSpectrum.back beta gamma := by
  rw [hop_eq_exchange, back_eq_exchange, WallExchange.beta_back]

lemma beta_back_beta : beta * DomainWallSpectrum.back beta gamma * beta =
    DomainWallSpectrum.hop beta gamma := by
  rw [hop_eq_exchange, back_eq_exchange, WallExchange.beta_hop]

/-- The concrete Wilson Hamiltonian satisfies wall-parity covariance. -/
theorem hamiltonian_conjugates (k : Fin 3 → ℝ) (δ : ℝ) :
    P8 * hamiltonian k δ * P8 = hamiltonian (-k) δ := by
  have hd : beta * (DomainWallSpectrum.momentum alpha k + δ • beta) * beta =
      DomainWallSpectrum.momentum alpha (-k) + δ • beta := by
    simp only [mul_add, add_mul, beta_momentum, mul_smul_comm, smul_mul_assoc,
      WallExchange.beta_beta]
  change P8 * DomainWallSpectrum.H (DomainWallSpectrum.momentum alpha k) beta gamma δ * P8 =
    DomainWallSpectrum.H (DomainWallSpectrum.momentum alpha (-k)) beta gamma δ
  rw [DomainWallSpectrum.H, P8_sandwich_block]
  rw [beta_back_beta, beta_hop_beta, hd]
  rfl

/-- P8 commutes with the on-site wall hopping matrix. -/
theorem wall_commutes : P8 * wall * P8 = wall := by
  have h := hamiltonian_conjugates 0 0
  have hz : (-0 : Fin 3 → ℝ) = 0 := neg_zero
  rwa [hz] at h

/-- P8 commutes with beta8. -/
theorem beta8_commutes : P8 * beta8 * P8 = beta8 := by
  rw [beta8, P8_sandwich_diag, WallExchange.beta_beta]

/-- P8 commutes with on-site beta8 rotations. -/
theorem rotation_commutes (τ : ℝ) : P8 * rotation τ * P8 = rotation τ := by
  simp only [rotation, LocalUnitary.rotation, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, P8_involution, beta8_commutes]

theorem rotation_adjoint_commutes (τ : ℝ) : P8 * (rotation τ)ᴴ * P8 = (rotation τ)ᴴ := by
  have h := congrArg conjTranspose (rotation_commutes τ)
  have hp : P8ᴴ = P8 := P8_hermitian.eq
  rw [conjTranspose_mul, conjTranspose_mul, hp] at h
  rw [← mul_assoc] at h
  exact h

/-- P8 commutes with powers of the rotation adjoint. -/
theorem rotation_pow_commutes (τ : ℝ) (n : ℕ) :
    P8 * ((rotation τ)ᴴ)^n * P8 = ((rotation τ)ᴴ)^n := by
  induction n with
  | zero => simp [P8_involution]
  | succ n ih =>
    rw [pow_succ, ← P8_sandwich_mul, ih, rotation_adjoint_commutes]

/-- Conjugation of the matrix exponential by P8. -/
lemma exp_conj_P8 (A : Matrix Sites Sites ℂ) :
    P8 * NormedSpace.exp A * P8 = NormedSpace.exp (P8 * A * P8) := by
  have hU : P8ᴴ * P8 = 1 := by rw [P8_hermitian.eq, P8_involution]
  have hU' : P8 * P8ᴴ = 1 := by rw [P8_hermitian.eq, P8_involution]
  let U : unitary (Matrix Sites Sites ℂ) := ⟨P8, hU, hU'⟩
  have hu : ((Unitary.toUnits U : (Matrix Sites Sites ℂ)ˣ) : Matrix Sites Sites ℂ) = P8 := rfl
  have hi : (((Unitary.toUnits U)⁻¹ : (Matrix Sites Sites ℂ)ˣ) : Matrix Sites Sites ℂ) = P8ᴴ := rfl
  rw [P8_hermitian.eq] at hi
  have he := Matrix.exp_units_conj (Unitary.toUnits U) A
  rw [hu, hi] at he
  exact he.symm

/-- P8 commutes with the wall coin. -/
theorem wallCoin_commutes (τ : ℝ) : P8 * wallCoin τ * P8 = wallCoin τ := by
  rw [wallCoin, exp_conj_P8]
  have hs : P8 * ((-Complex.I * (τ : ℂ)) • wall) * P8 = (-Complex.I * (τ : ℂ)) • wall := by
    simp only [mul_smul_comm, smul_mul_assoc, wall_commutes]
  rw [hs]

/-- P8 commutes with the combined on-site coin. -/
theorem onsiteCoin_commutes (τ : ℝ) : P8 * onsiteCoin τ * P8 = onsiteCoin τ := by
  rw [onsiteCoin, ← P8_sandwich_mul, wallCoin_commutes, rotation_pow_commutes]

/-- The directional symbol transforms under wall-parity as momentum reversal. -/
theorem directionSymbol_conjugates (j : Fin 3) (q : ℝ) :
    P8 * WilsonSplit.directionSymbol j q * P8 = WilsonSplit.directionSymbol j (-q) := by
  have hd : beta * ((Real.cos q : ℝ) • beta - (Real.sin q : ℝ) • alpha j) * beta =
      (Real.cos (-q) : ℝ) • beta - (Real.sin (-q) : ℝ) • alpha j := by
    ext a b
    fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [beta, alpha, mul_apply, Fin.sum_univ_four, Real.cos_neg, Real.sin_neg]
  rw [WilsonSplit.directionSymbol, P8_sandwich_diag, hd]
  rfl

/-- Each directional rotation transforms with momentum reversal. -/
theorem directionRotation_conjugates (j : Fin 3) (q τ : ℝ) :
    P8 * LocalUnitary.rotation (WilsonSplit.directionSymbol j q) τ * P8 =
      LocalUnitary.rotation (WilsonSplit.directionSymbol j (-q)) τ := by
  simp only [LocalUnitary.rotation, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, P8_involution, directionSymbol_conjugates]

/-- **Main theorem: The actual ordered Wilson split update satisfies wall-parity covariance.** -/
theorem momentumUpdate_conjugates (k : Fin 3 → ℝ) (τ : ℝ) :
    P8 * momentumUpdate k τ * P8 = momentumUpdate (-k) τ := by
  simp only [momentumUpdate]
  rw [← P8_sandwich_mul, ← P8_sandwich_mul, ← P8_sandwich_mul,
    onsiteCoin_commutes, directionRotation_conjugates,
    directionRotation_conjugates, directionRotation_conjugates]
  rfl

/-- Iterated finite-tick evolution shares the same covariance. -/
theorem momentumUpdate_pow_conjugates (k : Fin 3 → ℝ) (τ : ℝ) (N : ℕ) :
    P8 * (momentumUpdate k τ)^N * P8 = (momentumUpdate (-k) τ)^N := by
  induction N with
  | zero => simp [P8_involution]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← P8_sandwich_mul, ih, momentumUpdate_conjugates]

/-- Exact Wilson Hamiltonian exponential shares wall-parity covariance. -/
theorem hamiltonian_exp_conjugates (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ) :
    P8 * NormedSpace.exp (z • hamiltonian k δ) * P8 =
      NormedSpace.exp (z • hamiltonian (-k) δ) := by
  rw [exp_conj_P8]
  have hs : P8 * (z • hamiltonian k δ) * P8 = z • hamiltonian (-k) δ := by
    simp only [mul_smul_comm, smul_mul_assoc, hamiltonian_conjugates]
  rw [hs]

end PMAction.SplitCovariance
