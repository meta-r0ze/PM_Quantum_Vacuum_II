import PMAction.VacuumSplit
import Mathlib.Analysis.Calculus.Deriv.Star

/-! The vacuum-preserving reordering retains the original first-order generator. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.VacuumSplit
open Matrix ConcreteFermion NormedSpace
open scoped Matrix.Norms.Operator
local instance {n : Type*} [Fintype n] : TopologicalSpace (Matrix n n ℂ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

lemma onsite_decomposition : wall+(3 : ℂ) • beta8=WilsonSplit.onsiteHamiltonian := by
  ext x y
  cases x with
  | inl i => cases y <;> simp [wall, beta8, WilsonSplit.onsiteHamiltonian, hamiltonian,
      DomainWallSpectrum.H, DomainWallSpectrum.momentum, Fin.sum_univ_three]
  | inr i => cases y <;> simp [wall, beta8, WilsonSplit.onsiteHamiltonian, hamiltonian,
      DomainWallSpectrum.H, DomainWallSpectrum.momentum, Fin.sum_univ_three]

lemma rotation_zero : rotation 0=1 := by simp [rotation, LocalUnitary.rotation]
lemma wallCoin_zero : wallCoin 0=1 := by simp [wallCoin]
lemma onsiteCoin_zero : onsiteCoin 0=1 := by simp [onsiteCoin, rotation_zero, wallCoin_zero]

lemma rotation_deriv : HasDerivAt rotation (Complex.I • beta8) (0 : ℝ) :=
  WilsonSplit.rotation_deriv beta8

lemma backward_deriv : HasDerivAt (fun τ : ℝ => ((rotation τ)ᴴ)^3)
    ((-3*Complex.I) • beta8) 0 := by
  have hb : HasDerivAt (fun τ : ℝ => (rotation τ)ᴴ) ((-Complex.I) • beta8) 0 := by
    have h := rotation_deriv.star
    simpa only [star_eq_conjTranspose, conjTranspose_smul, beta8_hermitian.eq,
      RCLike.star_def, Complex.conj_I] using h
  have h := (hb.mul hb).mul hb
  simp only [Pi.mul_apply, rotation_zero, conjTranspose_one, one_mul, mul_one] at h
  have hd : (-Complex.I) • beta8 + (-Complex.I) • beta8 + (-Complex.I) • beta8 =
      (-3*Complex.I) • beta8 := by module
  rw [hd] at h
  convert! h using 1 <;> first | rfl | (funext τ; simp [pow_succ, pow_two])

lemma wallCoin_eq (τ : ℝ) : wallCoin τ=exp (τ • ((-Complex.I) • wall)) := by
  rw [wallCoin, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply congrArg exp
  exact congrArg (fun c : ℂ => c • wall) (mul_comm _ _)

lemma wallCoin_deriv : HasDerivAt wallCoin ((-Complex.I) • wall) (0 : ℝ) := by
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • wall) (0 : ℝ)
  simpa only [← wallCoin_eq, zero_smul, NormedSpace.exp_zero, one_mul] using h

lemma onsiteCoin_deriv : HasDerivAt onsiteCoin
    ((-Complex.I) • WilsonSplit.onsiteHamiltonian) (0 : ℝ) := by
  have h := wallCoin_deriv.mul backward_deriv
  simp only [wallCoin_zero, rotation_zero, conjTranspose_one, one_pow, one_mul, mul_one] at h
  have hd : (-Complex.I) • wall + (-3*Complex.I) • beta8 =
      (-Complex.I) • WilsonSplit.onsiteHamiltonian := by
    rw [← onsite_decomposition]
    module
  rw [hd] at h
  exact h

lemma momentumUpdate_zero (k : Fin 3 → ℝ) : momentumUpdate k 0=1 := by
  simp [momentumUpdate, onsiteCoin_zero, LocalUnitary.rotation]

/-- Both exact vacuum preservation and the original Wilson tangent hold. -/
theorem momentumUpdate_deriv (k : Fin 3 → ℝ) : HasDerivAt (momentumUpdate k)
    ((-Complex.I) • hamiltonian k (DomainWallSpectrum.wilson k)) (0 : ℝ) := by
  have h := ((onsiteCoin_deriv.mul (WilsonSplit.rotation_deriv
    (WilsonSplit.directionSymbol 0 (k 0)))).mul (WilsonSplit.rotation_deriv
    (WilsonSplit.directionSymbol 1 (k 1)))).mul (WilsonSplit.rotation_deriv
    (WilsonSplit.directionSymbol 2 (k 2)))
  simp only [onsiteCoin_zero, LocalUnitary.rotation, Real.cos_zero, Real.sin_zero,
    Complex.ofReal_one, Complex.ofReal_zero, mul_zero, zero_smul, one_smul,
    add_zero, mul_one, one_mul, Pi.mul_apply] at h
  have hd : (-Complex.I) • WilsonSplit.onsiteHamiltonian +
      Complex.I • WilsonSplit.directionSymbol 0 (k 0) +
      Complex.I • WilsonSplit.directionSymbol 1 (k 1) +
      Complex.I • WilsonSplit.directionSymbol 2 (k 2) =
      (-Complex.I) • hamiltonian k (DomainWallSpectrum.wilson k) := by
    rw [← WilsonSplit.generator_identity]
    simp only [Fin.sum_univ_three]
    module
  rw [← hd]
  exact h

end PMAction.VacuumSplit
