import PMAction.WilsonSplit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The split-symbol tangent is the specified Hamiltonian, not its finite-tick spectrum. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.WilsonSplit
open Matrix ConcreteFermion NormedSpace
open scoped Matrix.Norms.Operator
local instance {n : Type*} [Fintype n] : TopologicalSpace (Matrix n n ℂ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

lemma rotation_deriv {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) :
    HasDerivAt (LocalUnitary.rotation B) (Complex.I • B) (0 : ℝ) := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).ofReal_comp
  have h := (hc.smul_const (1 : Matrix n n ℂ)).add ((hs.const_mul Complex.I).smul_const B)
  convert! h using 1; first | rfl | simp


lemma onsiteCoin_eq (τ : ℝ) : onsiteCoin τ = exp (τ • ((-Complex.I) • onsiteHamiltonian)) := by
  rw [onsiteCoin, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply congrArg exp
  have hc : (-Complex.I)*(τ : ℂ)=(τ : ℂ)*(-Complex.I) := mul_comm _ _
  exact congrArg (fun c : ℂ => c • onsiteHamiltonian) hc

lemma onsiteCoin_deriv : HasDerivAt onsiteCoin ((-Complex.I) • onsiteHamiltonian) (0 : ℝ) := by
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • onsiteHamiltonian) (0 : ℝ)
  simpa only [← onsiteCoin_eq, zero_smul, NormedSpace.exp_zero, one_mul] using h

/-- Product in the same order as the proved finite-range update. -/
def momentumUpdate (k : Fin 3 → ℝ) (τ : ℝ) : Matrix Sites Sites ℂ :=
  onsiteCoin τ * LocalUnitary.rotation (directionSymbol 0 (k 0)) τ *
    LocalUnitary.rotation (directionSymbol 1 (k 1)) τ *
    LocalUnitary.rotation (directionSymbol 2 (k 2)) τ

theorem momentumUpdate_zero (k : Fin 3 → ℝ) : momentumUpdate k 0=1 := by
  simp [momentumUpdate, onsiteCoin, LocalUnitary.rotation]

/-- A checked first derivative; no claim of equality at nonzero tick size. -/
theorem momentumUpdate_deriv (k : Fin 3 → ℝ) :
    HasDerivAt (momentumUpdate k)
      ((-Complex.I) • hamiltonian k (DomainWallSpectrum.wilson k)) (0 : ℝ) := by
  have h := ((onsiteCoin_deriv.mul (rotation_deriv (directionSymbol 0 (k 0)))).mul
    (rotation_deriv (directionSymbol 1 (k 1)))).mul (rotation_deriv (directionSymbol 2 (k 2)))
  simp only [onsiteCoin, zero_smul, NormedSpace.exp_zero, LocalUnitary.rotation,
    Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_zero, zero_smul, one_smul, add_zero, mul_one, one_mul, Pi.mul_apply] at h
  have hd : (-Complex.I) • onsiteHamiltonian + Complex.I • directionSymbol 0 (k 0) +
      Complex.I • directionSymbol 1 (k 1) + Complex.I • directionSymbol 2 (k 2) =
      (-Complex.I) • hamiltonian k (DomainWallSpectrum.wilson k) := by
    rw [← generator_identity]
    simp only [Fin.sum_univ_three]
    module
  rw [← hd]
  exact h

end PMAction.WilsonSplit
