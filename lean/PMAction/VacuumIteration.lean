import PMAction.IterationError
import PMAction.MatrixEvolutionSlope
import PMAction.VacuumGenerator
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Fixed-time convergence of the actual corrected momentum split

Errors are measured in the Euclidean operator norm, where unitary factors are
contractions. The prior derivative theorem supplies a vanishing local slope
defect. No unproved quadratic remainder or uniform-in-momentum rate is assumed.
This does not exclude extra unit eigenphases at a fixed nonzero tick size.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumIteration
open Matrix ConcreteFermion Filter Topology
open scoped Matrix.Norms.L2Operator

local notation "M" => Matrix Sites Sites ℂ

theorem direction_hermitian (j : Fin 3) (q : ℝ) : (WilsonSplit.directionSymbol j q).IsHermitian := by
  have hb := (beta_hermitian.smul (IsSelfAdjoint.all (Real.cos q))).sub
    ((alpha_hermitian j).smul (IsSelfAdjoint.all (Real.sin q)))
  change (fromBlocks _ 0 0 _)ᴴ = fromBlocks _ 0 0 _
  simp only [fromBlocks_conjTranspose, hb.eq, conjTranspose_zero]

theorem direction_square (j : Fin 3) (q : ℝ) :
    WilsonSplit.directionSymbol j q * WilsonSplit.directionSymbol j q = 1 := by
  let B : Spin := (Real.cos q) • beta - (Real.sin q) • alpha j
  have ha : beta * alpha j + alpha j * beta = 0 := by
    simpa only [add_comm] using clifford.2.2.2 j
  have hb : B*B = 1 := by
    calc
      B*B = (Real.cos q * Real.cos q) • (beta*beta) +
          (Real.sin q * Real.sin q) • (alpha j*alpha j) -
          (Real.cos q * Real.sin q) • (beta*alpha j+alpha j*beta) := by
        simp only [B, sub_mul, mul_sub, smul_mul_smul_comm, smul_add,
          mul_comm (Real.sin q) (Real.cos q)]
        module
      _ = 1 := by
        rw [beta_square, clifford.1 j, ha]
        simp only [smul_zero, sub_zero, ← add_smul]
        have ht : Real.cos q * Real.cos q + Real.sin q * Real.sin q = 1 := by
          nlinarith [Real.sin_sq_add_cos_sq q]
        rw [ht, one_smul]
  change fromBlocks B 0 0 B * fromBlocks B 0 0 B = 1
  simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add, hb, fromBlocks_one]

theorem momentum_unitary (k : Fin 3 → ℝ) (h : ℝ) :
    VacuumSplit.momentumUpdate k h ∈ unitary M := by
  have hr (j : Fin 3) := LocalUnitary.rotation_unitary (WilsonSplit.directionSymbol j (k j)) h
    (direction_hermitian j _) (direction_square j _)
  exact (unitary M).mul_mem ((unitary M).mul_mem ((unitary M).mul_mem
    (VacuumSplit.onsiteCoin_unitary h) (hr 0)) (hr 1)) (hr 2)

def generator (k : Fin 3 → ℝ) : M := (-Complex.I) • hamiltonian k (DomainWallSpectrum.wilson k)
def exactStep (k : Fin 3 → ℝ) (h : ℝ) : M := NormedSpace.exp (h • generator k)

theorem exact_zero (k : Fin 3 → ℝ) : exactStep k 0 = 1 := by simp [exactStep]

theorem exact_unitary (k : Fin 3 → ℝ) (h : ℝ) : exactStep k h ∈ unitary M := by
  have he : exactStep k h = NormedSpace.exp ((-Complex.I*(h : ℂ)) •
      hamiltonian k (DomainWallSpectrum.wilson k)) := by
    simp [exactStep, generator, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rw [he]
  exact VacuumSplit.exp_unitary _ (hamiltonian_hermitian _ _) h

theorem exact_slope (k : Fin 3 → ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ • (exactStep k h-1)) (𝓝[≠] 0) (𝓝 (generator k)) := by
  exact MatrixEvolutionSlope.exponential_slope (generator k)

/-- A topological slope statement transfers the earlier finite-matrix
derivative to the Euclidean operator norm without assuming the norms equal. -/
theorem split_slope (k : Fin 3 → ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ • (VacuumSplit.momentumUpdate k h-1))
      (𝓝[≠] 0) (𝓝 (generator k)) := by
  have h := (VacuumSplit.momentumUpdate_deriv k).tendsto_slope_zero
  simpa only [zero_add, VacuumSplit.momentumUpdate_zero, generator] using h

theorem local_slope_defect (k : Fin 3 → ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ • (VacuumSplit.momentumUpdate k h-exactStep k h))
      (𝓝[≠] 0) (𝓝 0) := by
  have he := exact_slope k
  have hd := (split_slope k).sub he
  simp only [sub_self] at hd
  have hi (h : ℝ) : h⁻¹ • (VacuumSplit.momentumUpdate k h-1) - h⁻¹ • (exactStep k h-1) =
      h⁻¹ • (VacuumSplit.momentumUpdate k h-exactStep k h) := by
    rw [← smul_sub]
    congr 1
    abel
  simpa only [hi] using hd

theorem exact_power (k : Fin 3 → ℝ) (T : ℝ) (n : ℕ) :
    exactStep k (IterationError.mesh T n)^(n+1) = exactStep k T := by
  let : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
  unfold exactStep
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  unfold IterationError.mesh
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- A certified finite-step bound in terms of the actual one-step defect. -/
theorem accumulated_error_bound (k : Fin 3 → ℝ) (T : ℝ) (n : ℕ) :
    ‖VacuumSplit.momentumUpdate k (IterationError.mesh T n)^(n+1)-exactStep k T‖ ≤
      ((n+1 : ℕ) : ℝ)*‖VacuumSplit.momentumUpdate k (IterationError.mesh T n)-
        exactStep k (IterationError.mesh T n)‖ := by
  rw [← exact_power k T n]
  exact IterationError.power_error_bound _ _
    (le_of_eq (CStarRing.norm_of_mem_unitary (momentum_unitary _ _)))
    (le_of_eq (CStarRing.norm_of_mem_unitary (exact_unitary _ _))) (n+1)

/-- At each fixed momentum and fixed real elapsed time, refining the tick
converges to the exact Wilson Hamiltonian evolution. No physical scale is selected. -/
theorem fixed_time_norm_convergence (k : Fin 3 → ℝ) (T : ℝ) :
    Tendsto (fun n : ℕ => ‖VacuumSplit.momentumUpdate k (IterationError.mesh T n)^(n+1)-
      exactStep k T‖) atTop (𝓝 0) := by
  by_cases hT : T = 0
  · subst T
    simp [IterationError.mesh, VacuumSplit.momentumUpdate_zero, exact_zero]
  · have h := IterationError.powers_converge (VacuumSplit.momentumUpdate k) (exactStep k)
      (fun h => le_of_eq (CStarRing.norm_of_mem_unitary (momentum_unitary k h)))
      (fun h => le_of_eq (CStarRing.norm_of_mem_unitary (exact_unitary k h))) hT (local_slope_defect k)
    simpa only [exact_power] using h

theorem fixed_time_convergence (k : Fin 3 → ℝ) (T : ℝ) :
    Tendsto (fun n : ℕ => VacuumSplit.momentumUpdate k (IterationError.mesh T n)^(n+1))
      atTop (𝓝 (exactStep k T)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact fixed_time_norm_convergence k T

/-- Every fixed internal state converges under the refined split evolution. -/
theorem state_convergence (k : Fin 3 → ℝ) (T : ℝ) (ψ : Sites → ℂ) :
    Tendsto (fun n : ℕ =>
      (VacuumSplit.momentumUpdate k (IterationError.mesh T n)^(n+1)) *ᵥ ψ)
      atTop (𝓝 (exactStep k T *ᵥ ψ)) := by
  have hc : Continuous (fun A : M => A *ᵥ ψ) :=
    Continuous.matrix_mulVec continuous_id continuous_const
  exact hc.continuousAt.tendsto.comp (fixed_time_convergence k T)

end PMAction.VacuumIteration
