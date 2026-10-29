import PMAction.PathError
import PMAction.VacuumIteration

/-! Explicit, momentum-independent time-refinement bounds for the corrected split.
This controls time discretization for the chosen Wilson Hamiltonian, not a spatial
continuum limit or a physical choice of microscopic tick. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumErrorRate
open Matrix ConcreteFermion PathError Filter Topology
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

theorem exp_deriv (A : M) (t : ℝ) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp (h • A))
      (NormedSpace.exp (t • A)*A) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact MatrixEvolutionSlope.exponential_slope_at A t

theorem rotation_deriv (B : M) (hB : B*B=1) (t : ℝ) :
    HasDerivAt (LocalUnitary.rotation B)
      (LocalUnitary.rotation B t*(Complex.I • B)) t := by
  have hc := (Real.hasDerivAt_cos t).ofReal_comp
  have hs := (Real.hasDerivAt_sin t).ofReal_comp
  have hd := (hc.smul_const (1 : M)).add ((hs.const_mul Complex.I).smul_const B)
  have hi : LocalUnitary.rotation B t*(Complex.I • B) =
      ((-(Real.sin t) : ℝ) : ℂ) • (1 : M)+(Complex.I*(Real.cos t : ℂ)) • B := by
    simp only [LocalUnitary.rotation, add_mul, smul_mul_smul_comm, one_mul, hB]
    simp only [Complex.ofReal_neg]
    match_scalars <;> (ring_nf; all_goals simp)
  rw [hi]
  exact hd

def rotationPath (B : M) (hHerm : B.IsHermitian) (hB : B*B=1) : Path (A := M) :=
  Path.ofGenerator (LocalUnitary.rotation B) (Complex.I • B)
    (rotation_deriv B hB) (fun t => le_of_eq
      (CStarRing.norm_of_mem_unitary (LocalUnitary.rotation_unitary B t hHerm hB)))

def reversePath (B : M) (hHerm : B.IsHermitian) (hB : B*B=1) : Path (A := M) :=
  rotationPath (-B) hHerm.neg (by simpa only [neg_mul_neg] using hB)

def exponentialPath (H : M) (hH : H.IsHermitian) : Path (A := M) :=
  Path.ofGenerator (fun t => NormedSpace.exp (t • ((-Complex.I) • H))) ((-Complex.I) • H)
    (exp_deriv _) (fun t => by
      have he : t • ((-Complex.I) • H) = (-Complex.I*(t : ℂ)) • H := by
        simp [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
      rw [he]
      exact le_of_eq (CStarRing.norm_of_mem_unitary (VacuumSplit.exp_unitary H hH t)))

theorem norm_involution (B : M) (hHerm : B.IsHermitian) (hB : B*B=1) : ‖B‖=1 := by
  exact CStarRing.norm_of_mem_unitary (show B ∈ unitary M from
    ⟨by simpa only [star_eq_conjTranspose, hHerm.eq] using hB,
     by simpa only [star_eq_conjTranspose, hHerm.eq] using hB⟩)

theorem rotation_speed (B : M) (hHerm : B.IsHermitian) (hB : B*B=1) :
    (rotationPath B hHerm hB).speed = 1 := by
  change ‖Complex.I • B‖=1
  simp [norm_smul, norm_involution B hHerm hB]

theorem reverse_speed (B : M) (hHerm : B.IsHermitian) (hB : B*B=1) :
    (reversePath B hHerm hB).speed = 1 :=
  rotation_speed (-B) hHerm.neg (by simpa only [neg_mul_neg] using hB)

theorem reverse_eq (B : M) (hHerm : B.IsHermitian) (t : ℝ) :
    LocalUnitary.rotation (-B) t = (LocalUnitary.rotation B t)ᴴ := by
  simp only [LocalUnitary.rotation, conjTranspose_add, conjTranspose_smul,
    conjTranspose_one, hHerm.eq, RCLike.star_def, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul, neg_smul, smul_neg]

/-- Exactly the seven primitive factors of the corrected split. -/
def splitPath (k : Fin 3 → ℝ) : Path (A := M) :=
  let b := reversePath VacuumSplit.beta8 VacuumSplit.beta8_hermitian VacuumSplit.beta8_square
  let d (j : Fin 3) := rotationPath (WilsonSplit.directionSymbol j (k j))
    (VacuumIteration.direction_hermitian j _) (VacuumIteration.direction_square j _)
  ((((exponentialPath VacuumSplit.wall (hamiltonian_hermitian 0 0)).mul
    ((b.mul b).mul b)).mul (d 0)).mul (d 1)).mul (d 2)

theorem split_value (k : Fin 3 → ℝ) (t : ℝ) :
    (splitPath k).value t = VacuumSplit.momentumUpdate k t := by
  change ((NormedSpace.exp (t • ((-Complex.I) • VacuumSplit.wall)) *
    ((LocalUnitary.rotation (-VacuumSplit.beta8) t *
      LocalUnitary.rotation (-VacuumSplit.beta8) t) *
      LocalUnitary.rotation (-VacuumSplit.beta8) t)) * _ * _) * _ = _
  rw [← VacuumSplit.wallCoin_eq, reverse_eq _ VacuumSplit.beta8_hermitian]
  simp only [VacuumSplit.momentumUpdate, VacuumSplit.onsiteCoin, VacuumSplit.rotation,
    pow_succ, pow_zero, one_mul, rotationPath, Path.ofGenerator]

def speedBound : ℝ := ‖VacuumSplit.wall‖+6

theorem speedBound_nonneg : 0 ≤ speedBound := by
  unfold speedBound
  positivity

theorem split_speed (k : Fin 3 → ℝ) : (splitPath k).speed = speedBound := by
  change (((‖(-Complex.I) • VacuumSplit.wall‖+
    ((‖Complex.I • (-VacuumSplit.beta8)‖+‖Complex.I • (-VacuumSplit.beta8)‖)+
      ‖Complex.I • (-VacuumSplit.beta8)‖))+
      ‖Complex.I • WilsonSplit.directionSymbol 0 (k 0)‖)+
      ‖Complex.I • WilsonSplit.directionSymbol 1 (k 1)‖)+
      ‖Complex.I • WilsonSplit.directionSymbol 2 (k 2)‖ = speedBound
  unfold speedBound
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul]
  rw [norm_involution _ VacuumSplit.beta8_hermitian VacuumSplit.beta8_square]
  rw [norm_involution _ (VacuumIteration.direction_hermitian 0 _) (VacuumIteration.direction_square 0 _),
      norm_involution _ (VacuumIteration.direction_hermitian 1 _) (VacuumIteration.direction_square 1 _),
      norm_involution _ (VacuumIteration.direction_hermitian 2 _) (VacuumIteration.direction_square 2 _)]
  ring

set_option maxHeartbeats 1000000 in
theorem split_velocity_zero (k : Fin 3 → ℝ) :
    (splitPath k).velocity 0 = VacuumIteration.generator k := by
  have hd : HasDerivAt (VacuumSplit.momentumUpdate k) ((splitPath k).velocity 0) 0 := by
    have hh := (splitPath k).deriv_value 0
    have hf : (splitPath k).value = VacuumSplit.momentumUpdate k := funext (split_value k)
    rw [hf] at hh
    exact hh
  have he : HasDerivAt (VacuumSplit.momentumUpdate k) (VacuumIteration.generator k) 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [zero_add, VacuumSplit.momentumUpdate_zero] using VacuumIteration.split_slope k
  exact hd.unique he

theorem generator_norm_bound (k : Fin 3 → ℝ) : ‖VacuumIteration.generator k‖ ≤ speedBound := by
  rw [← split_velocity_zero k, ← split_speed k]
  exact (splitPath k).norm_velocity 0

/-- A global-in-tick, momentum-independent one-step quadratic defect estimate. -/
theorem one_step_error (k : Fin 3 → ℝ) (h : ℝ) :
    ‖VacuumSplit.momentumUpdate k h-VacuumIteration.exactStep k h‖ ≤
      (2*speedBound^2)*h^2 := by
  have hs := (splitPath k).remainder h
  simp only [split_value, VacuumSplit.momentumUpdate_zero, split_speed, split_velocity_zero] at hs
  let p := exponentialPath (hamiltonian k (DomainWallSpectrum.wilson k)) (hamiltonian_hermitian _ _)
  have he := p.remainder h
  have hpv (t : ℝ) : p.value t = VacuumIteration.exactStep k t := rfl
  have hp0 : p.velocity 0 = VacuumIteration.generator k := by
    change NormedSpace.exp ((0 : ℝ) • VacuumIteration.generator k)*VacuumIteration.generator k = _
    simp
  have hps : p.speed = ‖VacuumIteration.generator k‖ := rfl
  simp only [hpv, hp0, hps, VacuumIteration.exact_zero] at he
  have he' : ‖VacuumIteration.exactStep k h-1-h • VacuumIteration.generator k‖ ≤ speedBound^2*h^2 :=
    he.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (generator_norm_bound k) 2) (sq_nonneg h))
  have hi : VacuumSplit.momentumUpdate k h-VacuumIteration.exactStep k h =
      (VacuumSplit.momentumUpdate k h-1-h • VacuumIteration.generator k)-
      (VacuumIteration.exactStep k h-1-h • VacuumIteration.generator k) := by abel
  rw [hi]
  exact (norm_sub_le _ _).trans (by nlinarith)

/-- After N=n+1 steps at fixed elapsed time, the operator error is at most C T²/N.
The same constant works at every momentum. -/
theorem fixed_time_error (k : Fin 3 → ℝ) (T : ℝ) (n : ℕ) :
    ‖VacuumSplit.momentumUpdate k (IterationError.mesh T n)^(n+1)-
      VacuumIteration.exactStep k T‖ ≤ (2*speedBound^2)*T^2/((n+1 : ℕ) : ℝ) := by
  have he := IterationError.quadratic_error_bound
    (VacuumSplit.momentumUpdate k (IterationError.mesh T n))
    (VacuumIteration.exactStep k (IterationError.mesh T n))
    (le_of_eq (CStarRing.norm_of_mem_unitary (VacuumIteration.momentum_unitary _ _)))
    (le_of_eq (CStarRing.norm_of_mem_unitary (VacuumIteration.exact_unitary _ _)))
    (2*speedBound^2) (IterationError.mesh T n) (one_step_error k _) (n+1)
  rw [VacuumIteration.exact_power] at he
  refine he.trans_eq ?_
  unfold IterationError.mesh
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp


end PMAction.VacuumErrorRate
