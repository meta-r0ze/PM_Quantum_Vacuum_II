import PMAction.VacuumSchur

/-! Full momentum differentiability of the reduced vacuum equation. This
upgrades the earlier ray derivative to a uniform first-order remainder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumDifferential
open Matrix ConcreteFermion VacuumTangent VacuumSchur
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

theorem differentiable_update (t : ℝ) :
    Differentiable ℝ (fun k : Fin 3 → ℝ => VacuumSplit.momentumUpdate k t) := by
  unfold VacuumSplit.momentumUpdate LocalUnitary.rotation
  simp only [direction_eq]
  fun_prop

theorem differentiable_block (r c : Fin 4 → Sites) (t : ℝ) :
    Differentiable ℝ (fun k : Fin 3 → ℝ => (defect t k).submatrix r c) := by
  have hd := (differentiable_update t).sub_const (1 : M)
  have h := (submatrixCLM r c).differentiable.comp hd
  have he : (submatrixCLM r c : M → Spin)=(fun A : M => A.submatrix r c) :=
    LinearMap.coe_toContinuousLinearMap' (submatrixLinear r c)
  rw [he] at h
  simpa only [defect, Function.comp_def] using h

theorem differentiable_schur (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) :
    DifferentiableAt ℝ (schur t) (0 : Fin 3 → ℝ) := by
  have hA := differentiable_block vacuumIndex vacuumIndex t (0 : Fin 3 → ℝ)
  have hB := differentiable_block vacuumIndex complementIndex t (0 : Fin 3 → ℝ)
  have hC := differentiable_block complementIndex vacuumIndex t (0 : Fin 3 → ℝ)
  have hD := differentiable_block complementIndex complementIndex t (0 : Fin 3 → ℝ)
  change DifferentiableAt ℝ (blockA t) 0 at hA
  change DifferentiableAt ℝ (blockB t) 0 at hB
  change DifferentiableAt ℝ (blockC t) 0 at hC
  change DifferentiableAt ℝ (blockD t) 0 at hD
  have hi : DifferentiableAt ℝ (fun k : Fin 3 → ℝ => (blockD t k)⁻¹) 0 := by
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    apply hD.inverse
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (blockD_isUnit t ht hb)
    refine ⟨⟨blockD t 0, (blockD t 0)⁻¹, ?_, ?_⟩, rfl⟩
    · exact Matrix.mul_nonsing_inv _ hdet
    · exact Matrix.nonsing_inv_mul _ hdet
  simpa only [schur, Pi.sub_def, Pi.mul_def] using! hA.sub ((hB.mul hi).mul hC)

def differential (t : ℝ) : (Fin 3 → ℝ) →L[ℝ] Spin := fderiv ℝ (schur t) 0

theorem differential_formula (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) (p : Fin 3 → ℝ) :
    differential t p=(-Complex.I) • VacuumTangent.principal t p := by
  have h := (differentiable_schur t ht hb).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).smul_const p) (by simp)
  have hr : HasDerivAt (fun s : ℝ => schur t (fun j => s*p j)) (differential t p) 0 := by
    simpa only [differential, one_smul, Function.comp_def, id_eq, Pi.smul_def, smul_eq_mul] using h
  exact hr.unique (schur_deriv t ht hb p)

theorem differential_square (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) (p : Fin 3 → ℝ) :
    differential t p*differential t p=-(VacuumPrincipal.energySq t p • (1 : Spin)) := by
  rw [differential_formula t ht hb p]
  simp only [smul_mul_smul_comm, neg_mul_neg, Complex.I_mul_I,
    VacuumPrincipal.principal_square, neg_smul, one_smul]

theorem norm_sq_le_sum (p : Fin 3 → ℝ) : ‖p‖^2 ≤ p 0^2+p 1^2+p 2^2 := by
  let S : ℝ := p 0^2+p 1^2+p 2^2
  have hS : 0≤S := by dsimp [S]; positivity
  have hb : ‖p‖≤Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro j
    have hj : p j^2≤S := by
      have h := Finset.single_le_sum
        (fun l (_ : l ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (p l)) (Finset.mem_univ j)
      simpa only [Fin.sum_univ_three, S] using h
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S, sq_abs (p j), abs_nonneg (p j)]
  have hh := pow_le_pow_left₀ (norm_nonneg p) hb 2
  simpa only [Real.sq_sqrt hS, S] using hh

theorem differential_coercive (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) (p : Fin 3 → ℝ) :
    VacuumPrincipal.minSpeedSq t*‖p‖^2 ≤ VacuumPrincipal.energySq t p := by
  exact (mul_le_mul_of_nonneg_left (norm_sq_le_sum p)
    (VacuumPrincipal.minSpeedSq_pos t ht hb).le).trans (VacuumPrincipal.energySq_lower t p)

end PMAction.VacuumDifferential
