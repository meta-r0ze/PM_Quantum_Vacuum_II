import PMAction.NormalizedSchur
import PMAction.EllipticLocal

/-! One near-origin momentum neighborhood for all sufficiently small nonzero ticks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.JointVacuumGap
open Matrix ConcreteFermion NormalizedIncrement NormalizedSchur Filter Topology
open scoped Matrix.Norms.L2Operator

def jointDerivative : Joint →L[ℝ] Spin := fderiv ℝ S 0

def momentumDerivative : Momentum →L[ℝ] Spin :=
  jointDerivative.comp (ContinuousLinearMap.inr ℝ ℝ Momentum)

theorem momentumDerivative_formula (p : Momentum) :
    momentumDerivative p=(-Complex.I) • kinetic p := by
  have hpath : HasDerivAt (fun s : ℝ => ((0 : ℝ), fun j : Fin 3 => s*p j)) (0,p) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const p)
    simpa only [id_eq, one_smul, Pi.smul_def, smul_eq_mul] using! h
  have h := analytic_S.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hpath (by ext <;> simp)
  have hr : HasDerivAt (fun s : ℝ => S (0,fun j => s*p j)) (momentumDerivative p) 0 := by
    simpa only [jointDerivative, momentumDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Function.comp_def] using! h
  exact hr.unique (S_momentum_deriv p)

def energySq (p : Momentum) : ℝ := p 0^2+p 1^2+p 2^2

theorem momentumDerivative_square (p : Momentum) :
    momentumDerivative p*momentumDerivative p=-(energySq p • (1 : Spin)) := by
  have hp : kinetic p*kinetic p=energySq p • (1 : Spin) := by
    simpa [kinetic, energySq] using (Dirac.dispersion_iff_clifford alpha beta).mpr clifford p 0
  rw [momentumDerivative_formula]
  simp only [smul_mul_smul_comm, neg_mul_neg, Complex.I_mul_I, hp, neg_smul, one_smul]

theorem schur_uniform_isUnit : ∃ r : ℝ, 0<r ∧ ∀ t : ℝ, |t|<r →
    ∀ k : Momentum, k ≠ 0 → ‖k‖<r → IsUnit (S (t,k)) := by
  apply EllipticLocal.parameter_local_isUnit S jointDerivative momentumDerivative energySq 1
    (by norm_num) S_axis_zero analytic_S.hasStrictFDerivAt
  · intro p
    rfl
  · exact momentumDerivative_square
  · intro p
    simpa only [one_mul, energySq] using VacuumDifferential.norm_sq_le_sum p

theorem D_neighborhood : ∃ r : ℝ, 0<r ∧ ∀ z : Joint, ‖z‖<r → IsUnit (D z) := by
  have ha : AnalyticAt ℝ D 0 := analytic_block _ _
  have he : ∀ᶠ z : Joint in 𝓝 0, IsUnit (D z) :=
    ha.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds D_origin_isUnit)
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r, hr, fun z hz => h (by simpa only [dist_zero_right] using hz)⟩

/-- The same positive bound works jointly for tick and momentum. -/
theorem joint_local_defect_isUnit : ∃ r : ℝ, 0<r ∧ ∀ t : ℝ, t ≠ 0 → |t|<r →
    ∀ k : Momentum, k ≠ 0 → ‖k‖<r → IsUnit (VacuumSchur.defect t k) := by
  obtain ⟨rS, hrS, hS⟩ := schur_uniform_isUnit
  obtain ⟨rD, hrD, hD⟩ := D_neighborhood
  refine ⟨min rS rD, lt_min hrS hrD, ?_⟩
  intro t ht htr k hk hkr
  have hd : IsUnit (D (t,k)) := hD (t,k) (by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_lt (htr.trans_le (min_le_right rS rD)) (hkr.trans_le (min_le_right rS rD)))
  have hs := hS t (htr.trans_le (min_le_left rS rD)) k hk (hkr.trans_le (min_le_left rS rD))
  have hu := (increment_isUnit_iff (t,k) hd).mpr hs
  have hh := IsUnit.smul (Units.mk0 t ht) hu
  change IsUnit (t • increment (t,k)) at hh
  rw [increment_identity] at hh
  exact hh

end PMAction.JointVacuumGap
