import PMAction.EllipticLocal
import PMAction.VacuumDifferential

/-! A whole punctured momentum neighborhood, uniform in direction, at each
fixed nonzero tick below π/10. The radius may still depend on the tick. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumLocalGap
open Matrix ConcreteFermion VacuumSchur VacuumDifferential VacuumPrincipal
open scoped Matrix.Norms.L2Operator

theorem schur_local_isUnit (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) :
    ∃ r : ℝ, 0<r ∧ ∀ k : Fin 3 → ℝ, k ≠ 0 → ‖k‖<r → IsUnit (schur t k) := by
  have hhalf : |t|≤1/2 := by linarith [Real.pi_lt_four]
  exact EllipticLocal.local_isUnit (schur t) (differential t) (energySq t) (minSpeedSq t)
    (minSpeedSq_pos t ht hb) (schur_zero t) (differentiable_schur t ht hhalf).hasFDerivAt
    (differential_square t ht hhalf) (differential_coercive t ht hb)

/-- Nonlinear exclusion in all momentum directions simultaneously, for each
fixed tick in the stated interval. No physical tick or spatial continuum is selected. -/
theorem local_fixed_exclusion (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) :
    ∃ r : ℝ, 0<r ∧ ∀ k : Fin 3 → ℝ, k ≠ 0 → ‖k‖<r → ∀ v : Sites → ℂ,
      VacuumSplit.momentumUpdate k t*ᵥv=v → v=0 := by
  have hhalf : |t|≤1/2 := by linarith [Real.pi_lt_four]
  obtain ⟨rS, hrS, hS⟩ := schur_local_isUnit t ht hb
  obtain ⟨rD, hrD, hD⟩ := gapped_neighborhood t ht hhalf
  refine ⟨min rS rD, lt_min hrS hrD, ?_⟩
  intro k hk hkr v hv
  have hd := hD k (hkr.trans_le (min_le_right rS rD))
  have hs := hS k hk (hkr.trans_le (min_le_left rS rD))
  have hu := (defect_isUnit_iff_schur t k hd).mpr hs
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  simp only [defect, sub_mulVec, one_mulVec, hv, sub_self, mulVec_zero]

/-- In a sufficiently small ball, the only momentum supporting a nonzero
stationary vector is the origin. The ball is shared by every direction. -/
theorem local_fixed_only_at_origin (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) :
    ∃ r : ℝ, 0<r ∧ ∀ k : Fin 3 → ℝ, ‖k‖<r → ∀ v : Sites → ℂ, v ≠ 0 →
      VacuumSplit.momentumUpdate k t*ᵥv=v → k=0 := by
  obtain ⟨r, hr, h⟩ := local_fixed_exclusion t ht hb
  refine ⟨r, hr, ?_⟩
  intro k hk v hv hf
  by_contra hzero
  exact hv (h k hzero hk v hf)

end PMAction.VacuumLocalGap
