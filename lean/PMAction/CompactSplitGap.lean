import PMAction.SplitGap
import Mathlib.Topology.Order.Compact

/-! Uniform fixed-tick exclusion on compact momentum regions avoiding the origin.
No uniform lower radius at the gapless origin is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.CompactSplitGap
open Matrix ConcreteFermion VacuumIteration VacuumErrorRate SplitGap
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

theorem continuous_generator : Continuous generator := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;>
    simp only [generator, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
      DomainWallSpectrum.wilson, Matrix.smul_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sum_apply]
  all_goals fun_prop

theorem safeRadius_continuousAt (k : Fin 3 → ℝ) (hG : IsUnit (generator k)) :
    ContinuousAt safeRadius k := by
  have hd : (generator k).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)
  have hi : ContinuousAt (fun k => (generator k)⁻¹) k := by
    apply (continuousAt_matrix_inv (generator k) ?_).comp continuous_generator.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  unfold safeRadius
  exact continuousAt_const.div ((hi.norm.mul_const (speedBound^2)).add_const 1) (by positivity)

theorem compact_radius {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hcell : ∀ k ∈ K, ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi)
    (hzero : ∀ k ∈ K, k ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ k ∈ K, r ≤ safeRadius k := by
  by_cases hne : K.Nonempty
  · have hc : ContinuousOn safeRadius K := fun k hk =>
      (safeRadius_continuousAt k (generator_isUnit k (hcell k hk) (hzero k hk))).continuousWithinAt
    obtain ⟨k, hk, hmin⟩ := hK.exists_isMinOn hne hc
    exact ⟨safeRadius k, safeRadius_pos k, fun q hq => hmin hq⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro k hk
    exact (hne ⟨k, hk⟩).elim

/-- One sufficiently small nonzero tick excludes stationary modes throughout
any compact subset of the momentum cell that avoids zero. -/
theorem compact_fixed_exclusion {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hcell : ∀ k ∈ K, ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi)
    (hzero : ∀ k ∈ K, k ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ k ∈ K, ∀ h : ℝ, h ≠ 0 → |h|<r →
      ∀ v : Sites → ℂ, VacuumSplit.momentumUpdate k h*ᵥv=v → v=0 := by
  obtain ⟨r, hr, hbound⟩ := compact_radius hK hcell hzero
  refine ⟨r, hr, ?_⟩
  intro k hk h hh hs v hv
  exact nonzero_momentum_fixed_eq_zero k (hcell k hk) (hzero k hk) h hh
    (hs.trans_le (hbound k hk)) v hv

end PMAction.CompactSplitGap
