import PMAction.VacuumSchur

/-! Nonlinear fixed-mode exclusion on each fixed momentum ray near the origin.
The neighborhood may depend on both the tick and the direction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumRay
open Matrix ConcreteFermion VacuumTangent VacuumSchur Filter Topology
open scoped Matrix.Norms.L2Operator

theorem ray_defect_eventually_isUnit (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10)
    (p : Fin 3 → ℝ) (hp : p ≠ 0) :
    ∀ᶠ s : ℝ in 𝓝[≠] 0, IsUnit (defect t (fun j => s*p j)) := by
  have hhalf : |t|≤1/2 := by linarith [Real.pi_lt_four]
  have hderiv := schur_deriv t ht hhalf p
  have hlim := hderiv.tendsto_slope_zero
  simp only [zero_add, zero_mul, ← Pi.zero_def, schur_zero, sub_zero] at hlim
  have hP : IsUnit ((-Complex.I) • VacuumTangent.principal t p) :=
    IsUnit.smul (Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero))
      (VacuumPrincipal.principal_isUnit t ht hb p hp)
  have heS := hlim.eventually (Units.isOpen.mem_nhds hP)
  have hc : Continuous (fun s : ℝ => (fun j : Fin 3 => s*p j)) := by fun_prop
  have hDlim := ((continuous_blockD t).comp hc).tendsto (0 : ℝ)
  have hz : (fun j : Fin 3 => (0 : ℝ)*p j)=(0 : Fin 3 → ℝ) := by funext j; simp
  simp only [Function.comp_def] at hDlim
  rw [hz] at hDlim
  have heD : ∀ᶠ s : ℝ in 𝓝[≠] 0, IsUnit (blockD t (fun j => s*p j)) :=
    (hDlim.eventually (Units.isOpen.mem_nhds (blockD_isUnit t ht hhalf))).filter_mono
      nhdsWithin_le_nhds
  have hn : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  filter_upwards [heS, heD, hn] with s hs hD hne
  have hS := IsUnit.smul (Units.mk0 s hne) hs
  change IsUnit (s • (s⁻¹ • schur t (fun j => s*p j))) at hS
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul] at hS
  exact (defect_isUnit_iff_schur t _ hD).mpr hS

/-- At each admissible fixed tick, every fixed nonzero direction has a
punctured interval with no nonzero stationary vector of the actual split. -/
theorem ray_fixed_exclusion (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10)
    (p : Fin 3 → ℝ) (hp : p ≠ 0) :
    ∃ r : ℝ, 0<r ∧ ∀ s : ℝ, s ≠ 0 → |s|<r → ∀ v : Sites → ℂ,
      VacuumSplit.momentumUpdate (fun j => s*p j) t*ᵥv=v → v=0 := by
  have he := ray_defect_eventually_isUnit t ht hb p hp
  obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨r, hr, ?_⟩
  intro s hs hsbound v hv
  have hunit : IsUnit (defect t (fun j => s*p j)) := h
    ⟨by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hsbound,
     by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs⟩
  apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simp only [defect, sub_mulVec, one_mulVec, hv, sub_self, mulVec_zero]

end PMAction.VacuumRay
