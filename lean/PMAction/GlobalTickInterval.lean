import PMAction.JointVacuumGap
import PMAction.CompactSplitGap

/-! A positive tick interval valid over the entire momentum cell for the
actual corrected split. Existence is proved; no numerical endpoint or physical
microscopic tick is selected. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.GlobalTickInterval
open Matrix ConcreteFermion NormalizedIncrement
open scoped Matrix.Norms.L2Operator

def InCell (k : Momentum) : Prop := ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi

theorem norm_le_pi (k : Momentum) (hk : InCell k) : ‖k‖≤Real.pi := by
  apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
  intro j
  simpa only [Real.norm_eq_abs] using abs_le.mpr (hk j)

theorem cell_of_norm_le_pi (k : Momentum) (hk : ‖k‖≤Real.pi) : InCell k := by
  intro j
  apply abs_le.mp
  have h := (norm_le_pi_norm k j).trans hk
  simpa only [Real.norm_eq_abs] using h

/-- One strictly positive interval excludes extra stationary modes throughout
[-pi,pi]^3, including momenta arbitrarily close to zero. -/
theorem global_fixed_only_at_origin :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/2 ∧ ∀ t : ℝ, t ≠ 0 → |t|<δ →
      ∀ k : Momentum, InCell k → ∀ v : Sites → ℂ, v ≠ 0 →
        VacuumSplit.momentumUpdate k t*ᵥv=v → k=0 := by
  obtain ⟨r, hr, hnear⟩ := JointVacuumGap.joint_local_defect_isUnit
  let K : Set Momentum := Metric.closedBall 0 Real.pi ∩ {k | r/2≤‖k‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : Momentum) Real.pi).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hcell : ∀ k ∈ K, InCell k := by
    intro k hk
    apply cell_of_norm_le_pi k
    simpa only [Metric.mem_closedBall, dist_zero_right] using hk.1
  have hzero : ∀ k ∈ K, k ≠ 0 := by
    intro k hk hz
    have hh : r/2≤‖k‖ := hk.2
    rw [hz, norm_zero] at hh
    linarith
  obtain ⟨d, hd, hfar⟩ := CompactSplitGap.compact_fixed_exclusion hK hcell hzero
  refine ⟨min r (min d (1/2)), lt_min hr (lt_min hd (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro t ht hstep k hk v hv hf
  by_contra hkn
  by_cases hkr : ‖k‖<r
  · have hu := hnear t ht (hstep.trans_le (min_le_left _ _)) k hkn hkr
    apply hv
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu
    simp only [VacuumSchur.defect, sub_mulVec, one_mulVec, hf, sub_self, mulVec_zero]
  · have hmem : k ∈ K := ⟨by
        simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_pi k hk,
      (show r/2≤r by linarith).trans (le_of_not_gt hkr)⟩
    exact hv (hfar k hmem t ht
      (hstep.trans_le ((min_le_right _ _).trans (min_le_left _ _))) v hf)

/-- At sufficiently small nonzero ticks, the full split fixed space equals
the actual Wilson Hamiltonian kernel everywhere in the momentum cell. -/
theorem global_fixed_iff :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, t ≠ 0 → |t|<δ → ∀ k : Momentum, InCell k →
      ∀ v : Sites → ℂ, VacuumSplit.momentumUpdate k t*ᵥv=v ↔
        hamiltonian k (DomainWallSpectrum.wilson k)*ᵥv=0 := by
  obtain ⟨δ, hδ, hhalf, hglobal⟩ := global_fixed_only_at_origin
  refine ⟨δ, hδ, ?_⟩
  intro t ht hs k hk v
  by_cases hzero : k=0
  · subst k
    simpa [VacuumSplit.wall, DomainWallSpectrum.wilson] using
      VacuumFixedSpace.origin_split_fixed_iff t ht (hs.le.trans hhalf) v
  · constructor
    · intro hf
      have hv : v=0 := by
        by_contra hv
        exact hzero (hglobal t ht hs k hk v hv hf)
      rw [hv, mulVec_zero]
    · intro hH
      have hu := SplitGap.hamiltonian_isUnit k hk hzero
      have hv : v=0 := by
        apply Matrix.mulVec_injective_iff_isUnit.mpr hu
        simpa only [mulVec_zero] using hH
      rw [hv, mulVec_zero]

end PMAction.GlobalTickInterval
