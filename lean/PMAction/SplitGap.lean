import PMAction.VacuumErrorRate
import Mathlib.Analysis.Normed.Ring.Units

/-! Fixed-tick spectral safety from the actual split's linear remainder.
The safe tick depends on the inverse Hamiltonian gap; this does not establish
one uniform tick all the way to the gapless origin. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.SplitGap
open Matrix ConcreteFermion VacuumIteration VacuumErrorRate
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

theorem hamiltonian_isUnit (k : Fin 3 → ℝ)
    (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi) (hk : k ≠ 0) :
    IsUnit (hamiltonian k (DomainWallSpectrum.wilson k)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w he
  have hz : hamiltonian k (DomainWallSpectrum.wilson k)*ᵥ(v-w)=0 := by
    rw [mulVec_sub, he, sub_self]
  have hv : v-w=0 := by
    by_contra hv
    exact hk (DomainWallSpectrum.wilson_point_zero_only_at_origin alpha beta gamma k
      clifford gamma_square beta_gamma alpha_gamma hcell (v-w) hv hz)
  exact sub_eq_zero.mp hv

theorem generator_isUnit (k : Fin 3 → ℝ)
    (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi) (hk : k ≠ 0) : IsUnit (generator k) := by
  exact IsUnit.smul (Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero))
    (hamiltonian_isUnit k hcell hk)

theorem linear_remainder (k : Fin 3 → ℝ) (h : ℝ) :
    ‖VacuumSplit.momentumUpdate k h-1-h • generator k‖ ≤ speedBound^2*h^2 := by
  have hr := (splitPath k).remainder h
  simpa only [split_value, VacuumSplit.momentumUpdate_zero, split_speed, split_velocity_zero] using hr

theorem scaled_remainder (k : Fin 3 → ℝ) (h : ℝ) (hh : h ≠ 0) :
    ‖h⁻¹ • (VacuumSplit.momentumUpdate k h-1)-generator k‖ ≤ speedBound^2*|h| := by
  have hi : h⁻¹ • (VacuumSplit.momentumUpdate k h-1)-generator k =
      h⁻¹ • (VacuumSplit.momentumUpdate k h-1-h • generator k) := by
    symm
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul]
  rw [hi, norm_smul, Real.norm_eq_abs, abs_inv]
  refine (mul_le_mul_of_nonneg_left (linear_remainder k h) (inv_nonneg.mpr (abs_nonneg h))).trans_eq ?_
  have hne : |h| ≠ 0 := abs_ne_zero.mpr hh
  rw [← sq_abs h]
  field_simp

/-- Invertibility of the normalized split defect under a proved gap test. -/
theorem scaled_defect_isUnit (k : Fin 3 → ℝ) (h : ℝ) (hh : h ≠ 0)
    (hG : IsUnit (generator k))
    (hsafe : ‖(generator k)⁻¹‖*speedBound^2*|h| < 1) :
    IsUnit (h⁻¹ • (VacuumSplit.momentumUpdate k h-1)) := by
  let S : M := h⁻¹ • (VacuumSplit.momentumUpdate k h-1)
  let E : M := (generator k)⁻¹*(S-generator k)
  have hE : ‖E‖ < 1 := by
    calc
      ‖E‖ ≤ ‖(generator k)⁻¹‖*‖S-generator k‖ := norm_mul_le _ _
      _ ≤ ‖(generator k)⁻¹‖*(speedBound^2*|h|) :=
        mul_le_mul_of_nonneg_left (scaled_remainder k h hh) (norm_nonneg _)
      _ < 1 := by simpa only [mul_assoc] using hsafe
  have hunit : IsUnit (1+E) := by
    have hu := IsUnit.one_sub_of_norm_lt_one (show ‖-E‖<1 by simpa only [norm_neg] using hE)
    simpa only [sub_neg_eq_add] using hu
  have hcancel : generator k*(generator k)⁻¹=1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG)
  have hi : generator k*(1+E)=S := by
    dsimp only [E]
    rw [mul_add, mul_one, ← mul_assoc, hcancel, one_mul]
    abel
  change IsUnit S
  rw [← hi]
  exact hG.mul hunit

/-- No nonzero stationary vector can survive the inverse-gap tick test. -/
theorem fixed_vector_eq_zero (k : Fin 3 → ℝ) (h : ℝ) (hh : h ≠ 0)
    (hG : IsUnit (generator k))
    (hsafe : ‖(generator k)⁻¹‖*speedBound^2*|h| < 1)
    (v : Sites → ℂ) (hv : VacuumSplit.momentumUpdate k h*ᵥv=v) : v=0 := by
  have hu := scaled_defect_isUnit k h hh hG hsafe
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  simp only [smul_mulVec, sub_mulVec, one_mulVec, hv, sub_self, smul_zero, mulVec_zero]

/-- A strictly positive certified radius at every nonzero momentum in the cell. -/
def safeRadius (k : Fin 3 → ℝ) : ℝ := 1/(‖(generator k)⁻¹‖*speedBound^2+1)

theorem safeRadius_pos (k : Fin 3 → ℝ) : 0 < safeRadius k := by
  unfold safeRadius
  positivity

theorem safeRadius_test (k : Fin 3 → ℝ) (h : ℝ) (hs : |h|<safeRadius k) :
    ‖(generator k)⁻¹‖*speedBound^2*|h| < 1 := by
  have hnon : 0 ≤ ‖(generator k)⁻¹‖*speedBound^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hd : 0 < ‖(generator k)⁻¹‖*speedBound^2+1 := by positivity
  have ht := (lt_div_iff₀ hd).mp hs
  nlinarith [abs_nonneg h]

theorem nonzero_momentum_fixed_eq_zero (k : Fin 3 → ℝ)
    (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi) (hk : k ≠ 0)
    (h : ℝ) (hh : h ≠ 0) (hs : |h|<safeRadius k)
    (v : Sites → ℂ) (hv : VacuumSplit.momentumUpdate k h*ᵥv=v) : v=0 :=
  fixed_vector_eq_zero k h hh (generator_isUnit k hcell hk) (safeRadius_test k h hs) v hv

end PMAction.SplitGap
