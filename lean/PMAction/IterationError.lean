import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-! Stability for repeated contractions. Noncommuting one-step operators are
allowed; no replacement of a split product by an exact exponential is assumed. -/
noncomputable section
namespace PMAction.IterationError
open Filter Topology

variable {A : Type*} [NormedRing A] [NormOneClass A]

theorem power_error_bound (u v : A) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖u^n-v^n‖ ≤ (n : ℝ)*‖u-v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : u^(n+1)-v^(n+1) = u*(u^n-v^n)+(u-v)*v^n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hp : ‖v^n‖ ≤ 1 := (norm_pow_le v n).trans (pow_le_one₀ (norm_nonneg v) hv)
    rw [he]
    calc
      ‖u*(u^n-v^n)+(u-v)*v^n‖ ≤ ‖u*(u^n-v^n)‖+‖(u-v)*v^n‖ := norm_add_le _ _
      _ ≤ ‖u‖*‖u^n-v^n‖+‖u-v‖*‖v^n‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1*((n : ℝ)*‖u-v‖)+‖u-v‖*1 :=
        add_le_add (mul_le_mul hu ih (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      _ = ((n+1 : ℕ) : ℝ)*‖u-v‖ := by push_cast; ring

theorem quadratic_error_bound (u v : A) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (C h : ℝ) (he : ‖u-v‖ ≤ C*h^2) (n : ℕ) :
    ‖u^n-v^n‖ ≤ (n : ℝ)*C*h^2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact (power_error_bound u v hu hv n).trans (by nlinarith [mul_le_mul_of_nonneg_left he hn])

def mesh (T : ℝ) (n : ℕ) : ℝ := T / (n+1 : ℕ)

theorem mesh_tends_zero (T : ℝ) : Tendsto (mesh T) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => T / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)

theorem mesh_tends_punctured {T : ℝ} (hT : T ≠ 0) : Tendsto (mesh T) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨mesh_tends_zero T, Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact div_ne_zero hT (by exact_mod_cast Nat.succ_ne_zero n)

variable [NormedSpace ℝ A]

omit [NormOneClass A] in
/-- A vanishing first-order local defect gives a vanishing accumulated defect.
No quadratic remainder constant is inferred from first differentiability. -/
theorem scaled_error_tends_zero (U V : ℝ → A) {T : ℝ} (hT : T ≠ 0)
    (he : Tendsto (fun h : ℝ => h⁻¹ • (U h-V h)) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)*‖U (mesh T n)-V (mesh T n)‖) atTop (𝓝 0) := by
  have hn := (he.comp (mesh_tends_punctured hT)).norm
  have hh := hn.const_mul |T|
  simp only [norm_zero, mul_zero] at hh
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hA : |T| ≠ 0 := abs_ne_zero.mpr hT
  simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, mesh, abs_div,
    abs_of_pos hN, inv_div]
  field_simp

theorem powers_converge (U V : ℝ → A) (hU : ∀ h, ‖U h‖ ≤ 1) (hV : ∀ h, ‖V h‖ ≤ 1)
    {T : ℝ} (hT : T ≠ 0)
    (he : Tendsto (fun h : ℝ => h⁻¹ • (U h-V h)) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖U (mesh T n)^(n+1)-V (mesh T n)^(n+1)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => power_error_bound _ _ (hU _) (hV _) (n+1))
  exact scaled_error_tends_zero U V hT he

end PMAction.IterationError
