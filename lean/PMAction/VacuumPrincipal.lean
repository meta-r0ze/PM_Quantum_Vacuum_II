import PMAction.VacuumTangent

/-! Certified nondegeneracy and a finite-tick degeneracy of the vacuum principal symbol.
These statements concern the first momentum derivative, not the full nonlinear spectrum. -/
noncomputable section
namespace PMAction.VacuumPrincipal
open Matrix ConcreteFermion VacuumTangent Topology

def energySq (t : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  (weights t 0*p 0)^2+(weights t 1*p 1)^2+(weights t 2*p 2)^2

theorem principal_square (t : ℝ) (p : Fin 3 → ℝ) :
    principal t p*principal t p=energySq t p • (1 : Spin) := by
  simpa [principal, energySq] using
    (Dirac.dispersion_iff_clifford alpha beta).mpr clifford (fun j => weights t j*p j) 0

theorem weights_ne_zero (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) :
    ∀ j, weights t j ≠ 0 := by
  have hlow := (abs_lt.mp hb).1
  have hhigh := (abs_lt.mp hb).2
  have hs : Real.sin t ≠ 0 := by
    rcases lt_or_gt_of_ne ht with hn | hp
    · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hn (by linarith [Real.pi_pos]))
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hp (by linarith [Real.pi_pos]))
  have h5 : Real.cos (5*t) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  have h3 : Real.cos (3*t) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have h1 : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  intro j
  fin_cases j
  · change Real.sin t*Real.cos (5*t) ≠ 0
    exact mul_ne_zero hs h5
  · change Real.sin t*Real.cos (3*t) ≠ 0
    exact mul_ne_zero hs h3
  · change Real.sin t*Real.cos t ≠ 0
    exact mul_ne_zero hs h1

theorem energySq_pos (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10)
    (p : Fin 3 → ℝ) (hp : p ≠ 0) : 0 < energySq t p := by
  have hw := weights_ne_zero t ht hb
  have hex : ∃ j, p j ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  obtain ⟨j, hj⟩ := hex
  have hs := sq_pos_of_ne_zero (mul_ne_zero (hw j) hj)
  have hbound := Finset.single_le_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (weights t l*p l))
    (Finset.mem_univ j)
  exact hs.trans_le (by simpa only [energySq, Fin.sum_univ_three] using hbound)

/-- A certified positive constant for a lower bound uniform in tangent direction. -/
def minSpeedSq (t : ℝ) : ℝ :=
  min ((weights t 0)^2) (min ((weights t 1)^2) ((weights t 2)^2))

theorem minSpeedSq_pos (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10) :
    0 < minSpeedSq t := by
  have hw := weights_ne_zero t ht hb
  exact lt_min (sq_pos_of_ne_zero (hw 0))
    (lt_min (sq_pos_of_ne_zero (hw 1)) (sq_pos_of_ne_zero (hw 2)))

theorem energySq_lower (t : ℝ) (p : Fin 3 → ℝ) :
    minSpeedSq t*(p 0^2+p 1^2+p 2^2) ≤ energySq t p := by
  have h0 : minSpeedSq t ≤ (weights t 0)^2 := min_le_left _ _
  have h1 : minSpeedSq t ≤ (weights t 1)^2 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : minSpeedSq t ≤ (weights t 2)^2 := (min_le_right _ _).trans (min_le_right _ _)
  have h := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_right h0 (sq_nonneg (p 0)))
      (mul_le_mul_of_nonneg_right h1 (sq_nonneg (p 1))))
    (mul_le_mul_of_nonneg_right h2 (sq_nonneg (p 2)))
  simpa only [energySq, mul_add, mul_pow] using h

theorem principal_isUnit (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10)
    (p : Fin 3 → ℝ) (hp : p ≠ 0) : IsUnit (principal t p) := by
  have he := ne_of_gt (energySq_pos t ht hb p hp)
  have hl : principal t p*((energySq t p)⁻¹ • principal t p)=1 := by
    rw [mul_smul_comm, principal_square, smul_smul, inv_mul_cancel₀ he, one_smul]
  have hr : ((energySq t p)⁻¹ • principal t p)*principal t p=1 := by
    rw [smul_mul_assoc, principal_square, smul_smul, inv_mul_cancel₀ he, one_smul]
  exact ⟨⟨principal t p, (energySq t p)⁻¹ • principal t p, hl, hr⟩, rfl⟩

theorem principal_kernel_iff (t : ℝ) (ht : t ≠ 0) (hb : |t|<Real.pi/10)
    (p : Fin 3 → ℝ) (hp : p ≠ 0) (u : Fin 4 → ℂ) :
    principal t p*ᵥu=0 ↔ u=0 := by
  constructor
  · intro h
    apply Matrix.mulVec_injective_iff_isUnit.mpr (principal_isUnit t ht hb p hp)
    simpa only [mulVec_zero] using h
  · rintro rfl
    exact mulVec_zero _

/-- The first vacuum direction loses its linear term at a tick inside the old
exact-exponential bandwidth interval. This is not a nonlinear extra-mode theorem. -/
theorem boundary_principal_zero : principal (Real.pi/10) ![1,0,0]=0 := by
  have hangle : 5*(Real.pi/10)=Real.pi/2 := by ring
  simp [principal, Dirac.H, weights, hangle]

theorem boundary_in_old_range : 0 < Real.pi/10 ∧ Real.pi/10 < 1/2 := by
  constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]

theorem boundary_compressed_deriv :
    HasDerivAt (fun s : ℝ => compress
      (VacuumSplit.momentumUpdate (fun j => s*(![1,0,0] : Fin 3 → ℝ) j) (Real.pi/10)))
      0 0 := by
  simpa only [boundary_principal_zero, smul_zero] using
    compressed_deriv (Real.pi/10) ![1,0,0]

theorem sin_cos_deriv_zero (a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin t*Real.cos (a*t)) 1 0 := by
  have hc := (Real.hasDerivAt_cos (a*(0 : ℝ))).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul a)
  have hd := (Real.hasDerivAt_sin 0).mul hc
  simpa [Function.comp_def, Pi.mul_def] using hd

/-- All three finite-tick velocities recover the same normalized infinitesimal limit. -/
theorem normalized_weight_limit (j : Fin 3) :
    Filter.Tendsto (fun t : ℝ => t⁻¹*weights t j) (𝓝[≠] 0) (𝓝 1) := by
  fin_cases j
  · simpa [weights, smul_eq_mul] using (sin_cos_deriv_zero 5).tendsto_slope_zero
  · simpa [weights, smul_eq_mul] using (sin_cos_deriv_zero 3).tendsto_slope_zero
  · simpa [weights, smul_eq_mul] using (sin_cos_deriv_zero 1).tendsto_slope_zero

end PMAction.VacuumPrincipal
