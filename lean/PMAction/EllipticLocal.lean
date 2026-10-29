import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-! A uniform punctured-neighborhood invertibility theorem. A derivative whose
square has a coercive scalar bound controls the full nonlinear remainder. -/
noncomputable section
namespace PMAction.EllipticLocal
open Filter Topology
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A]

/-- Algebraic perturbation estimate used by both the pointwise and parametric theorems. -/
theorem isUnit_of_remainder (L : E →L[ℝ] A) (e : E → ℝ) (m : ℝ)
    (hm : 0<m) (hsquare : ∀ p, L p*L p=-(e p • (1 : A)))
    (hlower : ∀ p, m*‖p‖^2 ≤ e p) (p : E) (hp : p ≠ 0) (a : A)
    (hrem : ‖a-L p‖ ≤ (m/(‖L‖+1))*‖p‖) : IsUnit a := by
  let c : ℝ := m/(‖L‖+1)
  change ‖a-L p‖ ≤ c*‖p‖ at hrem
  have hbc : ‖L‖*c<m := by
    dsimp only [c]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < ‖L‖+1)]
    nlinarith
  have hq : 0<‖p‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
  have he : 0<e p := (mul_pos hm hq).trans_le (hlower p)
  let J : A := -((e p)⁻¹ • L p)
  have hleft : L p*J=1 := by
    dsimp only [J]
    rw [mul_neg, mul_smul_comm, hsquare p, smul_neg, neg_neg,
      smul_smul, inv_mul_cancel₀ (ne_of_gt he), one_smul]
  have hright : J*L p=1 := by
    dsimp only [J]
    rw [neg_mul, smul_mul_assoc, hsquare p, smul_neg, neg_neg,
      smul_smul, inv_mul_cancel₀ (ne_of_gt he), one_smul]
  have hnum : ‖L p‖*‖a-L p‖ < e p := by
    calc
      _ ≤ (‖L‖*‖p‖)*(c*‖p‖) :=
        mul_le_mul (L.le_opNorm p) hrem (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖L‖*c)*‖p‖^2 := by ring
      _ < m*‖p‖^2 := mul_lt_mul_of_pos_right hbc hq
      _ ≤ e p := hlower p
  have hJ : ‖J‖=(e p)⁻¹*‖L p‖ := by
    simp only [J, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos he]
  have hsmall : ‖J*(a-L p)‖<1 := by
    calc
      _ ≤ ‖J‖*‖a-L p‖ := norm_mul_le _ _
      _ = (e p)⁻¹*(‖L p‖*‖a-L p‖) := by rw [hJ, mul_assoc]
      _ < (e p)⁻¹*e p := mul_lt_mul_of_pos_left hnum (inv_pos.mpr he)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt he)
  have hunit : IsUnit (1+J*(a-L p)) := by
    have hh := IsUnit.one_sub_of_norm_lt_one
      (show ‖-(J*(a-L p))‖<1 by simpa only [norm_neg] using hsmall)
    simpa only [sub_neg_eq_add] using hh
  have hL : IsUnit (L p) := ⟨⟨L p, J, hleft, hright⟩, rfl⟩
  have hi : L p*(1+J*(a-L p))=a := by
    rw [mul_add, mul_one, ← mul_assoc, hleft, one_mul]
    abel
  rw [← hi]
  exact hL.mul hunit


theorem local_isUnit (f : E → A) (L : E →L[ℝ] A) (e : E → ℝ) (m : ℝ)
    (hm : 0<m) (hf0 : f 0=0) (hf : HasFDerivAt f L 0)
    (hsquare : ∀ p, L p*L p=-(e p • (1 : A)))
    (hlower : ∀ p, m*‖p‖^2 ≤ e p) :
    ∃ r : ℝ, 0<r ∧ ∀ p : E, p ≠ 0 → ‖p‖<r → IsUnit (f p) := by
  let c : ℝ := m/(‖L‖+1)
  have hc : 0<c := div_pos hm (by positivity)
  have hR := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf).bound hc
  simp only [zero_add, hf0, sub_zero] at hR
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hR
  refine ⟨r, hr, ?_⟩
  intro p hp hpr
  have hrem : ‖f p-L p‖ ≤ c*‖p‖ := hb (by simpa only [dist_zero_right] using hpr)
  exact isUnit_of_remainder L e m hm hsquare hlower p hp (f p) hrem

/-- Strict joint differentiability supplies one momentum ball for all small parameters. -/
theorem parameter_local_isUnit (f : ℝ × E → A) (L : (ℝ × E) →L[ℝ] A)
    (l : E →L[ℝ] A) (e : E → ℝ) (m : ℝ) (hm : 0<m)
    (hfzero : ∀ t : ℝ, f (t,0)=0) (hf : HasStrictFDerivAt f L (0 : ℝ × E))
    (hform : ∀ p, L (0,p)=l p)
    (hsquare : ∀ p, l p*l p=-(e p • (1 : A)))
    (hlower : ∀ p, m*‖p‖^2 ≤ e p) :
    ∃ r : ℝ, 0<r ∧ ∀ t : ℝ, |t|<r → ∀ p : E, p ≠ 0 → ‖p‖<r → IsUnit (f (t,p)) := by
  let c : ℝ := m/(‖l‖+1)
  have hc : 0<c := div_pos hm (by positivity)
  let paired : ℝ × E → (ℝ × E) × (ℝ × E) := fun z => (z,(z.1,0))
  have hcmap : Continuous paired := by fun_prop
  have he := (hcmap.tendsto (0 : ℝ × E)).eventually (hf.isLittleO.bound hc)
  have hlin (z : ℝ × E) : L z-L (z.1,0)=l z.2 := by
    rw [← map_sub]
    have hz : z-(z.1,0)=(0,z.2) := by ext <;> simp
    rw [hz, hform]
  have hrem : ∀ᶠ z : ℝ × E in 𝓝 0, ‖f z-l z.2‖ ≤ c*‖z.2‖ := by
    simpa [paired, Prod.norm_def, hfzero, hform, hlin] using! he
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨r, hr, ?_⟩
  intro t ht p hp hpr
  have hd : dist (t,p) (0 : ℝ × E)<r := by
    simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using max_lt ht hpr
  exact isUnit_of_remainder l e m hm hsquare hlower p hp (f (t,p)) (hb hd)

end PMAction.EllipticLocal
