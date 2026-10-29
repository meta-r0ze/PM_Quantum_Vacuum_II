import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! Explicit error bounds from bounded first and second derivatives. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.PathError
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem first_order_remainder (f d dd : ℝ → E) (C : ℝ)
    (hd : ∀ t, HasDerivAt f (d t) t) (hdd : ∀ t, HasDerivAt d (dd t) t)
    (hb : ∀ t, ‖dd t‖ ≤ C) (h : ℝ) :
    ‖f h - f 0 - h • d 0‖ ≤ C*h^2 := by
  have hC : 0 ≤ C := (norm_nonneg (dd 0)).trans (hb 0)
  have hl (t : ℝ) : ‖d t-d 0‖ ≤ C*|t| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ (univ : Set ℝ)) => (hdd x).differentiableAt)
      (fun x (_ : x ∈ (univ : Set ℝ)) => by rw [(hdd x).deriv]; exact hb x)
      convex_univ (mem_univ 0) (mem_univ t)
    simpa only [sub_zero, Real.norm_eq_abs] using hh
  let g (t : ℝ) := f t - f 0 - t • d 0
  have hg (t : ℝ) : HasDerivAt g (d t-d 0) t := by
    simpa only [g, one_smul, Pi.sub_def, id_eq] using
      ((hd t).sub_const (f 0)).sub ((hasDerivAt_id t).smul_const (d 0))
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc (-|h|) |h|) => (hg x).differentiableAt)
    (fun x (hx : x ∈ Icc (-|h|) |h|) => by
      rw [(hg x).deriv]
      exact (hl x).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hC))
    (convex_Icc (-|h|) |h|)
    (show (0 : ℝ) ∈ Icc (-|h|) |h| by constructor <;> linarith [abs_nonneg h])
    (show h ∈ Icc (-|h|) |h| from ⟨neg_abs_le h, le_abs_self h⟩)
  calc
    _ ≤ C * |h| * |h| := by simpa [g, Real.norm_eq_abs] using hh
    _ = C*h^2 := by rw [mul_assoc, ← pow_two, sq_abs]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A contraction path with a certified speed and squared-speed acceleration bound. -/
structure Path where
  value : ℝ → A
  velocity : ℝ → A
  acceleration : ℝ → A
  speed : ℝ
  speed_nonneg : 0 ≤ speed
  deriv_value : ∀ t, HasDerivAt value (velocity t) t
  deriv_velocity : ∀ t, HasDerivAt velocity (acceleration t) t
  norm_value : ∀ t, ‖value t‖ ≤ 1
  norm_velocity : ∀ t, ‖velocity t‖ ≤ speed
  norm_acceleration : ∀ t, ‖acceleration t‖ ≤ speed^2

namespace Path

def mul (p q : Path (A := A)) : Path (A := A) where
  value t := p.value t*q.value t
  velocity t := p.velocity t*q.value t+p.value t*q.velocity t
  acceleration t := (p.acceleration t*q.value t+p.velocity t*q.velocity t)+
    (p.velocity t*q.velocity t+p.value t*q.acceleration t)
  speed := p.speed+q.speed
  speed_nonneg := add_nonneg p.speed_nonneg q.speed_nonneg
  deriv_value t := (p.deriv_value t).mul (q.deriv_value t)
  deriv_velocity t := ((p.deriv_velocity t).mul (q.deriv_value t)).add
    ((p.deriv_value t).mul (q.deriv_velocity t))
  norm_value t := (norm_mul_le _ _).trans (by
    simpa using mul_le_mul (p.norm_value t) (q.norm_value t) (norm_nonneg _) (by norm_num))
  norm_velocity t := (norm_add_le _ _).trans (by
    have h1 := (norm_mul_le _ _).trans
      (mul_le_mul (p.norm_velocity t) (q.norm_value t) (norm_nonneg _) p.speed_nonneg)
    have h2 := (norm_mul_le _ _).trans
      (mul_le_mul (p.norm_value t) (q.norm_velocity t) (norm_nonneg _) (by norm_num))
    simpa using add_le_add h1 h2)
  norm_acceleration t := by
    have h1 := (norm_mul_le _ _).trans
      (mul_le_mul (p.norm_acceleration t) (q.norm_value t) (norm_nonneg _) (sq_nonneg _))
    have h2 := (norm_mul_le _ _).trans
      (mul_le_mul (p.norm_velocity t) (q.norm_velocity t) (norm_nonneg _) p.speed_nonneg)
    have h3 := (norm_mul_le _ _).trans
      (mul_le_mul (p.norm_value t) (q.norm_acceleration t) (norm_nonneg _) (by norm_num))
    calc
      _ ≤ (‖p.acceleration t*q.value t‖+‖p.velocity t*q.velocity t‖)+
        (‖p.velocity t*q.velocity t‖+‖p.value t*q.acceleration t‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ (p.speed^2*1+p.speed*q.speed)+(p.speed*q.speed+1*q.speed^2) := by
        exact add_le_add (add_le_add h1 h2) (add_le_add h2 h3)
      _ = (p.speed+q.speed)^2 := by ring

/-- A constant-generator contraction path has certified speed ‖G‖. -/
def ofGenerator (f : ℝ → A) (G : A)
    (hd : ∀ t, HasDerivAt f (f t*G) t) (hc : ∀ t, ‖f t‖ ≤ 1) : Path (A := A) where
  value := f
  velocity t := f t*G
  acceleration t := (f t*G)*G
  speed := ‖G‖
  speed_nonneg := norm_nonneg _
  deriv_value := hd
  deriv_velocity t := (hd t).mul_const G
  norm_value := hc
  norm_velocity t := (norm_mul_le _ _).trans (by simpa using (mul_le_mul_of_nonneg_right (hc t) (norm_nonneg G)))
  norm_acceleration t := by
    calc
      _ ≤ (‖f t‖*‖G‖)*‖G‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg G))
      _ ≤ (1*‖G‖)*‖G‖ := by gcongr; exact hc t
      _ = ‖G‖^2 := by ring

theorem remainder (p : Path (A := A)) (h : ℝ) :
    ‖p.value h-p.value 0-h • p.velocity 0‖ ≤ p.speed^2*h^2 :=
  first_order_remainder p.value p.velocity p.acceleration (p.speed^2)
    p.deriv_value p.deriv_velocity p.norm_acceleration h

end Path
end PMAction.PathError
