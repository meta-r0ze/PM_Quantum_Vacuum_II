import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Species doubling of the Paper II quantum-walk update

`DiscreteEvolution.step` applies a real rotation (angle `θ`) to two channels and streams
channel 0 one site right and channel 1 one site left. On the infinite chain a plane wave
`ψ_x = e^{ikx} u` is mapped to `e^{ikx} W(k) u` with symbol `W(k) = S(k) C(θ)`.

* `symbol_trace`, `symbol_det`: `tr W = 2 cos θ cos k`, `det W = 1`, so the quasi-energies obey
  `cos ω = cos θ cos k`.
* `symbol_shift`: `W(k + π) = −W(k)`. Every mode `(k, ω)` has a twin `(k + π, ω + π)` with the
  same dispersion. Near the massless point the update carries two low-energy species.
* `plane_wave`: the chain update acts on plane waves exactly by the symbol.
-/

noncomputable section
namespace PMAction.Doubling
open Matrix Complex

def C (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

def S (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp (-(k : ℂ) * I), 0; 0, exp ((k : ℂ) * I)]

def W (θ k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := S k * C θ

theorem symbol_trace (θ k : ℝ) : (W θ k).trace = 2 * Real.cos θ * Real.cos k := by
  simp only [W, S, C, trace_fin_two, mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, head_cons, empty_val', cons_val_fin_one, head_fin_const]
  simp only [zero_mul, add_zero, zero_add]
  rw [show exp (-(k:ℂ) * I) * (Real.cos θ : ℂ) + exp ((k:ℂ) * I) * (Real.cos θ : ℂ) =
    (Real.cos θ : ℂ) * (exp ((k:ℂ) * I) + exp (-(k:ℂ) * I)) by ring]
  rw [show exp ((k:ℂ) * I) + exp (-(k:ℂ) * I) = 2 * Complex.cos k by
    rw [Complex.cos]; ring_nf]
  push_cast; ring

theorem symbol_det (θ k : ℝ) : (W θ k).det = 1 := by
  rw [W, det_mul]
  have h1 : (S k).det = 1 := by
    simp [S, det_fin_two, ← Complex.exp_add]
  have h2 : (C θ).det = 1 := by
    simp only [C, det_fin_two_of]
    have := Real.sin_sq_add_cos_sq θ
    have : ((Real.cos θ : ℂ)) * (Real.cos θ : ℂ) - -(Real.sin θ : ℂ) * (Real.sin θ : ℂ) =
      ((Real.sin θ ^ 2 + Real.cos θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Real.sin_sq_add_cos_sq]; simp
  rw [h1, h2, one_mul]

theorem symbol_shift (θ k : ℝ) : W θ (k + Real.pi) = -W θ k := by
  have he : ∀ z : ℂ, exp (z + Real.pi * I) = - exp z := by
    intro z; rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hS : S (k + Real.pi) = -S k := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [S]
    · rw [show (-(Real.pi:ℂ) + -(k:ℂ)) * I = -((k:ℂ) * I) + -((Real.pi:ℂ) * I) by ring,
        Complex.exp_add, Complex.exp_neg ((Real.pi:ℂ) * I), Complex.exp_pi_mul_I]; ring
    · rw [show ((k:ℂ) + Real.pi) * I = (k:ℂ) * I + Real.pi * I by ring, he]
  rw [W, W, hS, neg_mul]

/-- The same local rule on the infinite chain. -/
def chainStep (θ : ℝ) (ψ : ℤ → Fin 2 → ℂ) : ℤ → Fin 2 → ℂ := fun x =>
  ![(C θ *ᵥ ψ (x - 1)) 0, (C θ *ᵥ ψ (x + 1)) 1]

def plane (k : ℝ) (u : Fin 2 → ℂ) : ℤ → Fin 2 → ℂ := fun x => exp ((k : ℂ) * x * I) • u

theorem plane_wave (θ k : ℝ) (u : Fin 2 → ℂ) :
    chainStep θ (plane k u) = plane k (W θ k *ᵥ u) := by
  funext x i
  fin_cases i
  · simp only [chainStep, plane, W, S, C, mulVec, dotProduct, Fin.sum_univ_two, mul_apply,
      Pi.smul_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
      empty_val', cons_val_fin_one, head_fin_const, Matrix.cons_val_zero]
    push_cast
    rw [show (k:ℂ) * ((x:ℂ) - 1) * I = (k:ℂ) * x * I + -(k:ℂ) * I by ring, Complex.exp_add]
    ring
  · simp only [chainStep, plane, W, S, C, mulVec, dotProduct, Fin.sum_univ_two, mul_apply,
      Pi.smul_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
      empty_val', cons_val_fin_one, head_fin_const, Matrix.cons_val_one]
    push_cast
    rw [show (k:ℂ) * ((x:ℂ) + 1) * I = (k:ℂ) * x * I + (k:ℂ) * I by ring, Complex.exp_add]
    ring

end PMAction.Doubling
