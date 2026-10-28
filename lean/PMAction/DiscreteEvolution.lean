import PMAction.Reconstruction
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact persistent dynamics versus an Euler approximation

The displayed update in Paper II has, on a spatially constant scalar mass mode,
the forward-Euler factor `1 - i a`. It is lossless only for `a = 0`.
An exact completion is possible: rotate two internal channels and stream them
one site in opposite directions. Every rotation angle gives an exactly
norm-preserving, radius-one update. Persistence alone does not select its angle.
This is a finite periodic model, not a derived E8 quantum walk or continuum limit.
-/

noncomputable section
namespace PMAction.DiscreteEvolution

theorem euler_norm (a : ℝ) :
    Complex.normSq (1 - Complex.I * (a : ℂ)) = 1 + a ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

theorem euler_lossless_iff (a : ℝ) :
    Complex.normSq (1 - Complex.I * (a : ℂ)) = 1 ↔ a = 0 := by
  rw [euler_norm]
  constructor
  · intro h; nlinarith [sq_nonneg a]
  · rintro rfl; norm_num

/-- Real orthogonal mixing of two complex amplitudes. -/
def coin (θ : ℝ) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(Real.cos θ : ℂ) * v 0 - (Real.sin θ : ℂ) * v 1,
    (Real.sin θ : ℂ) * v 0 + (Real.cos θ : ℂ) * v 1]

theorem coin_lossless (θ : ℝ) (v : Fin 2 → ℂ) :
    Complex.normSq (coin θ v 0) + Complex.normSq (coin θ v 1) =
      Complex.normSq (v 0) + Complex.normSq (v 1) := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [coin, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) *
        ((v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2) := by ring
    _ = _ := by rw [h]; ring

abbrev State (N : ℕ) := Fin N → Fin 2 → ℂ

def population {N : ℕ} (ψ : State N) : ℝ :=
  ∑ x, (Complex.normSq (ψ x 0) + Complex.normSq (ψ x 1))

/-- Coin followed by counterpropagating streams on a finite ring. -/
def step {N : ℕ} (θ : ℝ) (ψ : State N) : State N := fun x =>
  ![coin θ (ψ ((finRotate N).symm x)) 0, coin θ (ψ (finRotate N x)) 1]

theorem step_lossless {N : ℕ} (θ : ℝ) (ψ : State N) :
    population (step θ ψ) = population ψ := by
  simp only [population, step, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.sum_add_distrib]
  rw [Equiv.sum_comp (finRotate N).symm (fun x => Complex.normSq (coin θ (ψ x) 0)),
    Equiv.sum_comp (finRotate N) (fun x => Complex.normSq (coin θ (ψ x) 1)),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => coin_lossless θ (ψ x))

/-- One tick reads only the two adjacent sites. -/
theorem step_local {N : ℕ} (θ : ℝ) (ψ φ : State N) (x : Fin N)
    (hl : ψ ((finRotate N).symm x) = φ ((finRotate N).symm x))
    (hr : ψ (finRotate N x) = φ (finRotate N x)) : step θ ψ x = step θ φ x := by
  simp only [step, hl, hr]

/-- Losslessness permits physically different internal updates. -/
theorem coin_not_unique :
    coin 0 ![1, 0] ≠ coin (Real.pi / 2) ![1, 0] := by
  intro h
  have := congrFun h 0
  simp [coin] at this

end PMAction.DiscreteEvolution
