import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# The charged-current vertex normalization

`ContactMatching` uses the vertex coupling `g/(2√2)`. This module derives that factor from the
doublet generators and a chiral projector.

* `charged_decomposition`: with `T₁, T₂` the doublet generators, `T± = T₁ ± iT₂` and
  `W± = (W₁ ∓ iW₂)/√2`, `g(W₁T₁ + W₂T₂) = (g/√2)(W⁺T₊ + W⁻T₋)`. The raising and lowering
  generators have unit entries (`raising_entries`), so each charged vertex carries `g/√2`.
* `projector_idempotent`: for any `Γ` with `Γ² = 1`, `P = (1 - Γ)/2` is a projector.
* `vertex_coefficient`: written with `(1 - Γ)`, the chiral charged vertex `(g/√2)P` is
  `(g/(2√2))(1 - Γ)`, the coefficient `ContactMatching.coeff` squares.

Identifying `Γ` with the chirality of the actual carriers (the left-handed sector of Paper II's
domain wall) is the physical input; the algebra here holds for any involution.
-/

noncomputable section
namespace PMAction.ChargedCurrent
open Matrix Complex

def T1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1/2; 1/2, 0]
def T2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I/2; I/2, 0]
def Tp : Matrix (Fin 2) (Fin 2) ℂ := T1 + I • T2
def Tm : Matrix (Fin 2) (Fin 2) ℂ := T1 - I • T2

theorem raising_entries : Tp = !![0, 1; 0, 0] ∧ Tm = !![0, 0; 1, 0] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Tp, Tm, T1, T2] <;> ring_nf <;> simp [I_sq] <;> norm_num

set_option linter.unnecessarySeqFocus false in
/-- **The charged decomposition.** -/
theorem charged_decomposition (g W1 W2 : ℂ) :
    g • (W1 • T1 + W2 • T2) =
      (g / Real.sqrt 2) • (((W1 - I * W2) / Real.sqrt 2) • Tp +
        ((W1 + I * W2) / Real.sqrt 2) • Tm) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tp, Tm, T1, T2] <;> field_simp <;> ring_nf <;>
    simp [hs] <;> ring

theorem projector_idempotent {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ)
    (h : Γ * Γ = 1) : ((1 / 2 : ℂ) • (1 - Γ)) * ((1 / 2 : ℂ) • (1 - Γ)) = (1 / 2 : ℂ) • (1 - Γ) := by
  rw [smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, h]
  simp only [one_mul, mul_one]
  rw [show (1 : Matrix n n ℂ) - Γ - (Γ - 1) = (2 : ℂ) • (1 - Γ) by
    rw [two_smul]; abel]
  rw [smul_smul]; norm_num

/-- **The vertex coefficient.** -/
theorem vertex_coefficient {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ) (g : ℂ) :
    (g / Real.sqrt 2) • ((1 / 2 : ℂ) • (1 - Γ)) = (g / (2 * Real.sqrt 2)) • (1 - Γ) := by
  rw [smul_smul]; congr 1; ring

end PMAction.ChargedCurrent
