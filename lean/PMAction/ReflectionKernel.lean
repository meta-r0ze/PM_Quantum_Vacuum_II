import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-!
# The Osterwalder–Seiler kernel is positive definite

Reflection positivity of a Wilson-type lattice measure (`YANG-MILLS-STATUS.md` item 2) rests on
one kernel inequality: across a reflection plane, the action contributes a factor
`exp(β Re tr(Φ Ψᴴ))` with `Φ` a product of links on one side and `Ψ` the reflected product. The
needed fact is that this kernel is positive definite for `β ≥ 0`:

    Σ_{i,j} c_i c_j exp(β Re tr(U_i U_jᴴ)) ≥ 0   for all real c and matrices U_i.

* `gram_power_psd`: for vectors `x_i ∈ ℝ^d`, `Σ c_i c_j ⟨x_i, x_j⟩ⁿ ≥ 0` (induction, using
  `⟨x, y⟩ⁿ⁺¹ = Σ_k x_k y_k ⟨x, y⟩ⁿ`; no Schur product theorem needed).
* `gram_exp_psd`: hence `Σ c_i c_j exp(β ⟨x_i, x_j⟩) ≥ 0` for `β ≥ 0` (exponential series).
* `re_trace_eq_inner`: `Re tr(U Vᴴ)` is the real inner product of the real and imaginary parts of
  the entries.
* `wilson_kernel_psd`: so the kernel `exp(β Re tr(U Vᴴ))` is positive definite on all matrices.

Still open for PM's D₄ action: that every D₄ triangle crossing a reflection plane factors as
`tr(Φ Ψᴴ)` with `Φ`, `Ψ` on opposite sides (the geometric half of Osterwalder–Seiler), and the
resulting transfer matrix. That needs the D₄ lattice's reflection planes, which this file does not
treat.
-/

noncomputable section
namespace PMAction.ReflectionKernel
open Finset Matrix

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The real inner product on `ℝ^d`. -/
def ip (x y : Fin d → ℝ) : ℝ := ∑ k, x k * y k

/-- One step of the power expansion. -/
lemma power_step (x : ι → Fin d → ℝ) (n : ℕ) (c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * ip (x i) (x j) ^ (n + 1) =
      ∑ k, ∑ i, ∑ j, (c i * x i k) * (c j * x j k) * ip (x i) (x j) ^ n := by
  have h1 : ∀ i j, c i * c j * ip (x i) (x j) ^ (n + 1) =
      ∑ k, (c i * x i k) * (c j * x j k) * ip (x i) (x j) ^ n := by
    intro i j
    rw [pow_succ]
    set g := ip (x i) (x j) ^ n
    rw [show ip (x i) (x j) = ∑ k, x i k * x j k from rfl, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [h1]
  calc _ = ∑ i, ∑ k, ∑ j, (c i * x i k) * (c j * x j k) * ip (x i) (x j) ^ n :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- **Powers of a Gram kernel are positive semidefinite.** -/
theorem gram_power_psd (x : ι → Fin d → ℝ) (n : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * ip (x i) (x j) ^ n := by
  induction n generalizing c with
  | zero =>
    have : ∑ i, ∑ j, c i * c j * ip (x i) (x j) ^ 0 = (∑ i, c i) ^ 2 := by
      simp only [pow_zero, mul_one, sq, Finset.sum_mul_sum]
    rw [this]; positivity
  | succ n ih =>
    rw [power_step]
    exact Finset.sum_nonneg fun k _ => ih (fun i => c i * x i k)

/-- **The exponential of a Gram kernel is positive semidefinite.** -/
theorem gram_exp_psd (x : ι → Fin d → ℝ) (β : ℝ) (hβ : 0 ≤ β) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.exp (β * ip (x i) (x j)) := by
  have hs : ∀ i j, HasSum (fun n : ℕ => c i * c j * ((β * ip (x i) (x j)) ^ n / n.factorial))
      (c i * c j * Real.exp (β * ip (x i) (x j))) := by
    intro i j
    have := NormedSpace.expSeries_div_hasSum_exp (β * ip (x i) (x j))
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_left _
  have hsum : HasSum (fun n : ℕ => ∑ i, ∑ j, c i * c j * ((β * ip (x i) (x j)) ^ n / n.factorial))
      (∑ i, ∑ j, c i * c j * Real.exp (β * ip (x i) (x j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => hs i j
  refine hsum.nonneg fun n => ?_
  have e : ∑ i, ∑ j, c i * c j * ((β * ip (x i) (x j)) ^ n / n.factorial) =
      (β ^ n / n.factorial) * ∑ i, ∑ j, c i * c j * ip (x i) (x j) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  rw [e]
  exact mul_nonneg (by positivity) (gram_power_psd x n c)

variable {N : ℕ}

/-- Real coordinates of a complex matrix: real and imaginary parts of its entries. -/
def coords (U : Matrix (Fin N) (Fin N) ℂ) : Fin (N * N * 2) → ℝ := fun k =>
  let e := finProdFinEquiv.symm k
  let ab := finProdFinEquiv.symm e.1
  if e.2 = 0 then (U ab.1 ab.2).re else (U ab.1 ab.2).im

/-- **`Re tr(U Vᴴ)` is the real inner product of the coordinates.** -/
theorem re_trace_eq_inner (U V : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.trace (U * Vᴴ)).re = ip (coords U) (coords V) := by
  have lhs : (Matrix.trace (U * Vᴴ)).re =
      ∑ a : Fin N, ∑ b : Fin N, ((U a b).re * (V a b).re + (U a b).im * (V a b).im) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re]
  rw [lhs, ip]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [coords, Fin.sum_univ_two]

/-- **The Wilson reflection kernel is positive definite.** -/
theorem wilson_kernel_psd (U : ι → Matrix (Fin N) (Fin N) ℂ) (β : ℝ) (hβ : 0 ≤ β) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.exp (β * (Matrix.trace (U i * (U j)ᴴ)).re) := by
  simp only [re_trace_eq_inner]
  exact gram_exp_psd (fun i => coords (U i)) β hβ c

end PMAction.ReflectionKernel
