import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Coherent lifting of a finite injective state encoding

The sparse matrix of an injective label map is an isometry and preserves the
complete complex pairing. This is a representation theorem, with no physical
preparation, additional records, admissible gate or tariff inferred from it.
-/

noncomputable section
namespace PMAction.FiniteEncoding
open Matrix
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def matrix (f : a → b) : Matrix b a ℂ := fun i j => if i = f j then 1 else 0

omit [Fintype a] in
theorem isometry (f : a → b) (hf : Function.Injective f) :
    (matrix f)ᴴ * matrix f = 1 := by
  ext i j
  simp only [matrix, mul_apply, conjTranspose_apply, one_apply, apply_ite star,
    star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (f i)]
  · simp [hf.eq_iff]
  · intro h _ hh
    simp [hh]
  · simp

omit [Fintype b] in
theorem coordinate (f : a → b) (hf : Function.Injective f) (ψ : a → ℂ) (i : a) :
    (matrix f *ᵥ ψ) (f i) = ψ i := by
  simp [matrix, mulVec, dotProduct, hf.eq_iff]

theorem pairing (f : a → b) (hf : Function.Injective f) (ψ φ : a → ℂ) :
    star (matrix f *ᵥ ψ) ⬝ᵥ (matrix f *ᵥ φ) = star ψ ⬝ᵥ φ := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, isometry f hf, one_mulVec]

theorem recover (f : a → b) (hf : Function.Injective f) (ψ : a → ℂ) :
    (matrix f)ᴴ *ᵥ (matrix f *ᵥ ψ) = ψ := by
  rw [mulVec_mulVec, isometry f hf, one_mulVec]

/-- Relabeling commutes with a sparse encoding whenever it commutes on labels. -/
theorem intertwining (f : a → b) (e : Equiv.Perm a) (d : Equiv.Perm b)
    (h : ∀ x, d (f x) = f (e x)) :
    d.permMatrix ℂ * matrix f = matrix f * e.permMatrix ℂ := by
  ext i j
  change (d.permMatrix ℂ *ᵥ (fun y => matrix f y j)) i =
    ((fun x => matrix f i x) ᵥ* e.permMatrix ℂ) j
  rw [permMatrix_mulVec, vecMul_permMatrix]
  have hh : d i = f j ↔ i = f (e.symm j) := by
    constructor
    · intro hi
      apply d.injective
      simpa only [h, Equiv.apply_symm_apply] using hi
    · rintro rfl
      simpa using h (e.symm j)
  simp only [Function.comp_apply, matrix, hh]

/-- The reverse readout intertwiner holds on all ambient amplitudes. -/
theorem readout_intertwining (f : a → b) (e : Equiv.Perm a) (d : Equiv.Perm b)
    (h : ∀ x, d (f x) = f (e x)) :
    (matrix f)ᴴ * d.permMatrix ℂ = e.permMatrix ℂ * (matrix f)ᴴ := by
  have hi : ∀ x, d.symm (f x) = f (e.symm x) := by
    intro x
    apply d.injective
    simpa using (h (e.symm x)).symm
  have hh := congrArg Matrix.conjTranspose (intertwining f e.symm d.symm hi)
  simpa only [conjTranspose_mul, conjTranspose_permMatrix, Equiv.Perm.inv_def,
    Equiv.symm_symm] using hh

end PMAction.FiniteEncoding
