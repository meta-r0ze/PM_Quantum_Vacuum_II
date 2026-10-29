import PMAction.ControllerHamiltonian

/-!
# The comparison controller is a controlled operation between two branch mixers

`CoherentComparisonRepair.compare U` has half-amplitude blocks `(1 ± U)/2`, so it is not a
permutation (`root_comparison_not_permutation`). It factors into one controlled `U` between two
applications of a two-level branch mixer (the Hadamard test):

* `compare_factor`: `compare U = branchInverse · ctrl U · branchChange`, with
  `ctrl U = diag(1, U)` and `branchChange = [[1, 1], [1, -1]]` on the branch register.
* `compare_hadamard`: with the unitary mixer `had = branchChange/√2`, `compare U = had · ctrl U · had`.
* `had_unitary`, `ctrl_unitary`: both factors are unitary (the latter for unitary `U`).
* `ctrl_permutation`: if `U` is a permutation matrix (a root reflection on carriers), `ctrl U` is a
  permutation matrix of the two-branch space.

So the only non-permutation resource the controller needs is a single two-level mixer on the
branch register, applied twice. Its physical origin and price remain inputs; the carrier side is
the existing permutation, controlled by the branch.
-/

noncomputable section
namespace PMAction.ComparisonFactorization
open Matrix PMAction CoherentComparisonRepair ControllerHamiltonian
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The controlled operation: identity on the first branch, `U` on the second. -/
def ctrl (U : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 1 0 0 U

/-- **The Hadamard-test factorization.** -/
theorem compare_factor (U : Matrix n n ℂ) :
    CoherentComparisonRepair.compare U = branchInverse * ctrl U * branchChange := by
  simp only [branchInverse, branchChange, ctrl, CoherentComparisonRepair.compare, plus, minus,
    smul_mul_assoc, fromBlocks_multiply, fromBlocks_smul]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> module

/-- The unitary branch mixer. -/
def had : Matrix (n ⊕ n) (n ⊕ n) ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) • branchChange

theorem compare_hadamard (U : Matrix n n ℂ) :
    CoherentComparisonRepair.compare U = had * ctrl U * had := by
  rw [compare_factor, had, branchInverse]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  push_cast
  field_simp
  rw [hs]

theorem had_unitary : had (n := n) ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hstar : (had (n := n))ᴴ = had := by
    rw [had, conjTranspose_smul, branchChange, fromBlocks_conjTranspose]
    simp
  have hsq : had (n := n) * had = 1 := by
    have h := branch_inverse_left (n := n)
    rw [branchInverse, smul_mul_assoc] at h
    rw [had, smul_mul_assoc, mul_smul_comm, smul_smul]
    convert h using 2
    push_cast; field_simp; rw [hs]
  exact ⟨by rw [star_eq_conjTranspose, hstar, hsq], by rw [star_eq_conjTranspose, hstar, hsq]⟩

theorem ctrl_unitary (U : Matrix n n ℂ) (hu : U ∈ unitary _) :
    ctrl U ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have h1 : star U * U = 1 := hu.1
  have h2 : U * star U = 1 := hu.2
  constructor
  · rw [ctrl, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [mul_one, mul_zero, zero_mul, add_zero,
      zero_add, ← star_eq_conjTranspose, h1, fromBlocks_one, star_zero, star_one]
  · rw [ctrl, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [mul_one, mul_zero, zero_mul, add_zero,
      zero_add, ← star_eq_conjTranspose, h2, fromBlocks_one, star_zero, star_one]

omit [Fintype n] in
theorem ctrl_permutation (e : Equiv.Perm n) :
    ctrl (Equiv.Perm.permMatrix ℂ e) =
      Equiv.Perm.permMatrix ℂ (Equiv.Perm.sumCongr (Equiv.refl n) e) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [ctrl, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]

end PMAction.ComparisonFactorization
