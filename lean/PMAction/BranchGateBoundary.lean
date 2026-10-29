import PMAction.ComparisonFactorization

/-!
# Permutations and diagonal phases cannot synthesize the branch mixer

`BasisPreserving` allows a basis column to acquire a scalar and change its
location, but not split over two locations. It is closed under composition
and contains every permutation and diagonal matrix (even without unitarity).
The comparison mixer is not in this class on a nonempty carrier space.

Thus finite words in those gates, in the fixed branch/carrier basis, cannot
supply the mixer. This does not exclude coherent rotations, coherent ancilla
preparation, or a different physical encoding; their admissibility and costs
need their own construction. In particular a supplied arbitrary weak unitary
already goes beyond permutation and diagonal gates.
-/
noncomputable section
namespace PMAction.BranchGateBoundary
open Matrix ComparisonFactorization ControllerHamiltonian
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each input basis vector is mapped to a multiple of one basis vector. -/
def BasisPreserving (A : Matrix n n ℂ) : Prop :=
  ∀ j, ∃ i c, ∀ k, A k j = if k = i then c else 0

omit [Fintype n] in
theorem diagonal_preserves (d : n → ℂ) : BasisPreserving (diagonal d) := by
  intro j
  exact ⟨j, d j, fun k => by by_cases h : k = j <;> simp [h]⟩

omit [Fintype n] in
theorem permutation_preserves (e : Equiv.Perm n) :
    BasisPreserving (e.permMatrix ℂ) := by
  intro j
  refine ⟨e.symm j, 1, fun k => ?_⟩
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.eq_symm_apply]

theorem mul_preserves {A B : Matrix n n ℂ}
    (hA : BasisPreserving A) (hB : BasisPreserving B) : BasisPreserving (A * B) := by
  intro j
  obtain ⟨b, c, hb⟩ := hB j
  obtain ⟨a, d, ha⟩ := hA b
  refine ⟨a, d * c, fun k => ?_⟩
  simp [Matrix.mul_apply, hb, ha, mul_ite]

/-- Any finite gate word of this kind remains unable to split a basis input. -/
theorem word_preserves (gates : List (Matrix n n ℂ))
    (h : ∀ A ∈ gates, BasisPreserving A) : BasisPreserving gates.prod := by
  induction gates with
  | nil => simpa using (diagonal_preserves (fun _ : n => (1 : ℂ)))
  | cons A gates ih =>
    exact mul_preserves (h A (by simp)) (ih (fun B hb => h B (by simp [hb])))

omit [Fintype n] in
/-- Both branch outputs of one basis input are nonzero for the mixer. -/
theorem mixer_not_basis_preserving [Nonempty n] :
    ¬ BasisPreserving (had (n := n)) := by
  intro h
  let j : n := Classical.choice inferInstance
  obtain ⟨i, c, hi⟩ := h (.inl j)
  have hl : Sum.inl j = i := by
    by_contra he
    have hx := hi (.inl j)
    simp [had, branchChange, he] at hx
  have hr : Sum.inr j = i := by
    by_contra he
    have hx := hi (.inr j)
    simp [had, branchChange, he] at hx
  have hf : (Sum.inl j : n ⊕ n) = Sum.inr j := hl.trans hr.symm
  cases hf

theorem word_ne_mixer [Nonempty n] (gates : List (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (h : ∀ A ∈ gates, BasisPreserving A) : gates.prod ≠ had (n := n) := by
  intro he
  exact mixer_not_basis_preserving (he ▸ word_preserves gates h)

end PMAction.BranchGateBoundary
