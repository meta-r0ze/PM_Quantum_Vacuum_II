import PMAction.DiscreteCausal

/-!
# The response law the substrate adjacency actually has

We do not choose a field equation. The substrate update links each site to its ±axis
neighbours (`Near (e j)`, the same stencil as the split update). This module builds the
**discrete Laplacian** on that actual adjacency and proves the two structural facts a
field equation must satisfy, from the substrate's symmetry and not from an ansatz:

* `lap_const` — a **uniform load produces no field**: the Laplacian annihilates constants.
* `lap_sum_zero` — the Laplacian is **source-neutral**: the sum of any source over the
  finite substrate is zero (the double sum is antisymmetric, because the adjacency is
  symmetric).
* `response_source_neutral` — consequently `lap K = source` forces `∑ source = 0`: a
  static source must be balanced, exactly the substrate's conservation law.

The load-to-clock readout (`WeakField`) then makes `g_00(x)` a functional of `K(x)`.
What is *not* derived: the source distribution itself (which maintenance/occupancy
imbalance drives it) and the continuum limit. Those remain model inputs.
-/

noncomputable section
set_option linter.unusedSectionVars false
namespace PMAction.ResponseLaw
open PMAction.SplitUpdate

variable {X : Type*} [Fintype X] [DecidableEq X]

attribute [local instance] Classical.propDecidable

/-- The substrate adjacency: a site and its ±axis neighbours under the three axis
permutations (the split-update stencil). -/
def Adj (e : Fin 3 → Equiv.Perm X) (x y : X) : Prop :=
  Near (e 0) x y ∨ Near (e 1) x y ∨ Near (e 2) x y

/-- Each one-axis neighbour relation is symmetric. -/
theorem near_symm (e : Equiv.Perm X) (x y : X) (h : Near e x y) : Near e y x := by
  rcases h with rfl | h | h
  · exact Or.inl rfl
  · rw [h]; exact Or.inr (Or.inr (by simp))
  · rw [h]; exact Or.inr (Or.inl (by simp))

theorem adj_symm (e : Fin 3 → Equiv.Perm X) (x y : X) : Adj e x y → Adj e y x := by
  rintro (h | h | h)
  · exact Or.inl (near_symm _ _ _ h)
  · exact Or.inr (Or.inl (near_symm _ _ _ h))
  · exact Or.inr (Or.inr (near_symm _ _ _ h))

/-- Edge weight of the adjacency. -/
def w (e : Fin 3 → Equiv.Perm X) (x y : X) : ℝ := if Adj e x y then 1 else 0

theorem w_symm (e : Fin 3 → Equiv.Perm X) (x y : X) : w e x y = w e y x := by
  unfold w
  by_cases h : Adj e x y
  · rw [ite_eq_left h, ite_eq_left (adj_symm e x y h)]
  · rw [ite_eq_right h]
    by_cases h' : Adj e y x
    · exact absurd (adj_symm e y x h') h
    · rw [ite_eq_right h']

/-- The discrete divergence integrand `w(x,y)·(f x − f y)`. -/
def summand (e : Fin 3 → Equiv.Perm X) (f : X → ℝ) (x y : X) : ℝ :=
  w e x y * (f x - f y)

theorem summand_antisymm (e : Fin 3 → Equiv.Perm X) (f : X → ℝ) (x y : X) :
    summand e f y x = -(summand e f x y) := by
  unfold summand
  rw [w_symm e x y]
  ring

/-- The discrete Laplacian on the substrate adjacency. -/
def lap (e : Fin 3 → Equiv.Perm X) (f : X → ℝ) (x : X) : ℝ :=
  ∑ y, summand e f x y

/-- **A uniform load produces no field.** -/
theorem lap_const (e : Fin 3 → Equiv.Perm X) (c : ℝ) (x : X) :
    lap e (fun _ => c) x = 0 := by
  simp [lap, summand]

/-- **The Laplacian is source-neutral.** The double sum is antisymmetric. -/
theorem lap_sum_zero (e : Fin 3 → Equiv.Perm X) (f : X → ℝ) :
    (∑ x, lap e f x) = 0 := by
  have hS : (∑ x, ∑ y, summand e f x y) = -(∑ x, ∑ y, summand e f x y) := by
    calc (∑ x, ∑ y, summand e f x y)
        = ∑ y, ∑ x, summand e f y x := rfl
      _ = ∑ y, ∑ x, -(summand e f x y) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            rw [summand_antisymm]
      _ = -(∑ y, ∑ x, summand e f x y) := by
            simp [Finset.sum_neg_distrib]
      _ = -(∑ x, ∑ y, summand e f x y) := by rw [Finset.sum_comm]
  simp only [lap]
  linarith

/-- **A static source must be balanced.** If `lap K = source` everywhere, the total
source over the finite substrate is zero — the substrate's conservation law. -/
theorem response_source_neutral (e : Fin 3 → Equiv.Perm X) (K s : X → ℝ)
    (h : ∀ x, lap e K x = s x) : (∑ x, s x) = 0 := by
  have : (∑ x, s x) = ∑ x, lap e K x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [h x]
  rw [this, lap_sum_zero e K]

end PMAction.ResponseLaw
