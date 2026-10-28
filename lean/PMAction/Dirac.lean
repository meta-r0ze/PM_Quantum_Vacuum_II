import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-!
# First-order local updates with relativistic dispersion are Clifford

A local first-order update on internal state space `A` (any real algebra, e.g. matrices) has
Hamiltonian `H(p, m) = Σₖ pₖ αₖ + m β`. Requiring the dispersion relation `H² = (|p|² + m²)·1`
for every momentum `p` and mass `m` (isotropy and the speed limit `c = 1`) is equivalent to the
Clifford relations: `αₖ² = β² = 1` and all distinct generators anticommute.
-/

namespace PMAction.Dirac

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The first-order Hamiltonian at momentum `p` and mass `m`. -/
def H (α : Fin 3 → A) (β : A) (p : Fin 3 → ℝ) (m : ℝ) : A :=
  p 0 • α 0 + p 1 • α 1 + p 2 • α 2 + m • β

/-- The Clifford relations. -/
def Clifford (α : Fin 3 → A) (β : A) : Prop :=
  (∀ k, α k * α k = 1) ∧ β * β = 1 ∧ (∀ j k, j ≠ k → α j * α k + α k * α j = 0) ∧
    (∀ k, α k * β + β * α k = 0)

lemma sq_expand (α : Fin 3 → A) (β : A) (p : Fin 3 → ℝ) (m : ℝ) :
    H α β p m * H α β p m =
      (p 0 * p 0) • (α 0 * α 0) + (p 1 * p 1) • (α 1 * α 1) + (p 2 * p 2) • (α 2 * α 2) +
      (m * m) • (β * β) +
      (p 0 * p 1) • (α 0 * α 1 + α 1 * α 0) + (p 0 * p 2) • (α 0 * α 2 + α 2 * α 0) +
      (p 1 * p 2) • (α 1 * α 2 + α 2 * α 1) +
      (p 0 * m) • (α 0 * β + β * α 0) + (p 1 * m) • (α 1 * β + β * α 1) +
      (p 2 * m) • (α 2 * β + β * α 2) := by
  simp only [H, add_mul, mul_add, smul_mul_smul_comm, smul_add]
  module

/-- **Dispersion ⇔ Clifford.** -/
theorem dispersion_iff_clifford (α : Fin 3 → A) (β : A) :
    (∀ (p : Fin 3 → ℝ) (m : ℝ), H α β p m * H α β p m = (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + m ^ 2) • (1 : A))
      ↔ Clifford α β := by
  constructor
  · intro h
    have e : ∀ (p : Fin 3 → ℝ) (m : ℝ), _ := fun p m => (sq_expand α β p m).symm.trans (h p m)
    have hk : ∀ k, α k * α k = 1 := by
      intro k; fin_cases k
      · simpa using e ![1, 0, 0] 0
      · simpa using e ![0, 1, 0] 0
      · simpa using e ![0, 0, 1] 0
    have hb : β * β = 1 := by simpa using e ![0, 0, 0] 1
    refine ⟨hk, hb, ?_, ?_⟩
    · have two : ∀ X : A, (1 : A) + 1 + X = ((1 : ℝ) + 1) • (1 : A) → X = 0 := by
        intro X hX
        rw [add_smul, one_smul] at hX
        simpa using hX
      have h01 : α 0 * α 1 + α 1 * α 0 = 0 := two _ (by simpa [hk 0, hk 1, hk 2] using e ![1, 1, 0] 0)
      have h02 : α 0 * α 2 + α 2 * α 0 = 0 := two _ (by simpa [hk 0, hk 1, hk 2] using e ![1, 0, 1] 0)
      have h12 : α 1 * α 2 + α 2 * α 1 = 0 := two _ (by simpa [hk 0, hk 1, hk 2] using e ![0, 1, 1] 0)
      have h10 : α 1 * α 0 + α 0 * α 1 = 0 := by rw [add_comm]; exact h01
      have h20 : α 2 * α 0 + α 0 * α 2 = 0 := by rw [add_comm]; exact h02
      have h21 : α 2 * α 1 + α 1 * α 2 = 0 := by rw [add_comm]; exact h12
      intro j k hjk
      fin_cases j <;> fin_cases k <;> simp at hjk ⊢ <;> assumption
    · have two : ∀ X : A, (1 : A) + 1 + X = ((1 : ℝ) + 1) • (1 : A) → X = 0 := by
        intro X hX
        rw [add_smul, one_smul] at hX
        simpa using hX
      intro k
      fin_cases k
      · exact two _ (by simpa [hk 0, hb] using e ![1, 0, 0] 1)
      · exact two _ (by simpa [hk 1, hb] using e ![0, 1, 0] 1)
      · exact two _ (by simpa [hk 2, hb] using e ![0, 0, 1] 1)
  · rintro ⟨hk, hb, hjk, hkb⟩ p m
    rw [sq_expand, hk, hk, hk, hb, hjk 0 1 (by decide), hjk 0 2 (by decide), hjk 1 2 (by decide),
      hkb, hkb, hkb]
    simp only [smul_zero, add_zero]
    module

end PMAction.Dirac
