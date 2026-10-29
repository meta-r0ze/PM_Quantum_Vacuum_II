import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# A two-slice domain wall: one chiral mode per D₄ sector

Take Paper I's two D₄ sectors as a two-site extra direction. On each sector the fermion has
the 4D Wilson-Dirac Hamiltonian; between sectors it hops with
`hop = −(i α₄ + r β)/2`, `hop† = −(−i α₄ + r β)/2`. At the Wilson point `M = r = 1` the
on-site mass vanishes at zero momentum and, with `Γ = i β α₄`,
`hop = −β(1 + Γ)/2`, `hop† = −β(1 − Γ)/2`.

* `zero_modes`: at zero momentum the two-slice Hamiltonian annihilates `(x₁, x₂)` exactly when
  `Γ x₁ = x₁` and `Γ x₂ = −x₂`. One sector carries the `Γ = +1` chirality, the other `Γ = −1`.
* `clifford_square`, `alpha_commutes_gamma`: the momentum term `Σ kⱼ αⱼ` squares to `|k|²` and
  preserves each chirality, so within either zero-mode space it disperses as `E = ±|k|`:
  speed one, isotropic.

Numerically (outside Lean), every twin at the momentum-cell corners is gapped by at least
`1.5`, and the modes stay localized on their sectors at small momentum. This is a
continuous-time Hamiltonian check; the discrete-time walk version is still to be built.
-/

namespace PMAction.DomainWall
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem zero_modes (β Γ : Matrix n n ℂ) (hβ : β * β = 1) (x₁ x₂ : n → ℂ) :
    ((-(1/2 : ℂ)) • (β * (1 + Γ)) *ᵥ x₂ = 0 ∧ (-(1/2 : ℂ)) • (β * (1 - Γ)) *ᵥ x₁ = 0) ↔
      (Γ *ᵥ x₁ = x₁ ∧ Γ *ᵥ x₂ = -x₂) := by
  have key : ∀ (A : Matrix n n ℂ) (y : n → ℂ),
      (-(1/2 : ℂ)) • (β * A) *ᵥ y = 0 ↔ A *ᵥ y = 0 := by
    intro A y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have h2 : β *ᵥ (A *ᵥ y) = 0 := by
        have := congrArg (fun z => (-2 : ℂ) • z) h
        simpa [smul_smul] using this
      have h3 := congrArg (fun z => β *ᵥ z) h2
      simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ] using h3
    · intro h; simp [h]
  rw [key, key]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · have := sub_eq_zero.mp h1; exact this.symm
    · exact eq_neg_of_add_eq_zero_right h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h2]; simp
    · rw [h1]; simp

/-- Anticommuting unit-square matrices: the momentum term squares to `|k|²`. -/
theorem clifford_square (α : Fin 3 → Matrix n n ℂ) (k : Fin 3 → ℂ)
    (hsq : ∀ j, α j * α j = 1) (hac : ∀ i j, i ≠ j → α i * α j = -(α j * α i)) :
    (∑ j, k j • α j) * (∑ j, k j • α j) = (∑ j, k j ^ 2) • (1 : Matrix n n ℂ) := by
  simp only [Fin.sum_univ_three, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hsq]
  rw [hac 1 0 (by decide), hac 2 0 (by decide), hac 2 1 (by decide)]
  simp only [smul_neg, add_smul]
  module

omit [DecidableEq n] in
/-- Each `αⱼ` anticommutes with `β` and `α₄`, hence commutes with `Γ = i β α₄`. -/
theorem alpha_commutes_gamma (a β α₄ : Matrix n n ℂ)
    (h1 : a * β = -(β * a)) (h2 : a * α₄ = -(α₄ * a)) :
    a * (Complex.I • (β * α₄)) = (Complex.I • (β * α₄)) * a := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, h1, Matrix.neg_mul,
    Matrix.mul_assoc, h2, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

/-- Discrete time. Paper II's reconstruction gives the update `e^{−iτH}`. An energy `E` maps to
the phase `e^{−iτE}`, which is one (a zero mode of the update) only for `E = 0`, provided
`|τE| < 2π`. With the domain-wall bandwidth below `2π/τ`, the update has exactly the
Hamiltonian's zero modes. -/
theorem update_zero_mode {τ E : ℝ} (hτ : τ ≠ 0) (hb : |τ * E| < 2 * Real.pi)
    (h : Complex.exp (-(τ * E : ℝ) * Complex.I) = 1) : E = 0 := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : -(τ * E) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this; linarith
  have hp := Real.pi_pos
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      exact_mod_cast this
    have : |τ * E| = |(n:ℝ)| * (2 * Real.pi) := by
      rw [← abs_neg, hre, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith
  rw [hn0] at hre; simp at hre
  rcases hre with h | h
  · exact absurd h hτ
  · exact h

end PMAction.DomainWall
