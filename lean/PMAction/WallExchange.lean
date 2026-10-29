import PMAction.ConcreteFermion
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The wall exchange that is a symmetry: swap the walls with parity

`WallChiralCurrent.plain_wall_exchange_fails` shows that swapping the two D₄ walls alone is not a
symmetry of the domain-wall Hamiltonian: the walls carry opposite chirality. This module finds the
exchange that is a symmetry and derives what it implies for an inter-wall flavour link.

Take the two-wall Hamiltonian with a flavour index `f` and an inter-wall flavour matrix `Y`:

  `H_Y(k) = [[ (K(k) + δβ) ⊗ 1,  hop ⊗ Y ], [ back ⊗ Yᴴ,  (K(k) + δβ) ⊗ 1 ]]`,

with `K(k) = Σ kⱼ αⱼ`, `hop = −β(1+Γ)/2`, `back = −β(1−Γ)/2` (`DomainWallSpectrum`). Let
`P = [[0, β ⊗ 1], [β ⊗ 1, 0]]`: exchange the walls and apply the spinor parity `β`.

* `beta_alpha`, `beta_hop`, `beta_back`: `β αⱼ β = −αⱼ`, `β back β = hop`, `β hop β = back`.
  Parity flips momentum and exchanges the two chiral hops.
* `exchange_involution`: `P² = 1` (and `P` is Hermitian, so unitary).
* `exchange_conjugates`: `P H_Y(k) P = H_{Yᴴ}(−k)`. The exchange maps the link `Y` to `Yᴴ` and
  reverses momentum.
* `exchange_symmetry_iff`: `P H_Y(k) P = H_Y(−k)` exactly when `Yᴴ = Y`.

So the sector exchange that respects the walls' chirality is parity combined with the swap. If the
update is invariant under it (the two D₄ sectors are copies of one lattice), every inter-wall flavour
link is Hermitian. That is the premise of Paper III's `HermitianMass.thetaBar_eq_theta`, now reduced
to invariance under a concrete symmetry of the actual Hamiltonian. Still an input: that the vacuum
update has this symmetry, and that the zero-mode mass matrix is this link `Y`.
-/

noncomputable section
namespace PMAction.WallExchange
open Matrix ConcreteFermion
open scoped Kronecker

/-- `−β(1+Γ)/2`, written out. -/
def hop : Spin := !![0,0,0,0; 0,0,0,0; -1,0,0,0; 0,-1,0,0]
/-- `−β(1−Γ)/2`, written out. -/
def back : Spin := !![0,0,-1,0; 0,0,0,-1; 0,0,0,0; 0,0,0,0]

lemma plus_mat : (1/2 : ℂ) • (1 + gamma) = !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gamma, one_apply] <;> norm_num

lemma minus_mat : (1/2 : ℂ) • (1 - gamma) = !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gamma, one_apply] <;> norm_num

theorem hop_eq : hop = -(beta * ((1/2 : ℂ) • (1 + gamma))) := by
  rw [plus_mat]
  ext a b; fin_cases a <;> fin_cases b <;> simp [hop, beta]

theorem back_eq : back = -(beta * ((1/2 : ℂ) • (1 - gamma))) := by
  rw [minus_mat]
  ext a b; fin_cases a <;> fin_cases b <;> simp [back, beta]

/-- Momentum term. -/
def K (k : Fin 3 → ℝ) : Spin := ∑ j, (k j : ℂ) • alpha j

theorem beta_alpha (j : Fin 3) : beta * alpha j * beta = -alpha j := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [beta, alpha, mul_apply, Fin.sum_univ_four]

theorem beta_beta : beta * beta * beta = beta := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [beta, mul_apply, Fin.sum_univ_four]

theorem beta_hop : beta * back * beta = hop := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [beta, hop, back, mul_apply, Fin.sum_univ_four]

theorem beta_back : beta * hop * beta = back := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [beta, hop, back, mul_apply, Fin.sum_univ_four]

theorem beta_K (k : Fin 3 → ℝ) : beta * K k * beta = K (-k) := by
  simp only [K, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, beta_alpha,
    Pi.neg_apply, Complex.ofReal_neg, neg_smul, smul_neg]

variable {f : Type*} [Fintype f] [DecidableEq f]

/-- Diagonal block. -/
def diag (k : Fin 3 → ℝ) (δ : ℝ) : Spin := K k + (δ : ℂ) • beta

/-- Two walls with an inter-wall flavour link `Y`. -/
def H (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    Matrix ((Fin 4 × f) ⊕ (Fin 4 × f)) ((Fin 4 × f) ⊕ (Fin 4 × f)) ℂ :=
  fromBlocks (diag k δ ⊗ₖ (1 : Matrix f f ℂ)) (hop ⊗ₖ Y) (back ⊗ₖ Yᴴ) (diag k δ ⊗ₖ (1 : Matrix f f ℂ))

/-- Wall exchange with spinor parity. -/
def P : Matrix ((Fin 4 × f) ⊕ (Fin 4 × f)) ((Fin 4 × f) ⊕ (Fin 4 × f)) ℂ :=
  fromBlocks 0 (beta ⊗ₖ (1 : Matrix f f ℂ)) (beta ⊗ₖ (1 : Matrix f f ℂ)) 0

theorem exchange_involution : (P : Matrix ((Fin 4 × f) ⊕ (Fin 4 × f)) _ ℂ) * P = 1 := by
  rw [P, fromBlocks_multiply]
  simp [← mul_kronecker_mul, beta_square, fromBlocks_one]

omit [Fintype f] in
theorem exchange_hermitian : (P : Matrix ((Fin 4 × f) ⊕ (Fin 4 × f)) _ ℂ)ᴴ = P := by
  have hb : betaᴴ = beta := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [beta]
  rw [P, fromBlocks_conjTranspose]
  simp [conjTranspose_kronecker, hb]

lemma beta_diag (k : Fin 3 → ℝ) (δ : ℝ) : beta * diag k δ * beta = diag (-k) δ := by
  simp only [diag, mul_add, add_mul, beta_K, mul_smul_comm, smul_mul_assoc, beta_beta]

lemma sandwich (A : Spin) (B : Matrix f f ℂ) :
    (beta ⊗ₖ (1 : Matrix f f ℂ)) * (A ⊗ₖ B) * (beta ⊗ₖ (1 : Matrix f f ℂ)) = (beta * A * beta) ⊗ₖ B := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp

/-- **The exchange maps `Y` to `Yᴴ` and `k` to `−k`.** -/
theorem exchange_conjugates (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    P * H k δ Y * P = H (-k) δ Yᴴ := by
  rw [P, H, fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  simp only [sandwich]
  rw [beta_diag, beta_hop, beta_back, H, conjTranspose_conjTranspose]

/-- **The exchange is a symmetry exactly when the flavour link is Hermitian.** -/
theorem exchange_symmetry_iff (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    P * H k δ Y * P = H (-k) δ Y ↔ Yᴴ = Y := by
  rw [exchange_conjugates]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (.inl (2, i))) (.inr (0, j))
    simpa [H, hop, kronecker_apply] using this
  · intro h; rw [h]

end PMAction.WallExchange

