import PMAction.WallExchange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Light chiral masses on the two-wall Hamiltonian: a seesaw `δ² Y⁻¹`

At zero momentum the two-wall Hamiltonian of `WallExchange` with inter-wall flavour link `Y` and
on-site mass `δβ` acts on four chirality/wall components, each a flavour vector (and a spectator
spin doublet, on which every operator is the identity: `hop_reduced`, `back_reduced`,
`beta_reduced`):

* `a` = wall 1, `Γ = +1`; `b` = wall 1, `Γ = −1`; `c` = wall 2, `Γ = +1`; `d` = wall 2, `Γ = −1`.

`δβ` couples `a ↔ b` and `c ↔ d` with `δ`; the inter-wall hops couple `b ↔ c` with `−Y` and
`−Yᴴ`. At `δ = 0`, `a` and `d` are the chiral zero modes (`DomainWall.zero_modes`) and `(b, c)`
is gapped by `Y`.

* `gapped_inverse`: for invertible `Y`, the gapped block `G = [[0, −Y], [−Yᴴ, 0]]` has inverse
  `[[0, −(Yᴴ)⁻¹], [−Y⁻¹, 0]]`.
* `effective_mass`: the zero-energy Schur complement onto the zero modes, `−V G⁻¹ Vᴴ`, is
  `[[0, δ² (Yᴴ)⁻¹], [δ² Y⁻¹, 0]]`. The light chiral modes acquire the Dirac mass `M = δ² Y⁻¹`
  coupling wall 1's right-handed mode to wall 2's left-handed mode.
* `seesaw`: `M Mᴴ = δ⁴ (Yᴴ Y)⁻¹`: the light masses are `δ²/σᵢ(Y)`, inversely proportional to the
  link's singular values. A stronger link gives a lighter chiral fermion.
* `light_hermitian`, `light_posDef`: if `Y` is Hermitian (the wall-parity symmetry,
  `exchange_symmetry_iff`) and positive definite, so is `M`.
* `light_det`: `det M = δ^{2n} / det Y`, so `arg det M = −arg det Y` up to the branch cut.

**Exact one-flavour spectrum** (`one_flavour_identity`, `one_flavour_eigen`). For a single
flavour with real link `y`, the four-component Hamiltonian satisfies
`H⁴ − (y² + 2δ²) H² + δ⁴ = 0`. Every energy `E` therefore has `E⁴ − (y² + 2δ²)E² + δ⁴ = 0`: a light
mode and a heavy partner with `m_light · m_heavy = δ²` and `m_light² + m_heavy² = y² + 2δ²`
exactly (`light_heavy`).

The Schur complement at zero energy is the leading-order effective mass for `δ ≪ σᵢ(Y)`; the
energy-dependent corrections are `O(δ²/σ²)` relative. That the physical fermion masses are these
light modes is the identification the formula proposes.
-/

noncomputable section
namespace PMAction.WallSeesaw
open Matrix ConcreteFermion
open scoped ComplexOrder

/-- Chirality-sector forms of `β`, `hop`, `back` (index `0` is `Γ = +1`, `1` is `Γ = −1`). -/
def betaC : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def hopC : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; -1, 0]
def backC : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 0, 0]

/-- Spinor index `2χ + s`: chirality `χ`, spectator spin `s`. -/
def ix (χ s : Fin 2) : Fin 4 := ⟨2 * χ.val + s.val, by omega⟩

theorem beta_reduced (χ s χ' s' : Fin 2) :
    beta (ix χ s) (ix χ' s') = if s = s' then betaC χ χ' else 0 := by
  fin_cases χ <;> fin_cases s <;> fin_cases χ' <;> fin_cases s' <;> simp [beta, betaC, ix]

theorem hop_reduced (χ s χ' s' : Fin 2) :
    WallExchange.hop (ix χ s) (ix χ' s') = if s = s' then hopC χ χ' else 0 := by
  fin_cases χ <;> fin_cases s <;> fin_cases χ' <;> fin_cases s' <;>
    simp [WallExchange.hop, hopC, ix]

theorem back_reduced (χ s χ' s' : Fin 2) :
    WallExchange.back (ix χ s) (ix χ' s') = if s = s' then backC χ χ' else 0 := by
  fin_cases χ <;> fin_cases s <;> fin_cases χ' <;> fin_cases s' <;>
    simp [WallExchange.back, backC, ix]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Gapped block on `(b, c)`. -/
def G (Y : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 (-Y) (-Yᴴ) 0

/-- Zero-mode/gapped coupling: rows `(a, d)`, columns `(b, c)`. -/
def V (δ : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks ((δ : ℂ) • 1) 0 0 ((δ : ℂ) • 1)

def Ginv (Y : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 (-(Yᴴ)⁻¹) (-Y⁻¹) 0

theorem gapped_inverse (Y : Matrix n n ℂ) (hY : IsUnit Y.det) :
    G Y * Ginv Y = 1 ∧ Ginv Y * G Y = 1 := by
  have hYh : IsUnit Yᴴ.det := by rw [det_conjTranspose]; exact hY.star
  constructor
  · rw [G, Ginv, fromBlocks_multiply]
    simp [mul_nonsing_inv _ hY, mul_nonsing_inv _ hYh, fromBlocks_one]
  · rw [G, Ginv, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hY, nonsing_inv_mul _ hYh, fromBlocks_one]

/-- The light Dirac mass `δ² Y⁻¹`. -/
def light (δ : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ := (δ ^ 2 : ℝ) • Y⁻¹

/-- **The light Dirac mass from the zero-energy Schur complement.** -/
theorem effective_mass (Y : Matrix n n ℂ) (δ : ℝ) :
    -(V δ * Ginv Y * (V δ)ᴴ) = fromBlocks 0 (light δ Yᴴ) (light δ Y) (0 : Matrix n n ℂ) := by
  rw [V, Ginv, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, light, light]
  simp [smul_smul, pow_two, fromBlocks_neg]

/-- **Seesaw: `M Mᴴ = δ⁴ (Yᴴ Y)⁻¹`.** -/
theorem seesaw (Y : Matrix n n ℂ) (δ : ℝ) :
    light δ Y * (light δ Y)ᴴ = (δ ^ 4 : ℝ) • (Yᴴ * Y)⁻¹ := by
  rw [light, conjTranspose_smul, smul_mul_smul_comm, conjTranspose_nonsing_inv,
    Matrix.mul_inv_rev]
  congr 1
  simp; ring

/-- **A Hermitian link gives a Hermitian light mass.** -/
theorem light_hermitian (Y : Matrix n n ℂ) (hH : Y.IsHermitian) (δ : ℝ) :
    (light δ Y).IsHermitian := by
  unfold IsHermitian light
  rw [conjTranspose_smul, conjTranspose_nonsing_inv, hH.eq]
  simp

/-- **A positive link gives a positive light mass.** -/
theorem light_posDef (Y : Matrix n n ℂ) (hP : Y.PosDef) (δ : ℝ) (hδ : δ ≠ 0) :
    (light δ Y).PosDef :=
  hP.inv.smul (by positivity)

/-- **`det M = δ^{2n} / det Y`.** -/
theorem light_det (Y : Matrix n n ℂ) (δ : ℝ) :
    (light δ Y).det = ((δ ^ 2 : ℝ) : ℂ) ^ Fintype.card n * (Y.det)⁻¹ := by
  rw [light, ← Complex.coe_smul, det_smul, det_nonsing_inv, Ring.inverse_eq_inv']

/-- One flavour, components `(a, b, c, d)`, real link `y`. -/
def H1 (δ y : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, (δ : ℂ), 0, 0; (δ : ℂ), 0, -(y : ℂ), 0; 0, -(y : ℂ), 0, (δ : ℂ); 0, 0, (δ : ℂ), 0]

/-- **`H⁴ − (y² + 2δ²) H² + δ⁴ = 0`.** -/
theorem one_flavour_identity (δ y : ℝ) :
    H1 δ y ^ 4 - (((y ^ 2 + 2 * δ ^ 2 : ℝ) : ℂ)) • H1 δ y ^ 2 + (((δ ^ 4 : ℝ)) : ℂ) • 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H1, pow_succ, one_apply] <;> ring

/-- Every eigenvalue satisfies the quartic. -/
theorem one_flavour_eigen (δ y : ℝ) (E : ℂ) (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (h : H1 δ y *ᵥ v = E • v) :
    E ^ 4 - ((y ^ 2 + 2 * δ ^ 2 : ℝ) : ℂ) * E ^ 2 + ((δ ^ 4 : ℝ) : ℂ) = 0 := by
  have hp : ∀ k : ℕ, (H1 δ y ^ k) *ᵥ v = E ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hz := congrArg (fun M => M *ᵥ v) (one_flavour_identity δ y)
  simp only [sub_mulVec, add_mulVec, smul_mulVec, hp, one_mulVec, zero_mulVec] at hz
  have : (E ^ 4 - ((y ^ 2 + 2 * δ ^ 2 : ℝ) : ℂ) * E ^ 2 + ((δ ^ 4 : ℝ) : ℂ)) • v = 0 := by
    rw [← hz]; simp only [sub_smul, add_smul, smul_smul]
  rcases smul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd h0 hv

/-- **Light mode and heavy partner.** If `m_l² ≠ m_h²` are the two roots in `E²`, then
`m_l² m_h² = δ⁴` and `m_l² + m_h² = y² + 2δ²`. -/
theorem light_heavy (δ y xl xh : ℝ) (hne : xl ≠ xh)
    (hl : xl ^ 2 - (y ^ 2 + 2 * δ ^ 2) * xl + δ ^ 4 = 0)
    (hh : xh ^ 2 - (y ^ 2 + 2 * δ ^ 2) * xh + δ ^ 4 = 0) :
    xl * xh = δ ^ 4 ∧ xl + xh = y ^ 2 + 2 * δ ^ 2 := by
  have hs : xl + xh = y ^ 2 + 2 * δ ^ 2 := by
    have : (xl - xh) * (xl + xh - (y ^ 2 + 2 * δ ^ 2)) = 0 := by linear_combination hl - hh
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  refine ⟨?_, hs⟩
  have : xl ^ 2 - (xl + xh) * xl + δ ^ 4 = 0 := by rw [hs]; exact hl
  nlinarith [this]

end PMAction.WallSeesaw
