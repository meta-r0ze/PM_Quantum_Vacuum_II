import PMAction.CommonResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The scalar link cost at small angle: `‖φ − U_ε φ‖² = ε²‖θφ‖² + O(ε⁴)`

`CommonResponse` prices the scalar link by `‖φ' − Uφ‖²/4`. Paper III's `LinkMass` uses its leading
form `|θφ|²` for `U = exp(iθ)`. This module proves that expansion with an explicit remainder.

A Hermitian generator is given in an orthonormal eigenbasis: `θ = V diag(λ) V†` with `V` unitary
(the spectral theorem supplies such `V, λ`). The transport it generates is
`U_ε = V diag(e^{iελ}) V†`.

* `normSq_one_sub_exp`: `|1 − e^{ix}|² = 2 − 2cos x`.
* `diag_cost`, `diag_generator`: in eigen-coordinates `c`, the cost is `Σ|c_k|²(2 − 2cos ελ_k)` and
  `‖θc‖² = Σ|c_k|²λ_k²`.
* `diag_expansion`: if every `|ελ_k| ≤ 1`, then
  `|‖c − U_ε c‖² − ε²‖θc‖²| ≤ (5/48) ε⁴ Σ|c_k|²λ_k⁴`.
* `link_expansion`: the same bound for any `φ` and any unitary eigenbasis `V`, so the event-law
  link cost has leading term `ε²‖θφ‖²`, the quadratic form of `LinkMass`.
-/

noncomputable section
namespace PMAction.LinkExpansion
open Matrix Finset Complex CommonResponse
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem normSq_one_sub_exp (x : ℝ) :
    Complex.normSq (1 - Complex.exp (x * I)) = 2 - 2 * Real.cos x := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.one_im, Complex.add_im,
    Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Transport in eigen-coordinates. -/
def phaseVec (lam : n → ℝ) (ε : ℝ) (c : n → ℂ) : n → ℂ :=
  fun k => Complex.exp ((ε * lam k : ℝ) * I) * c k

def genVec (lam : n → ℝ) (c : n → ℂ) : n → ℂ := fun k => (lam k : ℂ) * c k

omit [DecidableEq n] in
lemma nsq_eq (x : n → ℂ) : nsq x = ∑ k, Complex.normSq (x k) := by
  unfold nsq
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

omit [DecidableEq n] in
theorem diag_cost (lam : n → ℝ) (ε : ℝ) (c : n → ℂ) :
    nsq (c - phaseVec lam ε c) = ∑ k, Complex.normSq (c k) * (2 - 2 * Real.cos (ε * lam k)) := by
  rw [nsq_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : (c - phaseVec lam ε c) k = (1 - Complex.exp ((ε * lam k : ℝ) * I)) * c k := by
    simp [phaseVec]; ring
  rw [this, Complex.normSq_mul, normSq_one_sub_exp, mul_comm]

omit [DecidableEq n] in
theorem diag_generator (lam : n → ℝ) (c : n → ℂ) :
    nsq (genVec lam c) = ∑ k, Complex.normSq (c k) * lam k ^ 2 := by
  rw [nsq_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [genVec, Complex.normSq_mul, Complex.normSq_ofReal]; ring

lemma cos_remainder {x : ℝ} (hx : |x| ≤ 1) : |(2 - 2 * Real.cos x) - x ^ 2| ≤ 5 / 48 * x ^ 4 := by
  have h := Real.cos_bound hx
  have h4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [h4] at h
  have : (2 - 2 * Real.cos x) - x ^ 2 = -2 * (Real.cos x - (1 - x ^ 2 / 2)) := by ring
  rw [this, abs_mul]
  norm_num
  linarith

omit [DecidableEq n] in
theorem diag_expansion (lam : n → ℝ) (ε : ℝ) (c : n → ℂ) (h : ∀ k, |ε * lam k| ≤ 1) :
    |nsq (c - phaseVec lam ε c) - ε ^ 2 * nsq (genVec lam c)| ≤
      5 / 48 * ε ^ 4 * ∑ k, Complex.normSq (c k) * lam k ^ 4 := by
  rw [diag_cost, diag_generator, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  have hr := cos_remainder (h k)
  have hn := Complex.normSq_nonneg (c k)
  have e1 : Complex.normSq (c k) * (2 - 2 * Real.cos (ε * lam k)) - ε ^ 2 * (Complex.normSq (c k) * lam k ^ 2)
      = Complex.normSq (c k) * ((2 - 2 * Real.cos (ε * lam k)) - (ε * lam k) ^ 2) := by ring
  rw [e1, abs_mul, abs_of_nonneg hn]
  calc Complex.normSq (c k) * |(2 - 2 * Real.cos (ε * lam k)) - (ε * lam k) ^ 2|
      ≤ Complex.normSq (c k) * (5 / 48 * (ε * lam k) ^ 4) := mul_le_mul_of_nonneg_left hr hn
    _ = 5 / 48 * ε ^ 4 * (Complex.normSq (c k) * lam k ^ 4) := by ring

/-- Diagonal matrices realizing the eigen-coordinate maps. -/
def phaseDiag (lam : n → ℝ) (ε : ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun k => Complex.exp ((ε * lam k : ℝ) * I)

def genDiag (lam : n → ℝ) : Matrix n n ℂ := Matrix.diagonal fun k => (lam k : ℂ)

lemma unitary_nsq' (V : Matrix n n ℂ) (hV : Vᴴ * V = 1) (x : n → ℂ) :
    nsq (V *ᵥ x) = nsq x := by
  unfold nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hV, one_mulVec]

/-- For any unitary eigenbasis `V`, transport `U_ε = V diag(e^{iελ}) V†` and generator
`θ = V diag(λ) V†`, the event-law link cost has leading term `ε²‖θφ‖²`. -/
theorem link_expansion (V : Matrix n n ℂ) (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1)
    (lam : n → ℝ) (ε : ℝ) (φ : n → ℂ) (h : ∀ k, |ε * lam k| ≤ 1) :
    |nsq (φ - (V * phaseDiag lam ε * Vᴴ) *ᵥ φ) - ε ^ 2 * nsq ((V * genDiag lam * Vᴴ) *ᵥ φ)| ≤
      5 / 48 * ε ^ 4 * ∑ k, Complex.normSq ((Vᴴ *ᵥ φ) k) * lam k ^ 4 := by
  set c := Vᴴ *ᵥ φ
  have hφ : φ = V *ᵥ c := by simp [c, mulVec_mulVec, hV2]
  have e1 : φ - (V * phaseDiag lam ε * Vᴴ) *ᵥ φ = V *ᵥ (c - phaseVec lam ε c) := by
    rw [mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec, ← hφ]
    congr 2
    ext k; simp [phaseDiag, phaseVec, mulVec_diagonal]; rfl
  have e2 : (V * genDiag lam * Vᴴ) *ᵥ φ = V *ᵥ genVec lam c := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    congr 1
    ext k; simp [genDiag, genVec, mulVec_diagonal]; left; rfl
  rw [e1, e2, unitary_nsq' V hV1, unitary_nsq' V hV1]
  exact diag_expansion lam ε c h

end PMAction.LinkExpansion
