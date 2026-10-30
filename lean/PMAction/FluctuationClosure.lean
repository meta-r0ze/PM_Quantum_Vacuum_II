import PMAction.FluctuationPremises
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
namespace PMAction.FluctuationClosure
open Matrix
open scoped Pointwise

/-! ## 1. The Faddeev–Popov power as a determinant identity -/

section FP
variable {κ μ : Type*} [Fintype κ] [Fintype μ] [DecidableEq κ] [DecidableEq μ]

/-- The frame `S = [D | Q]`: gauge directions `D`, and a basis `Q` of their orthogonal
complement. -/
def frame (D : Matrix (κ ⊕ μ) κ ℝ) (Q : Matrix (κ ⊕ μ) μ ℝ) : Matrix (κ ⊕ μ) (κ ⊕ μ) ℝ :=
  Matrix.of fun i j => Sum.elim (D i) (Q i) j

omit [DecidableEq κ] [DecidableEq μ] in
theorem frame_conj (D : Matrix (κ ⊕ μ) κ ℝ) (Q : Matrix (κ ⊕ μ) μ ℝ)
    (M : Matrix (κ ⊕ μ) (κ ⊕ μ) ℝ) :
    (frame D Q)ᵀ * M * frame D Q = fromBlocks (Dᵀ * M * D) (Dᵀ * M * Q) (Qᵀ * M * D) (Qᵀ * M * Q) := by
  ext (a | a) (b | b) <;> simp [frame, Matrix.mul_apply, fromBlocks]

/-- **Orbit Jacobian.** `(det S)² = det(DᵀD)`: the change of variables
`(ω, a⊥) ↦ Dω + Qa⊥` has Jacobian `√det G`, with `G = DᵀD` the ghost operator. -/
theorem frame_det_sq (D : Matrix (κ ⊕ μ) κ ℝ) (Q : Matrix (κ ⊕ μ) μ ℝ) (hQD : Qᵀ * D = 0)
    (hQQ : Qᵀ * Q = 1) : (frame D Q).det ^ 2 = (Dᵀ * D).det := by
  have h := frame_conj D Q 1
  simp only [Matrix.mul_one] at h
  have hDQ : Dᵀ * Q = 0 := by rw [← transpose_transpose (Dᵀ * Q), transpose_mul, transpose_transpose, hQD,
    transpose_zero]
  rw [hDQ, hQD, hQQ] at h
  have := congrArg det h
  rw [det_mul, det_transpose, det_fromBlocks_zero₂₁, det_one, mul_one] at this
  rw [sq]; exact this

/-- **Gauge-fixed determinant.** If `K` is symmetric and annihilates the gauge directions
(`K D = 0`, the Ward identity), then
`det(K + ξ⁻¹ D Dᵀ) = ξ^{-k} · det(DᵀD) · det(QᵀKQ)`. -/
theorem fp_determinant (D : Matrix (κ ⊕ μ) κ ℝ) (Q : Matrix (κ ⊕ μ) μ ℝ) (hQD : Qᵀ * D = 0)
    (hQQ : Qᵀ * Q = 1) (K : Matrix (κ ⊕ μ) (κ ⊕ μ) ℝ) (hK : Kᵀ = K) (hKD : K * D = 0)
    (hG : (Dᵀ * D).det ≠ 0) (ξ : ℝ) :
    (K + ξ⁻¹ • (D * Dᵀ)).det = (ξ⁻¹) ^ Fintype.card κ * (Dᵀ * D).det * (Qᵀ * K * Q).det := by
  have hDQ : Dᵀ * Q = 0 := by rw [← transpose_transpose (Dᵀ * Q), transpose_mul, transpose_transpose, hQD,
    transpose_zero]
  have hDK : Dᵀ * K = 0 := by rw [← hK, ← transpose_mul, hKD, transpose_zero]
  have h := frame_conj D Q (K + ξ⁻¹ • (D * Dᵀ))
  have b11 : Dᵀ * (K + ξ⁻¹ • (D * Dᵀ)) * D = ξ⁻¹ • ((Dᵀ * D) * (Dᵀ * D)) := by
    rw [Matrix.mul_add, Matrix.add_mul, hDK, Matrix.zero_mul, zero_add, Matrix.mul_smul,
      Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have b12 : Dᵀ * (K + ξ⁻¹ • (D * Dᵀ)) * Q = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, hDK, Matrix.zero_mul, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hDQ, Matrix.mul_zero, Matrix.mul_zero,
      smul_zero]
  have b21 : Qᵀ * (K + ξ⁻¹ • (D * Dᵀ)) * D = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hKD, Matrix.mul_zero, zero_add,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hQD, Matrix.zero_mul, Matrix.zero_mul,
      smul_zero]
  have b22 : Qᵀ * (K + ξ⁻¹ • (D * Dᵀ)) * Q = Qᵀ * K * Q := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hQD,
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, add_zero]
  rw [b11, b12, b21, b22] at h
  have hd := congrArg det h
  rw [det_mul, det_mul, det_transpose, det_fromBlocks_zero₂₁, det_smul, det_mul] at hd
  have hS := frame_det_sq D Q hQD hQQ
  have : (frame D Q).det ^ 2 * (K + ξ⁻¹ • (D * Dᵀ)).det =
      (frame D Q).det ^ 2 * ((ξ⁻¹) ^ Fintype.card κ * (Dᵀ * D).det * (Qᵀ * K * Q).det) := by
    linear_combination hd - ((ξ⁻¹) ^ Fintype.card κ * (Dᵀ * D).det * (Qᵀ * K * Q).det) * hS
  exact mul_left_cancel₀ (by rw [hS]; exact hG) this

/-- **The ghost power.** In log-determinant form (the one-loop effective action), with
`G = DᵀD` and `K⊥ = QᵀKQ`:
`½ log det K⊥ − log |det S| = ½ log det K_ξ − log det G + (k/2) log ξ`.
The left side is the transverse Gaussian with the gauge-orbit Jacobian `|det S| = √det G`. So the
ghost determinant enters with power `1` against the vector's `½`: two ghost components. -/
theorem ghost_power (D : Matrix (κ ⊕ μ) κ ℝ) (Q : Matrix (κ ⊕ μ) μ ℝ) (hQD : Qᵀ * D = 0)
    (hQQ : Qᵀ * Q = 1) (K : Matrix (κ ⊕ μ) (κ ⊕ μ) ℝ) (hK : Kᵀ = K) (hKD : K * D = 0)
    (hG : 0 < (Dᵀ * D).det) (hKp : 0 < (Qᵀ * K * Q).det) {ξ : ℝ} (hξ : 0 < ξ) :
    (1 / 2) * Real.log (Qᵀ * K * Q).det - Real.log |(frame D Q).det| =
      (1 / 2) * Real.log (K + ξ⁻¹ • (D * Dᵀ)).det - Real.log (Dᵀ * D).det +
        (Fintype.card κ / 2) * Real.log ξ := by
  rw [fp_determinant D Q hQD hQQ K hK hKD hG.ne' ξ]
  have hS : Real.log |(frame D Q).det| = (1 / 2) * Real.log (Dᵀ * D).det := by
    rw [← frame_det_sq D Q hQD hQQ, ← sq_abs, Real.log_pow]; push_cast; ring
  have hx : 0 < (ξ⁻¹) ^ Fintype.card κ := by positivity
  rw [hS, Real.log_mul (by positivity) hKp.ne', Real.log_mul hx.ne' hG.ne', Real.log_pow,
    Real.log_inv]
  ring

end FP

/-! ## 2. Landau degeneracy proportional to `|b|` -/

/-- **Dilation.** Rescaling the kinetic momenta by `√λ` turns `[π₁, π₂] = i b` into
`[√λ π₁, √λ π₂] = i λ b`. A field `λb` is the field `b` seen through the dilation `x ↦ x/√λ`. -/
theorem dilation_algebra {R : Type*} [Ring R] [Algebra ℂ R] (p1 p2 : R) (b lam : ℝ)
    (hl : 0 ≤ lam) (h : p1 * p2 - p2 * p1 = (Complex.I * b) • (1 : R)) :
    (((Real.sqrt lam : ℝ) : ℂ) • p1) * (((Real.sqrt lam : ℝ) : ℂ) • p2) -
        (((Real.sqrt lam : ℝ) : ℂ) • p2) * (((Real.sqrt lam : ℝ) : ℂ) • p1) =
      (Complex.I * ((lam * b : ℝ) : ℂ)) • (1 : R) := by
  simp only [smul_mul_smul_comm, ← smul_sub, h, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]; push_cast; ring

/-- Plane areas scale by `r²` under `x ↦ r x`. -/
theorem area_scaling (r : ℝ) (s : Set (Fin 2 → ℝ)) :
    MeasureTheory.volume (r • s) = ENNReal.ofReal (r ^ 2) * MeasureTheory.volume s := by
  rw [MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (by positivity)]

/-- **Degeneracy is linear in `b`.** Suppose the state density per area `ρ(b)` satisfies:
the dilation `x ↦ x/√λ` maps the field-`b` states in a region `R` bijectively onto the
field-`λb` states in `R/√λ` (`dilation_algebra`), and areas scale by `1/λ` (`area_scaling`).
Then `ρ(λb) = λρ(b)`, so `ρ(b) = ρ(1)·b`. -/
theorem density_linear (ρ : ℝ → ℝ) (hscale : ∀ lam b, 0 < lam → 0 < b → ρ (lam * b) = lam * ρ b)
    {b : ℝ} (hb : 0 < b) : ρ b = ρ 1 * b := by
  have := hscale b 1 hb one_pos
  rw [mul_one] at this; rw [this]; ring

/-- **The coefficient is `1/2π`.** If `ρ(b) = ρ₁ b`, the kernel per area relative to the free
kernel `1/(4πt)` is `ρ₁ b / (2 sinh bt) · 4πt = 2πρ₁ · x/sinh x`. Matching the free field as
`b → 0` forces `ρ₁ = 1/2π`: one state per flux quantum. -/
theorem density_coefficient (ρ₁ : ℝ)
    (hmatch : Filter.Tendsto (fun x : ℝ => 2 * Real.pi * ρ₁ * (x / Real.sinh x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) : ρ₁ = 1 / (2 * Real.pi) := by
  obtain ⟨C, hC, h⟩ := FluctuationPremises.weak_field_normalization
  have hlim : Filter.Tendsto (fun x : ℝ => x / Real.sinh x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨min 1 (Real.sqrt (ε / (C + 1))), by positivity, fun {x} hx hdx => ?_⟩
    have hx0 : 0 < x := hx
    rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hdx
    have hx1 : x ≤ 1 := le_trans hdx.le (min_le_left _ _)
    have hxs : x < Real.sqrt (ε / (C + 1)) := lt_of_lt_of_le hdx (min_le_right _ _)
    have hx2 : x ^ 2 < ε / (C + 1) := by
      have := Real.sq_sqrt (show 0 ≤ ε / (C + 1) by positivity)
      nlinarith [Real.sqrt_nonneg (ε / (C + 1))]
    rw [Real.dist_eq]
    calc |x / Real.sinh x - 1| ≤ C * x ^ 2 := h x hx0 hx1
      _ ≤ (C + 1) * x ^ 2 := by nlinarith [sq_nonneg x]
      _ < (C + 1) * (ε / (C + 1)) := by gcongr
      _ = ε := by field_simp
  have h2 := hlim.const_mul (2 * Real.pi * ρ₁)
  rw [mul_one] at h2
  have := tendsto_nhds_unique (by simpa [mul_assoc] using h2) (by simpa [mul_assoc] using hmatch)
  field_simp
  linarith

end PMAction.FluctuationClosure
