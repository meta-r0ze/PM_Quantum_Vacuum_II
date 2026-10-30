import PMAction.RunningCoefficients
import PMAction.ConcreteFermion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section
namespace PMAction.RunningResponse
open Real Finset

/-! ## Spin response: the Zeeman factor `g = 2` from the Clifford relations -/

section Zeeman
variable {R : Type*} [Ring R]

/-- **Square of the transverse Dirac operator.** If `a₁, a₂` are anticommuting involutions
commuting with the kinetic momenta `p₁, p₂`, then
`(a₁p₁ + a₂p₂)² = p₁² + p₂² + a₁a₂ [p₁, p₂]`. -/
theorem dirac_square (a1 a2 p1 p2 : R) (h1 : a1 * a1 = 1) (h2 : a2 * a2 = 1)
    (hac : a1 * a2 = -(a2 * a1)) (c11 : a1 * p1 = p1 * a1) (c12 : a1 * p2 = p2 * a1)
    (c21 : a2 * p1 = p1 * a2) (c22 : a2 * p2 = p2 * a2) :
    (a1 * p1 + a2 * p2) ^ 2 = p1 ^ 2 + p2 ^ 2 + a1 * a2 * (p1 * p2 - p2 * p1) := by
  have e11 : a1 * p1 * (a1 * p1) = p1 * p1 := by
    rw [mul_assoc, ← mul_assoc p1, ← c11, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have e22 : a2 * p2 * (a2 * p2) = p2 * p2 := by
    rw [mul_assoc, ← mul_assoc p2, ← c22, ← mul_assoc, ← mul_assoc, h2, one_mul]
  have e12 : a1 * p1 * (a2 * p2) = a1 * a2 * (p1 * p2) := by
    rw [mul_assoc, ← mul_assoc p1, ← c21, mul_assoc, ← mul_assoc]
  have e21 : a2 * p2 * (a1 * p1) = -(a1 * a2 * (p2 * p1)) := by
    rw [mul_assoc, ← mul_assoc p2, ← c12, mul_assoc, ← mul_assoc, hac]; simp
  rw [sq, sq, sq, add_mul, mul_add, mul_add, e11, e22, e12, e21, mul_sub]
  abel

/-- The spin operator `Σ = −i a₁a₂` squares to one. -/
theorem spin_square [Algebra ℂ R] (a1 a2 : R) (h1 : a1 * a1 = 1) (h2 : a2 * a2 = 1)
    (hac : a1 * a2 = -(a2 * a1)) :
    ((-Complex.I) • (a1 * a2)) * ((-Complex.I) • (a1 * a2)) = 1 := by
  rw [smul_mul_smul_comm]
  have : a1 * a2 * (a1 * a2) = -1 := by
    calc a1 * a2 * (a1 * a2) = a1 * (a2 * a1) * a2 := by noncomm_ring
      _ = a1 * (-(a1 * a2)) * a2 := by rw [hac, neg_neg]
      _ = -1 := by
          rw [mul_neg, neg_mul, ← mul_assoc, h1, one_mul, h2]
  rw [this]
  simp

/-- **Zeeman form with `g = 2`.** In a magnetic field `b` (`[p₁, p₂] = i b`), the transverse
Dirac square is `p₁² + p₂² − b Σ` with `Σ² = 1`: each spin state is shifted by `∓b = −2 s_z b`
with `s_z = ±1/2`. -/
theorem zeeman [Algebra ℂ R] (a1 a2 p1 p2 : R) (b : ℂ) (h1 : a1 * a1 = 1) (h2 : a2 * a2 = 1)
    (hac : a1 * a2 = -(a2 * a1)) (c11 : a1 * p1 = p1 * a1) (c12 : a1 * p2 = p2 * a1)
    (c21 : a2 * p1 = p1 * a2) (c22 : a2 * p2 = p2 * a2)
    (hb : p1 * p2 - p2 * p1 = (Complex.I * b) • (1 : R)) :
    (a1 * p1 + a2 * p2) ^ 2 = p1 ^ 2 + p2 ^ 2 - b • ((-Complex.I) • (a1 * a2)) := by
  rw [dirac_square a1 a2 p1 p2 h1 h2 hac c11 c12 c21 c22, hb, mul_smul_comm, mul_one, smul_smul]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  rw [mul_neg, neg_neg, mul_comm]

end Zeeman

/-- Paper II's own Dirac matrices satisfy the hypotheses; their spin operator
`Σ₃ = −i α₁α₂` (axes `0, 1`) is an involution with zero trace: two states shifted each way. -/
theorem concrete_spin :
    ((-Complex.I) • (ConcreteFermion.alpha 0 * ConcreteFermion.alpha 1)) *
        ((-Complex.I) • (ConcreteFermion.alpha 0 * ConcreteFermion.alpha 1)) = 1 ∧
      Matrix.trace ((-Complex.I) • (ConcreteFermion.alpha 0 * ConcreteFermion.alpha 1)) = 0 := by
  have hc := ConcreteFermion.clifford
  refine ⟨spin_square _ _ (hc.1 0) (hc.1 1) ?_, ?_⟩
  · have := hc.2.2.1 0 1 (by decide)
    simpa [add_eq_zero_iff_eq_neg] using this
  · simp [ConcreteFermion.alpha, Matrix.trace, Fin.sum_univ_four]

/-! ## Orbital response: the Landau-level sum -/

/-- **Landau sum.** The levels `(2n + 1) x` (`x = |b| t`) give
`Σ_n e^{−(2n+1)x} = 1/(2 sinh x)`. -/
theorem landau_sum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => exp (-((2 * n + 1) * x))) (1 / (2 * sinh x)) := by
  have hr0 : 0 ≤ exp (-(2 * x)) := (exp_pos _).le
  have hr1 : exp (-(2 * x)) < 1 := by
    have := exp_lt_exp.mpr (show -(2 * x) < 0 by linarith); rwa [exp_zero] at this
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (exp (-x))
  have e : ∀ n : ℕ, exp (-x) * exp (-(2 * x)) ^ n = exp (-((2 * n + 1) * x)) := by
    intro n; rw [← exp_nat_mul, ← exp_add]; congr 1; ring
  simp only [e] at hg
  convert hg using 1
  rw [sinh_eq]
  have h1 : exp x - exp (-x) ≠ 0 := by
    have : exp (-x) < exp x := exp_lt_exp.mpr (by linarith)
    linarith
  have h2 : 1 - exp (-(2 * x)) ≠ 0 := by linarith
  have hx2 : exp (-(2 * x)) = exp (-x) * exp (-x) := by rw [← exp_add]; ring_nf
  field_simp
  rw [hx2]
  have : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
  nlinarith [this]

/-- **Pair kernel as a level sum.** A helicity pair in Landau levels `(2n+1)x` with Zeeman
shifts `∓a x`, weighted by the Landau degeneracy `2x` (flux per unit area, in units of `t`), sums
to `(x / sinh x)(e^{ax} + e^{−ax})`. -/
theorem pair_kernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 2 * x * (exp (-((2 * n + 1) * x) + a * x) +
        exp (-((2 * n + 1) * x) - a * x)))
      (x / sinh x * (exp (a * x) + exp (-(a * x)))) := by
  have h := (landau_sum hx).mul_left (2 * x * (exp (a * x) + exp (-(a * x))))
  convert h using 1
  · funext n
    rw [sub_eq_add_neg, exp_add, exp_add]; ring
  · have : sinh x ≠ 0 := (lt_of_lt_of_le hx (Real.self_le_sinh_iff.mpr hx.le)).ne'
    field_simp

/-! ## The `B²` coefficient per helicity pair -/

lemma cosh_rem {y : ℝ} (hy : |y| ≤ 1) : |exp y + exp (-y) - 2 - y ^ 2| ≤ 5 / 48 * y ^ 4 := by
  have b1 := Real.exp_bound hy (n := 4) (by norm_num)
  have b2 := Real.exp_bound (x := -y) (by rwa [abs_neg]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at b1 b2
  norm_num at b1 b2
  have hy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [hy4] at b1 b2
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  rw [abs_le]; constructor <;> linarith

lemma sinh_rem {x : ℝ} (hx : |x| ≤ 1) : |exp x - exp (-x) - 2 * x - x ^ 3 / 3| ≤ x ^ 4 / 50 * |x| := by
  have b1 := Real.exp_bound hx (n := 5) (by norm_num)
  have b2 := Real.exp_bound (x := -x) (by rwa [abs_neg]) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at b1 b2
  norm_num at b1 b2
  have hx5 : |x| ^ 5 = x ^ 4 * |x| := by
    rw [pow_succ, ← abs_pow]; rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
  rw [hx5] at b1 b2
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  rw [abs_le]; constructor <;> linarith

/-- **Heat-kernel coefficient of a helicity pair.** With Landau degeneracy factor `x/sinh x`
and Zeeman factors `e^{±a x}` (`a = 2s`), the pair's kernel is
`2 + (a² − 1/3) x² + O(x⁴)`: paramagnetic `a²`, diamagnetic `−1/3`. -/
theorem pair_coefficient (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → |a| * x ≤ 1 →
      |x / sinh x * (exp (a * x) + exp (-(a * x))) - 2 - (a ^ 2 - 1 / 3) * x ^ 2| ≤ C * x ^ 4 := by
  set κ := a ^ 2 - 1 / 3
  refine ⟨5 / 48 * a ^ 4 + 1 / 50 + |κ| / 6 + |κ| / 100, by positivity, fun x hx h1 hax => ?_⟩
  have hx1 : |x| ≤ 1 := by rw [abs_of_pos hx]; exact h1
  have hy : |a * x| ≤ 1 := by rw [abs_mul, abs_of_pos hx]; exact hax
  have hc := cosh_rem hy
  have hs := sinh_rem hx1
  rw [abs_of_pos hx] at hs
  set Rc := exp (a * x) + exp (-(a * x)) - 2 - (a * x) ^ 2
  set Rs := exp x - exp (-x) - 2 * x - x ^ 3 / 3
  have hsh : sinh x = x + x ^ 3 / 6 + Rs / 2 := by rw [sinh_eq]; simp only [Rs]; ring
  have hpos : x ≤ sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hsp : 0 < sinh x := lt_of_lt_of_le hx hpos
  have num : x * (exp (a * x) + exp (-(a * x))) - (2 + κ * x ^ 2) * sinh x =
      x * Rc - Rs - κ * x ^ 5 / 6 - κ * x ^ 2 * Rs / 2 := by
    rw [hsh]; simp only [Rc, κ]; ring
  have e : x / sinh x * (exp (a * x) + exp (-(a * x))) - 2 - κ * x ^ 2 =
      (x * (exp (a * x) + exp (-(a * x))) - (2 + κ * x ^ 2) * sinh x) / sinh x := by
    field_simp; ring
  rw [e, num, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
  have hRc : |x * Rc| ≤ 5 / 48 * a ^ 4 * x ^ 5 := by
    rw [abs_mul, abs_of_pos hx]
    calc x * |Rc| ≤ x * (5 / 48 * (a * x) ^ 4) := by gcongr
      _ = _ := by ring
  have hRs : |Rs| ≤ x ^ 5 / 50 := by
    calc |Rs| ≤ x ^ 4 / 50 * x := hs
      _ = _ := by ring
  have hk1 : |κ * x ^ 5 / 6| = |κ| * x ^ 5 / 6 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < x ^ 5)]; norm_num
  have hk2 : |κ * x ^ 2 * Rs / 2| ≤ |κ| * x ^ 5 / 100 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have : x ^ 2 * |Rs| ≤ x ^ 5 / 50 := by
      calc x ^ 2 * |Rs| ≤ 1 * (x ^ 5 / 50) := by
            apply mul_le_mul (by nlinarith) hRs (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have hk := abs_nonneg κ
    calc |κ| * x ^ 2 * |Rs| / |(2 : ℝ)| = |κ| * (x ^ 2 * |Rs|) / 2 := by norm_num; ring
      _ ≤ |κ| * (x ^ 5 / 50) / 2 := by gcongr
      _ = _ := by ring
  have tri : |x * Rc - Rs - κ * x ^ 5 / 6 - κ * x ^ 2 * Rs / 2| ≤
      |x * Rc| + |Rs| + |κ * x ^ 5 / 6| + |κ * x ^ 2 * Rs / 2| := by
    have a1 := abs_sub (x * Rc - Rs - κ * x ^ 5 / 6) (κ * x ^ 2 * Rs / 2)
    have a2 := abs_sub (x * Rc - Rs) (κ * x ^ 5 / 6)
    have a3 := abs_sub (x * Rc) Rs
    linarith
  have hx5 : x ^ 5 ≤ x ^ 4 * sinh x := by
    have : x ^ 5 = x ^ 4 * x := by ring
    rw [this]; gcongr
  have hbig : |x * Rc - Rs - κ * x ^ 5 / 6 - κ * x ^ 2 * Rs / 2| ≤
      (5 / 48 * a ^ 4 + 1 / 50 + |κ| / 6 + |κ| / 100) * x ^ 5 := by
    rw [hk1] at tri
    linarith
  calc _ ≤ (5 / 48 * a ^ 4 + 1 / 50 + |κ| / 6 + |κ| / 100) * x ^ 5 := hbig
    _ ≤ (5 / 48 * a ^ 4 + 1 / 50 + |κ| / 6 + |κ| / 100) * (x ^ 4 * sinh x) := by
        gcongr
    _ = _ := by ring

/-! ## The running coefficient per unit index -/

/-- **Spin decomposition derived.** The `B²` coefficient of a helicity pair with Zeeman factor
`a = 2s`, times the statistics sign `(−1)^{2s}`, is `RunningCoefficients.spinTerm`. -/
theorem spin_term_from_response (twoS : ℕ) :
    ((RunningCoefficients.spinTerm twoS : ℚ) : ℝ) = (-1) ^ twoS * (((twoS : ℝ)) ^ 2 - 1 / 3) := by
  simp [RunningCoefficients.spinTerm]

/-- Spin `1/2` uses the Zeeman factor `a = 1` derived above (`zeeman`, `concrete_spin`). -/
theorem weyl_term : (-1 : ℝ) ^ 1 * ((1 : ℝ) ^ 2 - 1 / 3) = -2 / 3 := by norm_num

end PMAction.RunningResponse
