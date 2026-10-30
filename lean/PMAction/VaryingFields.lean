import PMAction.D4Gauge
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Varying and non-Abelian gauge fields: controlled D₄ continuum limit

`GaugeContinuum` treats a constant Abelian field. Here the field is a differentiable
connection one-form `A : E → (E →L[ℝ] 𝔄)` with values in a complete normed real algebra `𝔄`
(for the D₄ statement, `u(N)` inside `N × N` complex matrices). Links are midpoint
exponentials `U(y → y+hv) = exp(h A(y + h v/2) v)`.

* `exp_second`: `‖exp z − 1 − z − z²/2‖ ≤ ‖z‖³ e^{‖z‖}` in any complete normed real algebra.
* `mul_expand`: second-order product rule with an explicit cubic remainder (noncommutative).
* `taylor_line`: first-order Taylor bound for the connection from a Lipschitz derivative at `x`.
* `triangle_expand`: the elementary triangle `x → x+ha → x+hb → x` has holonomy
  `1 + (h²/2) F(a,b) + O(h³)` with `F(a,b) = ∂_a A_b − ∂_b A_a + [A_a, A_b]`, uniformly for
  `h ∈ [0,1]`. This is the non-Abelian path-order/BCH control the Abelian proof did not need.
* `triangle_unitary`: a skew-adjoint connection has unitary holonomy.
* `wilson_sum`: for unitary `P`, `Σ |(P−1)_{ij}|² = 2 Re tr(1 − P)`.
* `triangle_wilson`: `Re tr(1 − P_h)/h⁴ = Σ_{ij} |F(a,b)_{ij}|²/8 + O(h)`.
* `tri_entry_sum`: with `D4Gauge.flux_sum`, `Σ_{192 triangles} |F(a,b)|² = 48 Σ_{μν} |F_{μν}|²`.
* `d4_yang_mills`, `d4_yang_mills_tendsto`: the actual D₄ minimal-triangle density
  `(β/12) Σ_p Re tr(1 − P_p)/h⁴` converges, with `O(h)` error, to
  `(β/2) Σ_{μν} Σ_{ij} |F_{μν,ij}|²`.

For `N = 1` and `A = i g a`, this is `(βg²/2) Σ f_{μν}²`, matching `GaugeContinuum.density_limit`
at every point of a nonconstant field.

Hypotheses not derived from the current model: the links are midpoint exponentials of a smooth
connection; the formal hypotheses require differentiability everywhere and a global
derivative bound `‖DA y - DA x‖ ≤ L * ‖y - x‖` about the base point; the group, representation and `β` are
inputs. The result is a pointwise classical action density (Euclidean); no Riemann-sum
integration over sites, quantum continuum limit or Lorentzian continuation is claimed.
-/

noncomputable section
namespace PMAction.VaryingFields
open NormedSpace
open scoped Nat

section Ring
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Third-order remainder of the exponential in any complete normed real algebra. -/
theorem exp_second [CompleteSpace R] (z : R) :
    ‖exp z - (1 + z + (1/2 : ℝ) • z ^ 2)‖ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ := by
  set f : ℕ → R := fun n => ((n ! : ℝ)⁻¹) • z ^ n with hf
  have hn : Summable fun n => ‖f n‖ := norm_expSeries_summable' (𝕂 := ℝ) z
  have hs : Summable f := hn.of_norm
  have he : exp z = ∑' n, f n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  have hsplit := hs.sum_add_tsum_nat_add 3
  have hhead : (∑ i ∈ Finset.range 3, f i) = 1 + z + (1/2 : ℝ) • z ^ 2 := by
    simp [hf, Finset.sum_range_succ, Nat.factorial]
  have htail : exp z - (1 + z + (1/2 : ℝ) • z ^ 2) = ∑' n, f (n + 3) := by
    rw [he, ← hsplit, hhead]; abel
  rw [htail]
  have hn3 : Summable fun n => ‖f (n + 3)‖ := (summable_nat_add_iff 3).mpr hn
  have hbd : ∀ n, ‖f (n + 3)‖ ≤ ‖z‖ ^ 3 * (‖z‖ ^ n / n !) := by
    intro n
    simp only [hf, norm_smul, norm_inv, Real.norm_natCast]
    have hp : ‖z ^ (n + 3)‖ ≤ ‖z‖ ^ (n + 3) := norm_pow_le' z (by omega)
    have hfac : (n ! : ℝ) ≤ (n + 3)! := by exact_mod_cast Nat.factorial_le (by omega)
    have hpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    calc ((n + 3)! : ℝ)⁻¹ * ‖z ^ (n + 3)‖ ≤ (n ! : ℝ)⁻¹ * ‖z‖ ^ (n + 3) := by
          apply mul_le_mul (inv_anti₀ hpos hfac) hp (norm_nonneg _) (by positivity)
      _ = ‖z‖ ^ 3 * (‖z‖ ^ n / n !) := by rw [pow_add]; field_simp
  have hreal : Real.exp ‖z‖ = ∑' n, ‖z‖ ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc ‖∑' n, f (n + 3)‖ ≤ ∑' n, ‖f (n + 3)‖ := norm_tsum_le_tsum_norm hn3
    _ ≤ ∑' n, ‖z‖ ^ 3 * (‖z‖ ^ n / n !) :=
        hn3.tsum_le_tsum hbd ((Real.summable_pow_div_factorial _).mul_left _)
    _ = ‖z‖ ^ 3 * Real.exp ‖z‖ := by rw [tsum_mul_left, hreal]

omit [NormedAlgebra ℝ R] in
lemma norm_add8 (x1 x2 x3 x4 x5 x6 x7 x8 : R) :
    ‖x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8‖ ≤
      ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ + ‖x5‖ + ‖x6‖ + ‖x7‖ + ‖x8‖ := by
  have := norm_add_le (x1 + x2 + x3 + x4 + x5 + x6 + x7) x8
  have := norm_add_le (x1 + x2 + x3 + x4 + x5 + x6) x7
  have := norm_add_le (x1 + x2 + x3 + x4 + x5) x6
  have := norm_add_le (x1 + x2 + x3 + x4) x5
  have := norm_add_le (x1 + x2 + x3) x4
  have := norm_add_le (x1 + x2) x3
  have := norm_add_le x1 x2
  linarith

lemma norm_smul_pow_le {h M : ℝ} {x : R} (k : ℕ) (hx : ‖x‖ ≤ M) :
    ‖h ^ k • x‖ ≤ |h| ^ k * M := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]; gcongr

/-- Second-order product rule with an explicit cubic remainder. -/
theorem mul_expand {h K M : ℝ} (hh : |h| ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) {U V a b c d : R}
    (hU : ‖U - (1 + h • a + h ^ 2 • b)‖ ≤ K * |h| ^ 3)
    (hV : ‖V - (1 + h • c + h ^ 2 • d)‖ ≤ K * |h| ^ 3)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M) :
    ‖U * V - (1 + h • (a + c) + h ^ 2 • (b + d + a * c))‖ ≤
      (2 * K + 3 * M ^ 2 + 4 * M * K + K ^ 2) * |h| ^ 3 := by
  have hac : h ^ 2 • (a * c) = (h • a) * (h • c) := by rw [smul_mul_smul]; ring_nf
  have e2 : h ^ 2 • (b + d + a * c) = h ^ 2 • b + h ^ 2 • d + (h • a) * (h • c) := by
    rw [smul_add, smul_add, hac]
  rw [smul_add, e2]
  have hA : ‖h • a‖ ≤ |h| * M := by simpa using norm_smul_pow_le (h := h) 1 ha
  have hB : ‖h ^ 2 • b‖ ≤ |h| ^ 2 * M := norm_smul_pow_le 2 hb
  have hC : ‖h • c‖ ≤ |h| * M := by simpa using norm_smul_pow_le (h := h) 1 hc
  have hD : ‖h ^ 2 • d‖ ≤ |h| ^ 2 * M := norm_smul_pow_le 2 hd
  generalize h • a = A at hA hU
  generalize h ^ 2 • b = B at hB hU
  generalize h • c = C at hC hV
  generalize h ^ 2 • d = D at hD hV
  generalize hrU : U - (1 + A + B) = rU at hU
  generalize hrV : V - (1 + C + D) = rV at hV
  have eU : U = 1 + A + B + rU := by rw [← hrU]; abel
  have eV : V = 1 + C + D + rV := by rw [← hrV]; abel
  have key : U * V - (1 + (A + C) + (B + D + A * C)) =
      rU + rV + A * D + B * C + B * D + (A + B) * rV + rU * (C + D) + rU * rV := by
    rw [eU, eV]; noncomm_ring
  rw [key]
  have h0 : 0 ≤ |h| := abs_nonneg h
  have h2 : |h| ^ 2 ≤ 1 := pow_le_one₀ h0 hh
  have h3 : 0 ≤ |h| ^ 3 := by positivity
  have h4 : |h| ^ 4 ≤ |h| ^ 3 := pow_le_pow_of_le_one h0 hh (by norm_num)
  have h6 : |h| ^ 6 ≤ |h| ^ 3 := pow_le_pow_of_le_one h0 hh (by norm_num)
  have pm : ∀ x y : R, ∀ p q : ℝ, ‖x‖ ≤ p → ‖y‖ ≤ q → 0 ≤ q → ‖x * y‖ ≤ p * q :=
    fun x y p q hx hy hq => (norm_mul_le _ _).trans
      (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))
  have nAB : ‖A + B‖ ≤ 2 * M := by
    have := norm_add_le A B; nlinarith [mul_le_mul_of_nonneg_right h2 hM]
  have nCD : ‖C + D‖ ≤ 2 * M := by
    have := norm_add_le C D; nlinarith [mul_le_mul_of_nonneg_right h2 hM]
  have e1 := pm A D _ _ hA hD (by positivity)
  have e2 := pm B C _ _ hB hC (by positivity)
  have e3 := pm B D _ _ hB hD (by positivity)
  have e4 := pm (A + B) rV _ _ nAB hV (by positivity)
  have e5 := pm rU (C + D) _ _ hU nCD (by positivity)
  have e6 := pm rU rV _ _ hU hV (by positivity)
  have q1 : |h| * M * (|h| ^ 2 * M) = M ^ 2 * |h| ^ 3 := by ring
  have q2 : |h| ^ 2 * M * (|h| * M) = M ^ 2 * |h| ^ 3 := by ring
  have q3 : |h| ^ 2 * M * (|h| ^ 2 * M) ≤ M ^ 2 * |h| ^ 3 := by
    have : |h| ^ 2 * M * (|h| ^ 2 * M) = M ^ 2 * |h| ^ 4 := by ring
    rw [this]; gcongr
  have q6 : K * |h| ^ 3 * (K * |h| ^ 3) ≤ K ^ 2 * |h| ^ 3 := by
    have : K * |h| ^ 3 * (K * |h| ^ 3) = K ^ 2 * |h| ^ 6 := by ring
    rw [this]; gcongr
  have := norm_add8 rU rV (A * D) (B * C) (B * D) ((A + B) * rV) (rU * (C + D)) (rU * rV)
  nlinarith

omit [NormedAlgebra ℝ R] in
lemma prod_diff {x y x0 y0 : R} {M D h : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) (hy0 : ‖y0‖ ≤ M)
    (dx : ‖x - x0‖ ≤ D * h) (dy : ‖y - y0‖ ≤ D * h) :
    ‖x * y - x0 * y0‖ ≤ 2 * M * (D * h) := by
  have e : x * y - x0 * y0 = x * (y - y0) + (x - x0) * y0 := by noncomm_ring
  rw [e]
  have h1 : ‖x * (y - y0)‖ ≤ M * (D * h) := (norm_mul_le _ _).trans
    (mul_le_mul hx dy (norm_nonneg _) hM)
  have h2 : ‖(x - x0) * y0‖ ≤ (D * h) * M := (norm_mul_le _ _).trans
    (mul_le_mul dx hy0 (norm_nonneg _) ((norm_nonneg _).trans dx))
  have := norm_add_le (x * (y - y0)) ((x - x0) * y0)
  nlinarith

end Ring

section Connection
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order Taylor expansion of a connection one-form along a line, with a
quadratic remainder controlled by a Lipschitz bound on its derivative at the base point. -/
theorem taylor_line {A : E → E →L[ℝ] R} {DA : E → E →L[ℝ] (E →L[ℝ] R)} {x w : E} {L t : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖) (ht : 0 ≤ t) :
    ‖A (x + t • w) - A x - t • DA x w‖ ≤ L * ‖w‖ ^ 2 * t ^ 2 := by
  set g : ℝ → (E →L[ℝ] R) := fun s => A (x + s • w) - s • DA x w with hgdef
  have hg : ∀ s, HasDerivAt g (DA (x + s • w) w - DA x w) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add x
    have h1 := (hA (x + s • w)).comp_hasDerivAt s hl
    have h2 : HasDerivAt (fun s : ℝ => s • DA x w) (DA x w) s := by
      simpa using (hasDerivAt_id s).smul_const (DA x w)
    exact h1.sub h2
  have hb : ∀ s ∈ Set.Ico 0 t, ‖DA (x + s • w) w - DA x w‖ ≤ L * ‖w‖ ^ 2 * t := by
    intro s hs
    have heq : DA (x + s • w) w - DA x w = (DA (x + s • w) - DA x) w := by simp
    rw [heq]
    have hs' : ‖s • w‖ ≤ t * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
    calc _ ≤ ‖DA (x + s • w) - DA x‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * (t * ‖w‖)) * ‖w‖ := by
          gcongr
          exact (hL _).trans (by simpa using mul_le_mul_of_nonneg_left hs' hL0)
      _ = L * ‖w‖ ^ 2 * t := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := t)
    (fun s _ => (hg s).hasDerivWithinAt) hb t ⟨ht, le_rfl⟩
  have e : g t - g 0 = A (x + t • w) - A x - t • DA x w := by
    show A (x + t • w) - t • DA x w - (A (x + (0:ℝ) • w) - (0:ℝ) • DA x w) = _
    have z : ((0:ℝ) • DA x w) = 0 := by ext; simp
    rw [zero_smul, z, add_zero, sub_zero]; abel
  rw [e] at this
  calc _ ≤ L * ‖w‖ ^ 2 * t * (t - 0) := this
    _ = _ := by ring

theorem taylor_apply {A : E → E →L[ℝ] R} {DA : E → E →L[ℝ] (E →L[ℝ] R)} {x w : E} {L t : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖) (ht : 0 ≤ t) (v : E) :
    ‖A (x + t • w) v - A x v - t • DA x w v‖ ≤ L * ‖w‖ ^ 2 * ‖v‖ * t ^ 2 := by
  have e : A (x + t • w) v - A x v - t • DA x w v = (A (x + t • w) - A x - t • DA x w) v := by
    simp
  rw [e]
  calc _ ≤ ‖A (x + t • w) - A x - t • DA x w‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L * ‖w‖ ^ 2 * t ^ 2) * ‖v‖ := by gcongr; exact taylor_line hA hL0 hL ht
    _ = _ := by ring

omit [NormedSpace ℝ E] in
lemma coeff_close {c c0 g : R} {T h : ℝ} (hT : 0 ≤ T) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (e : ‖c - c0 - (h / 2) • g‖ ≤ T * h ^ 2) : ‖c - c0‖ ≤ (‖g‖ + T) * h := by
  have eq : c - c0 = (c - c0 - (h / 2) • g) + (h / 2) • g := by abel
  rw [eq]
  have hg : ‖(h / 2) • g‖ ≤ h * ‖g‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg g]
  have hh : T * h ^ 2 ≤ T * h := by
    apply mul_le_mul_of_nonneg_left _ hT; nlinarith
  have := norm_add_le (c - c0 - (h / 2) • g) ((h / 2) • g)
  nlinarith

omit [NormedSpace ℝ E] in
lemma exp_link [CompleteSpace R] {c : R} {M0 h : ℝ} (hc : ‖c‖ ≤ M0) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ‖exp (h • c) - (1 + h • c + h ^ 2 • ((1 / 2 : ℝ) • c ^ 2))‖ ≤
      M0 ^ 3 * Real.exp M0 * |h| ^ 3 := by
  have e : (1 / 2 : ℝ) • (h • c) ^ 2 = h ^ 2 • ((1 / 2 : ℝ) • c ^ 2) := by
    rw [smul_pow, smul_comm]
  have hb := exp_second (h • c)
  rw [e] at hb
  have hn : ‖h • c‖ ≤ h * M0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]; gcongr
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans hc
  have hn' : ‖h • c‖ ≤ M0 := hn.trans (by nlinarith)
  rw [abs_of_nonneg h0]
  calc _ ≤ ‖h • c‖ ^ 3 * Real.exp ‖h • c‖ := hb
    _ ≤ (h * M0) ^ 3 * Real.exp M0 := by
        gcongr
    _ = _ := by ring

/-- Midpoint link from `y` to `y + h v`: the exponential of the potential's
component along the edge, evaluated at the edge midpoint. -/
def link (A : E → E →L[ℝ] R) (y v : E) (h : ℝ) : R := exp (h • A (y + (h / 2) • v) v)

/-- Holonomy of the elementary triangle `x → x + h a → x + h b → x`.  The last factor is
the reverse of the link `x → x + h b` (its inverse whenever exponentials are invertible). -/
def triangle (A : E → E →L[ℝ] R) (x a b : E) (h : ℝ) : R :=
  link A x a h * link A (x + h • a) (b - a) h * exp (h • -(A (x + (h / 2) • b) b))

/-- Non-Abelian curvature `F(a,b) = ∂_a A_b − ∂_b A_a + [A_a, A_b]` at `x`. -/
def curvature (A : E → E →L[ℝ] R) (DA : E → E →L[ℝ] (E →L[ℝ] R)) (x a b : E) : R :=
  DA x a b - DA x b a + (A x a * A x b - A x b * A x a)

set_option maxHeartbeats 1000000 in
/-- **Varying non-Abelian triangle holonomy.**  For a `C^{1,1}` connection one-form (with the stated global derivative bound
about the base point), the midpoint-link triangle holonomy is
`1 + (h²/2) F(a,b) + O(h³)`, with a constant independent of `h ∈ [0,1]`. -/
theorem triangle_expand [CompleteSpace R] {A : E → E →L[ℝ] R}
    {DA : E → E →L[ℝ] (E →L[ℝ] R)} {x : E} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖) (a b : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖triangle A x a b h - (1 + (h ^ 2 / 2) • curvature A DA x a b)‖ ≤ C * h ^ 3 := by
  -- Taylor data for the three edges.
  set X := A x a
  set Y := A x (b - a)
  set Z := A x b
  set g1 := DA x a a
  set g2 := DA x (a + b) (b - a)
  set g3 := -DA x b b
  obtain ⟨T1, hT1d⟩ : ∃ T, T = L * ‖a‖ ^ 2 * ‖a‖ / 4 := ⟨_, rfl⟩
  obtain ⟨T2, hT2d⟩ : ∃ T, T = L * ‖a + b‖ ^ 2 * ‖b - a‖ / 4 := ⟨_, rfl⟩
  obtain ⟨T3, hT3d⟩ : ∃ T, T = L * ‖b‖ ^ 2 * ‖b‖ / 4 := ⟨_, rfl⟩
  have hT1 : 0 ≤ T1 := by rw [hT1d]; positivity
  have hT2 : 0 ≤ T2 := by rw [hT2d]; positivity
  have hT3 : 0 ≤ T3 := by rw [hT3d]; positivity
  obtain ⟨D, hDd⟩ : ∃ D, D = (‖g1‖ + T1) + (‖g2‖ + T2) + (‖g3‖ + T3) := ⟨_, rfl⟩
  have hD : 0 ≤ D := by rw [hDd]; positivity
  obtain ⟨M0, hM0d⟩ : ∃ M, M = ‖X‖ + ‖Y‖ + ‖-Z‖ + D := ⟨_, rfl⟩
  have hM0 : 0 ≤ M0 := by rw [hM0d]; positivity
  obtain ⟨M, hMd⟩ : ∃ M', M' = M0 + M0 ^ 2 := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMd]; positivity
  obtain ⟨K, hKd⟩ : ∃ K, K = M0 ^ 3 * Real.exp M0 := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  obtain ⟨K1, hK1d⟩ : ∃ K', K' = 2 * K + 3 * M ^ 2 + 4 * M * K + K ^ 2 := ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := by rw [hK1d]; positivity
  obtain ⟨K', hK'd⟩ : ∃ K'', K'' = K1 + K := ⟨_, rfl⟩
  have hK' : 0 ≤ K' := by rw [hK'd]; positivity
  obtain ⟨M', hM'd⟩ : ∃ M'', M'' = 3 * M + M ^ 2 := ⟨_, rfl⟩
  have hM' : 0 ≤ M' := by rw [hM'd]; positivity
  obtain ⟨K2, hK2d⟩ : ∃ K'', K'' = 2 * K' + 3 * M' ^ 2 + 4 * M' * K' + K' ^ 2 := ⟨_, rfl⟩
  have hK2 : 0 ≤ K2 := by rw [hK2d]; positivity
  refine ⟨K2 + (T1 + T2 + T3) + 12 * M0 * D, by positivity, ?_⟩
  intro h h0 h1
  have hah : |h| = h := abs_of_nonneg h0
  have ht : 0 ≤ h / 2 := by positivity
  set c1 := A (x + (h / 2) • a) a
  set c2 := A (x + (h / 2) • (a + b)) (b - a)
  set c3 := -(A (x + (h / 2) • b) b)
  -- Taylor remainders
  have tq : ∀ q : ℝ, q * (h / 2) ^ 2 = q / 4 * h ^ 2 := fun q => by ring
  have e1 : ‖c1 - X - (h / 2) • g1‖ ≤ T1 * h ^ 2 := by
    have := taylor_apply (w := a) hA hL0 hL ht a
    rw [tq, ← hT1d] at this; exact this
  have e2 : ‖c2 - Y - (h / 2) • g2‖ ≤ T2 * h ^ 2 := by
    have := taylor_apply (w := a + b) hA hL0 hL ht (b - a)
    rw [tq, ← hT2d] at this; exact this
  have e3 : ‖c3 - -Z - (h / 2) • g3‖ ≤ T3 * h ^ 2 := by
    have := taylor_apply (w := b) hA hL0 hL ht b
    rw [tq, ← hT3d] at this
    have eq : c3 - -Z - (h / 2) • g3 = -(A (x + (h / 2) • b) b - A x b - (h / 2) • DA x b b) := by
      simp only [c3, Z, g3, smul_neg]; abel
    rw [eq, norm_neg]; exact this
  have d1 := coeff_close hT1 h0 h1 e1
  have d2 := coeff_close hT2 h0 h1 e2
  have d3 := coeff_close hT3 h0 h1 e3
  have dD1 : ‖c1 - X‖ ≤ D * h := d1.trans (mul_le_mul_of_nonneg_right (by rw [hDd]; linarith [norm_nonneg g2, norm_nonneg g3]) h0)
  have dD2 : ‖c2 - Y‖ ≤ D * h := d2.trans (mul_le_mul_of_nonneg_right (by rw [hDd]; linarith [norm_nonneg g1, norm_nonneg g3]) h0)
  have dD3 : ‖c3 - -Z‖ ≤ D * h := d3.trans (mul_le_mul_of_nonneg_right (by rw [hDd]; linarith [norm_nonneg g1, norm_nonneg g2]) h0)
  have hDh : D * h ≤ D := by nlinarith
  have nb : ∀ c c0 : R, ‖c - c0‖ ≤ D * h → ‖c0‖ ≤ ‖X‖ + ‖Y‖ + ‖-Z‖ → ‖c‖ ≤ M0 := by
    intro c c0 hc hc0
    have := norm_le_insert' c c0
    rw [hM0d]; linarith
  have n1 : ‖c1‖ ≤ M0 := nb c1 X dD1 (by linarith [norm_nonneg Y, norm_nonneg (-Z)])
  have n2 : ‖c2‖ ≤ M0 := nb c2 Y dD2 (by linarith [norm_nonneg X, norm_nonneg (-Z)])
  have n3 : ‖c3‖ ≤ M0 := nb c3 (-Z) dD3 (by linarith [norm_nonneg X, norm_nonneg Y])
  have m1 : ‖X‖ ≤ M0 := by rw [hM0d]; linarith [hD, norm_nonneg Y, norm_nonneg (-Z)]
  have m2 : ‖Y‖ ≤ M0 := by rw [hM0d]; linarith [hD, norm_nonneg X, norm_nonneg (-Z)]
  have m3 : ‖-Z‖ ≤ M0 := by rw [hM0d]; linarith [hD, norm_nonneg X, norm_nonneg Y]
  -- quadratic coefficients
  have nq : ∀ c : R, ‖c‖ ≤ M0 → ‖(1 / 2 : ℝ) • c ^ 2‖ ≤ M := by
    intro c hc
    rw [norm_smul, hMd]
    have : ‖c ^ 2‖ ≤ M0 ^ 2 :=
      (norm_pow_le' c (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg _) hc 2)
    have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h2]; linarith [norm_nonneg (c ^ 2)]
  have nl : ∀ c : R, ‖c‖ ≤ M0 → ‖c‖ ≤ M := fun c hc => by rw [hMd]; linarith [sq_nonneg M0]
  -- exponentials
  have x1 : ‖exp (h • c1) - (1 + h • c1 + h ^ 2 • ((1 / 2 : ℝ) • c1 ^ 2))‖ ≤ K * |h| ^ 3 := by
    have := exp_link n1 h0 h1; rwa [← hKd] at this
  have x2 : ‖exp (h • c2) - (1 + h • c2 + h ^ 2 • ((1 / 2 : ℝ) • c2 ^ 2))‖ ≤ K * |h| ^ 3 := by
    have := exp_link n2 h0 h1; rwa [← hKd] at this
  have x3 : ‖exp (h • c3) - (1 + h • c3 + h ^ 2 • ((1 / 2 : ℝ) • c3 ^ 2))‖ ≤ K * |h| ^ 3 := by
    have := exp_link n3 h0 h1; rwa [← hKd] at this
  have hU1 : link A x a h = exp (h • c1) := rfl
  have hU2 : link A (x + h • a) (b - a) h = exp (h • c2) := by
    simp only [link, c2]
    congr 4
    module
  have hP : triangle A x a b h = exp (h • c1) * exp (h • c2) * exp (h • c3) := by
    rw [triangle, hU1, hU2]
  -- product expansion
  have s1 := mul_expand (h := h) (K := K) (M := M) (by rw [hah]; exact h1) hK hM x1 x2
    (nl _ n1) (nq _ n1) (nl _ n2) (nq _ n2)
  rw [← hK1d] at s1
  have hKK' : K1 ≤ K' := by rw [hK'd]; linarith
  have hKK : K ≤ K' := by rw [hK'd]; linarith
  have s1' := s1.trans (mul_le_mul_of_nonneg_right hKK' (by positivity))
  have x3' := x3.trans (mul_le_mul_of_nonneg_right hKK (by positivity))
  have hMM : M ≤ M' := by rw [hM'd]; linarith [sq_nonneg M]
  have na : ‖c1 + c2‖ ≤ M' := by
    have := norm_add_le c1 c2; rw [hM'd]; linarith [nl _ n1, nl _ n2, sq_nonneg M]
  have nbq : ‖(1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2‖ ≤ M' := by
    have q1 := nq _ n1; have q2 := nq _ n2
    have hc : ‖c1 * c2‖ ≤ M * M :=
      (norm_mul_le _ _).trans (mul_le_mul (nl _ n1) (nl _ n2) (norm_nonneg _) hM)
    have := norm_add_le ((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2) (c1 * c2)
    have := norm_add_le ((1 / 2 : ℝ) • c1 ^ 2) ((1 / 2 : ℝ) • c2 ^ 2)
    have : M * M = M ^ 2 := by ring
    rw [hM'd]; linarith
  have s2 := mul_expand (h := h) (K := K') (M := M') (by rw [hah]; exact h1) hK' hM' s1' x3'
    na nbq ((nl _ n3).trans hMM) ((nq _ n3).trans hMM)
  rw [← hP, hah, ← hK2d] at s2
  -- linear coefficient
  set G := DA x a b - DA x b a
  have hS : (c1 + c2 + c3) - (h / 2) • G = (c1 - X - (h / 2) • g1) + (c2 - Y - (h / 2) • g2) +
      (c3 - -Z - (h / 2) • g3) := by
    have hY : Y = Z - X := by simp only [Y, Z, X, map_sub]
    have hg : G = g1 + g2 + g3 := by
      simp only [G, g1, g2, g3, map_add, map_sub]
      simp only [FunLike.coe_add, Pi.add_apply]
      abel
    rw [hg, hY]; simp only [smul_add]; abel
  have eS : ‖(c1 + c2 + c3) - (h / 2) • G‖ ≤ (T1 + T2 + T3) * h ^ 2 := by
    rw [hS]
    have := norm_add_le ((c1 - X - (h / 2) • g1) + (c2 - Y - (h / 2) • g2)) (c3 - -Z - (h / 2) • g3)
    have := norm_add_le (c1 - X - (h / 2) • g1) (c2 - Y - (h / 2) • g2)
    linarith
  -- quadratic coefficient
  set Q := X * Z - Z * X
  have hT : ((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q = (1 / 2 : ℝ) • (c1 * c1 - X * X) + (1 / 2 : ℝ) • (c2 * c2 - Y * Y) +
      (c1 * c2 - X * Y) + (1 / 2 : ℝ) • (c3 * c3 - -Z * -Z) + (c1 * c3 - X * -Z) +
      (c2 * c3 - Y * -Z) := by
    have hY : Y = Z - X := by simp only [Y, Z, X, map_sub]
    simp only [Q, hY, sq, add_mul, sub_mul, mul_sub, neg_mul, mul_neg]
    module
  have pd : ∀ x y x0 y0 : R, ‖x‖ ≤ M0 → ‖y0‖ ≤ M0 → ‖x - x0‖ ≤ D * h → ‖y - y0‖ ≤ D * h →
      ‖x * y - x0 * y0‖ ≤ 2 * M0 * (D * h) := fun x y x0 y0 hx hy dx dy =>
    prod_diff hM0 hx hy dx dy
  have half : ∀ u : R, ‖(1 / 2 : ℝ) • u‖ ≤ ‖u‖ := fun u => by
    rw [norm_smul]; have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]; nlinarith [norm_nonneg u]
  have p1 := (half _).trans (pd c1 c1 X X n1 m1 dD1 dD1)
  have p2 := (half _).trans (pd c2 c2 Y Y n2 m2 dD2 dD2)
  have p3 := pd c1 c2 X Y n1 m2 dD1 dD2
  have p4 := (half _).trans (pd c3 c3 (-Z) (-Z) n3 m3 dD3 dD3)
  have p5 := pd c1 c3 X (-Z) n1 m3 dD1 dD3
  have p6 := pd c2 c3 Y (-Z) n2 m3 dD2 dD3
  have eT : ‖((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q‖ ≤ 12 * M0 * D * h := by
    rw [hT]
    have := norm_add_le ((1 / 2 : ℝ) • (c1 * c1 - X * X) + (1 / 2 : ℝ) • (c2 * c2 - Y * Y) +
      (c1 * c2 - X * Y) + (1 / 2 : ℝ) • (c3 * c3 - -Z * -Z) + (c1 * c3 - X * -Z)) (c2 * c3 - Y * -Z)
    have := norm_add_le ((1 / 2 : ℝ) • (c1 * c1 - X * X) + (1 / 2 : ℝ) • (c2 * c2 - Y * Y) +
      (c1 * c2 - X * Y) + (1 / 2 : ℝ) • (c3 * c3 - -Z * -Z)) (c1 * c3 - X * -Z)
    have := norm_add_le ((1 / 2 : ℝ) • (c1 * c1 - X * X) + (1 / 2 : ℝ) • (c2 * c2 - Y * Y) +
      (c1 * c2 - X * Y)) ((1 / 2 : ℝ) • (c3 * c3 - -Z * -Z))
    have := norm_add_le ((1 / 2 : ℝ) • (c1 * c1 - X * X) + (1 / 2 : ℝ) • (c2 * c2 - Y * Y))
      (c1 * c2 - X * Y)
    have := norm_add_le ((1 / 2 : ℝ) • (c1 * c1 - X * X)) ((1 / 2 : ℝ) • (c2 * c2 - Y * Y))
    linarith
  -- assemble
  set P := triangle A x a b h
  have hF : curvature A DA x a b = G + Q := rfl
  have key : P - (1 + (h ^ 2 / 2) • curvature A DA x a b) =
      (P - (1 + h • (c1 + c2 + c3) + h ^ 2 • ((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 +
        c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3))) +
      h • ((c1 + c2 + c3) - (h / 2) • G) + h ^ 2 • (((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q) := by
    rw [hF]; module
  rw [key]
  have n2' : ‖h • ((c1 + c2 + c3) - (h / 2) • G)‖ ≤ (T1 + T2 + T3) * h ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, hah]
    calc h * ‖(c1 + c2 + c3) - (h / 2) • G‖ ≤ h * ((T1 + T2 + T3) * h ^ 2) := by gcongr
      _ = _ := by ring
  have n3' : ‖h ^ 2 • (((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q)‖ ≤ 12 * M0 * D * h ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc h ^ 2 * ‖((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q‖ ≤ h ^ 2 * (12 * M0 * D * h) := by gcongr
      _ = _ := by ring
  have hA1 := norm_add_le (P - (1 + h • (c1 + c2 + c3) + h ^ 2 • ((1 / 2 : ℝ) • c1 ^ 2 +
    (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3)) +
      h • ((c1 + c2 + c3) - (h / 2) • G)) (h ^ 2 • (((1 / 2 : ℝ) • c1 ^ 2 + (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3) - (1 / 2 : ℝ) • Q))
  have hA2 := norm_add_le (P - (1 + h • (c1 + c2 + c3) + h ^ 2 • ((1 / 2 : ℝ) • c1 ^ 2 +
    (1 / 2 : ℝ) • c2 ^ 2 + c1 * c2 + (1 / 2 : ℝ) • c3 ^ 2 + (c1 + c2) * c3)))
      (h • ((c1 + c2 + c3) - (h / 2) • G))
  have ex : (K2 + (T1 + T2 + T3) + 12 * M0 * D) * h ^ 3 =
      K2 * h ^ 3 + (T1 + T2 + T3) * h ^ 3 + 12 * M0 * D * h ^ 3 := by ring
  linarith only [s2, n2', n3', hA1, hA2, ex]

/-- A skew-adjoint (`u(N)`-valued) connection has unitary triangle holonomy. -/
theorem triangle_unitary [CompleteSpace R] [StarRing R] [ContinuousStar R] [StarModule ℝ R]
    {A : E → E →L[ℝ] R} (hskew : ∀ y v, star (A y v) = -A y v) (x a b : E) (h : ℝ) :
    triangle A x a b h ∈ unitary R := by
  have sk : ∀ c : R, star c = -c → ∀ t : ℝ, exp (t • c) ∈ unitary R := by
    intro c hc t
    let _ : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ R
    apply exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff, star_smul, hc, star_trivial, smul_neg]
  have l1 : link A x a h ∈ unitary R := sk _ (hskew _ _) h
  have l2 : link A (x + h • a) (b - a) h ∈ unitary R := sk _ (hskew _ _) h
  have l3 : exp (h • -(A (x + (h / 2) • b) b)) ∈ unitary R :=
    sk _ (by rw [star_neg, hskew]) h
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ l1 l2) l3

end Connection
open Matrix

/-- Squared-norm stability of a quartic rescaling: a cubic error in `U − 1 − h²F` gives
an `O(h)` error in `‖U − 1‖²/h⁴`. -/
theorem quartic_close {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {U1 F : G} {C h : ℝ}
    (hh : 0 < h) (h1 : h ≤ 1) (hC : 0 ≤ C) (hU : ‖U1 - h ^ 2 • F‖ ≤ C * h ^ 3) :
    |‖U1‖ ^ 2 / h ^ 4 - ‖F‖ ^ 2| ≤ C * (2 * ‖F‖ + C) * h := by
  set e := (h ^ 2)⁻¹ • (U1 - h ^ 2 • F)
  have h2 : (0 : ℝ) < h ^ 2 := by positivity
  have he : ‖e‖ ≤ C * h := by
    simp only [e, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h2]
    rw [inv_mul_le_iff₀ h2]
    calc _ ≤ C * h ^ 3 := hU
      _ = h ^ 2 * (C * h) := by ring
  have hU1 : U1 = h ^ 2 • (F + e) := by
    simp only [e, smul_add, smul_smul, mul_inv_cancel₀ h2.ne', one_smul]; abel
  have hn : ‖U1‖ ^ 2 / h ^ 4 = ‖F + e‖ ^ 2 := by
    rw [hU1, norm_smul, Real.norm_eq_abs, abs_of_pos h2]
    field_simp
  rw [hn]
  have t1 := norm_add_le F e
  have t2 : ‖F‖ ≤ ‖F + e‖ + ‖e‖ := by
    have := norm_sub_le (F + e) e; simpa using this
  have hne : 0 ≤ ‖e‖ := norm_nonneg _
  have hCh : C * h ≤ C := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg F, norm_nonneg (F + e)]

section Matrix
variable {N : ℕ}

/-- For a unitary matrix the Wilson term is half the squared Frobenius distance to `1`,
written as an explicit entry sum. -/
theorem wilson_sum (P : Matrix (Fin N) (Fin N) ℂ) (hP : star P * P = 1) :
    ∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2 = 2 * (trace (1 - P)).re := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  have hcol : ∀ j, ∑ i, Complex.normSq (P i j) = 1 := by
    intro j
    have := congrFun (congrFun hP j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    have h2 : ((∑ i, Complex.normSq (P i j) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast
      exact Finset.sum_congr rfl fun i _ => by
        simp [Complex.normSq_eq_conj_mul_self, Matrix.star_apply]
    exact_mod_cast h2
  have hentry : ∀ i j, Complex.normSq ((P - 1) i j) =
      Complex.normSq (P i j) + (if i = j then 1 - 2 * (P i j).re else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.one_apply_eq, Complex.normSq_apply]; ring
    · simp [Matrix.one_apply_ne hij, hij]
  simp_rw [hentry, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => Complex.normSq (P i j))]
  simp only [hcol, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [Matrix.trace, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

open scoped Matrix.Norms.L2Operator

/-- Matrix entries are bounded by the `L²` operator norm. -/
lemma entry_le (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ‖M i j‖ ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin N) ℂ).symm
    (M *ᵥ (EuclideanSpace.single j (1 : ℂ)))) i
  convert this using 2
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Wilson term of one triangle.**  For a `u(N)`-valued `C^{1,1}` connection the triangle
Wilson term satisfies `Re tr(1 − P_h)/h⁴ = Σ |F(a,b)_{ij}|²/8 + O(h)`. -/
theorem triangle_wilson {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : E → E →L[ℝ] (E →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : E} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (a b : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (1 - triangle A x a b h)).re / h ^ 4 -
        (∑ i, ∑ j, ‖curvature A DA x a b i j‖ ^ 2) / 8| ≤ C * h := by
  obtain ⟨C0, hC0, hb⟩ := triangle_expand hA hL0 hL a b
  set F := curvature A DA x a b
  set F' : Matrix (Fin N) (Fin N) ℂ := (1 / 2 : ℝ) • F
  refine ⟨(N : ℝ) ^ 2 * (C0 * (2 * ‖F'‖ + C0)) / 2, by positivity, ?_⟩
  intro h hh h1
  set P := triangle A x a b h
  have hU : star P * P = 1 := (Unitary.mem_iff.mp (triangle_unitary hskew x a b h)).1
  have hw := wilson_sum P hU
  have hM : ‖(P - 1) - h ^ 2 • F'‖ ≤ C0 * h ^ 3 := by
    have : (P - 1) - h ^ 2 • F' = P - (1 + (h ^ 2 / 2) • F) := by
      simp only [F', smul_smul]; ring_nf; abel
    rw [this]; exact hb h hh.le h1
  have hent : ∀ i j, |‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F' i j‖ ^ 2| ≤ C0 * (2 * ‖F'‖ + C0) * h := by
    intro i j
    have he : ‖(P - 1) i j - h ^ 2 • F' i j‖ ≤ C0 * h ^ 3 := by
      have := entry_le ((P - 1) - h ^ 2 • F') i j
      simp only [Matrix.sub_apply, Matrix.smul_apply] at this
      exact this.trans hM
    have q := quartic_close hh h1 hC0 he
    refine q.trans ?_
    gcongr
    exact entry_le F' i j
  have hF : ∑ i, ∑ j, ‖F i j‖ ^ 2 = 4 * ∑ i, ∑ j, ‖F' i j‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [F', Matrix.smul_apply, norm_smul]; norm_num; ring
  have hre : (trace (1 - P)).re = (∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2) / 2 := by linarith
  rw [hre, hF]
  have key : (∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2) / 2 / h ^ 4 - 4 * (∑ i, ∑ j, ‖F' i j‖ ^ 2) / 8 =
      (∑ i, ∑ j, (‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F' i j‖ ^ 2)) / 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]; ring
  rw [key, abs_div, abs_two]
  have hs : |∑ i, ∑ j, (‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F' i j‖ ^ 2)| ≤
      (N : ℝ) ^ 2 * (C0 * (2 * ‖F'‖ + C0) * h) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j).trans ?_
    simp [Finset.sum_const, Finset.card_univ]; ring_nf; rfl
  have : (N : ℝ) ^ 2 * (C0 * (2 * ‖F'‖ + C0)) / 2 * h =
      (N : ℝ) ^ 2 * (C0 * (2 * ‖F'‖ + C0) * h) / 2 := by ring
  rw [this]
  exact div_le_div_of_nonneg_right hs (by norm_num)

end Matrix
section D4
variable {N : ℕ}
open scoped Matrix.Norms.L2Operator

/-- Real coordinates of a D₄ box vector. -/
def rv (k : Fin 4 → Fin 3) : Fin 4 → ℝ := fun i => (D4Gauge.vec k i : ℝ)

/-- Coordinate basis vector. -/
def basis (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1

lemma vec_expand (a : Fin 4 → ℝ) : a = ∑ μ, a μ • basis μ := by
  ext i; simp [basis, Pi.single_apply]

lemma bilinear_expand {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (B : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] R) (a b : Fin 4 → ℝ) :
    B a b = ∑ μ, ∑ ν, (a μ * b ν) • B (basis μ) (basis ν) := by
  conv_lhs => rw [vec_expand a, vec_expand b]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring_nf

/-- Field-strength components `F_{μν}` at `x`. -/
def fieldStrength {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] R)
    (DA : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] R)) (x : Fin 4 → ℝ)
    (μ ν : Fin 4) : R :=
  curvature A DA x (basis μ) (basis ν)

lemma curvature_expand {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] R)
    (DA : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] R)) (x a b : Fin 4 → ℝ) :
    curvature A DA x a b = ∑ μ, ∑ ν, (a μ * b ν) • fieldStrength A DA x μ ν := by
  set M := ContinuousLinearMap.mul ℝ R
  have p1 := bilinear_expand (DA x) a b
  have p2 := bilinear_expand (DA x).flip a b
  have p3 := bilinear_expand (M.bilinearComp (A x) (A x)) a b
  have p4 := bilinear_expand (M.bilinearComp (A x) (A x)).flip a b
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearComp_apply, M,
    ContinuousLinearMap.mul_apply'] at p1 p2 p3 p4
  simp only [curvature, fieldStrength, p1, p2, p3, p4, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma fieldStrength_antisymm {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] R)
    (DA : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] R)) (x : Fin 4 → ℝ)
    (μ ν : Fin 4) : fieldStrength A DA x μ ν = -fieldStrength A DA x ν μ := by
  simp only [fieldStrength, curvature]; abel

/-- Entrywise D₄ flux sum for a complex antisymmetric tensor. -/
lemma tri_entry_sum (f : Fin 4 → Fin 4 → ℂ) (hf : ∀ μ ν, f μ ν = -f ν μ) :
    ∑ p ∈ D4Gauge.tri, ‖∑ μ, ∑ ν, ((rv p.1 μ * rv p.2 ν : ℝ) : ℂ) * f μ ν‖ ^ 2 =
      48 * ∑ μ, ∑ ν, ‖f μ ν‖ ^ 2 := by
  have hre := D4Gauge.flux_sum (fun μ ν => (f μ ν).re) (fun μ ν => by simp [hf μ ν])
  have him := D4Gauge.flux_sum (fun μ ν => (f μ ν).im) (fun μ ν => by simp [hf μ ν])
  have half : ∀ p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3),
      ∑ μ, ∑ ν, ((rv p.1 μ * rv p.2 ν : ℝ) : ℂ) * f μ ν =
        ((1 / 2 : ℝ) : ℂ) * ∑ μ, ∑ ν, ((D4Gauge.area p μ ν : ℝ) : ℂ) * f μ ν := by
    intro p
    have hswap : ∑ μ, ∑ ν, ((rv p.1 ν * rv p.2 μ : ℝ) : ℂ) * f μ ν =
        -∑ μ, ∑ ν, ((rv p.1 μ * rv p.2 ν : ℝ) : ℂ) * f μ ν := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hf ν μ]; ring
    have harea : ∀ μ ν, ((D4Gauge.area p μ ν : ℝ) : ℂ) =
        ((rv p.1 μ * rv p.2 ν : ℝ) : ℂ) - ((rv p.1 ν * rv p.2 μ : ℝ) : ℂ) := by
      intro μ ν; simp [D4Gauge.area, rv]
    simp only [harea, sub_mul, Finset.sum_sub_distrib, hswap]
    push_cast; ring
  have hnorm : ∀ p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3),
      ‖∑ μ, ∑ ν, ((rv p.1 μ * rv p.2 ν : ℝ) : ℂ) * f μ ν‖ ^ 2 =
        ((∑ μ, ∑ ν, (f μ ν).re * D4Gauge.area p μ ν) ^ 2 +
          (∑ μ, ∑ ν, (f μ ν).im * D4Gauge.area p μ ν) ^ 2) / 4 := by
    intro p
    rw [half p, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    have hr : (∑ μ, ∑ ν, ((D4Gauge.area p μ ν : ℝ) : ℂ) * f μ ν).re =
        ∑ μ, ∑ ν, (f μ ν).re * D4Gauge.area p μ ν := by
      simp only [Complex.re_sum, Complex.re_ofReal_mul]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => mul_comm _ _
    have hi : (∑ μ, ∑ ν, ((D4Gauge.area p μ ν : ℝ) : ℂ) * f μ ν).im =
        ∑ μ, ∑ ν, (f μ ν).im * D4Gauge.area p μ ν := by
      simp only [Complex.im_sum, Complex.im_ofReal_mul]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => mul_comm _ _
    rw [hr, hi]; ring
  simp only [hnorm, ← Finset.sum_div, Finset.sum_add_distrib, hre, him]
  have : ∀ μ ν, ‖f μ ν‖ ^ 2 = (f μ ν).re ^ 2 + (f μ ν).im ^ 2 := fun μ ν => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp only [this, Finset.sum_add_distrib]
  ring

/-- Per-site D₄ triangle Wilson density at spacing `h` (sixfold triangle count and cell
volume two give the `β/12` prefactor used in `GaugeContinuum.density`). -/
def d4Density (A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (x : Fin 4 → ℝ) (β h : ℝ) : ℝ :=
  (β / 12) * ∑ p ∈ D4Gauge.tri, (trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4

/-- **Varying non-Abelian D₄ continuum limit.**  For a `u(N)`-valued `C^{1,1}` connection,
the actual D₄ minimal-triangle Wilson density converges, with an `O(h)` error, to the
Yang–Mills density `(β/2) Σ_{μν} Σ_{ij} |F_{μν,ij}|²` built from
`F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`. -/
theorem d4_yang_mills {A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ)}
    {x : Fin 4 → ℝ} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |d4Density A x β h -
        (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2| ≤ C * h := by
  have hc := fun p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3) =>
    triangle_wilson hA hL0 hL hskew (rv p.1) (rv p.2)
  choose C hC0 hCb using hc
  refine ⟨|β| / 12 * ∑ p ∈ D4Gauge.tri, C p,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => hC0 p), ?_⟩
  intro h hh h1
  have hentry : ∀ (a b : Fin 4 → ℝ) (i j : Fin N), curvature A DA x a b i j =
      ∑ μ, ∑ ν, ((a μ * b ν : ℝ) : ℂ) * fieldStrength A DA x μ ν i j := by
    intro a b i j
    rw [curvature_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  have hentry_sum : ∀ i j : Fin N, ∑ p ∈ D4Gauge.tri,
      ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2 =
      48 * ∑ μ, ∑ ν, ‖fieldStrength A DA x μ ν i j‖ ^ 2 := by
    intro i j
    simp only [hentry]
    exact tri_entry_sum (fun μ ν => fieldStrength A DA x μ ν i j) (fun μ ν => by
      show fieldStrength A DA x μ ν i j = -fieldStrength A DA x ν μ i j
      rw [fieldStrength_antisymm]; rfl)
  have htarget : ∑ p ∈ D4Gauge.tri, ∑ i, ∑ j,
      ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2 =
      48 * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2 := by
    calc _ = ∑ i : Fin N, ∑ j : Fin N, ∑ p ∈ D4Gauge.tri,
          ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin N, ∑ j : Fin N, 48 * ∑ μ, ∑ ν, ‖fieldStrength A DA x μ ν i j‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hentry_sum i j
      _ = 48 * ∑ i : Fin N, ∑ j : Fin N, ∑ μ, ∑ ν, ‖fieldStrength A DA x μ ν i j‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ = _ := by
          congr 1
          calc _ = ∑ i : Fin N, ∑ μ, ∑ j : Fin N, ∑ ν, ‖fieldStrength A DA x μ ν i j‖ ^ 2 :=
                Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ i : Fin N, ∑ μ, ∑ ν, ∑ j : Fin N, ‖fieldStrength A DA x μ ν i j‖ ^ 2 :=
                Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
            _ = ∑ μ, ∑ i : Fin N, ∑ ν, ∑ j : Fin N, ‖fieldStrength A DA x μ ν i j‖ ^ 2 :=
                Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
  have key : d4Density A x β h -
      (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2 =
      (β / 12) * ∑ p ∈ D4Gauge.tri,
        ((trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4 -
          (∑ i, ∑ j, ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2) / 8) := by
    have hs : ∑ p ∈ D4Gauge.tri, (∑ i, ∑ j, ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2) / 8 =
        (∑ p ∈ D4Gauge.tri, ∑ i, ∑ j, ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2) / 8 :=
      (Finset.sum_div _ _ _).symm
    rw [Finset.sum_sub_distrib, hs, htarget, d4Density]
    ring
  rw [key, abs_mul]
  have hb : |∑ p ∈ D4Gauge.tri,
      ((trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        (∑ i, ∑ j, ‖curvature A DA x (rv p.1) (rv p.2) i j‖ ^ 2) / 8)| ≤
      ∑ p ∈ D4Gauge.tri, C p * h :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hCb p h hh h1)
  rw [← Finset.sum_mul] at hb
  have h12 : |β / 12| = |β| / 12 := by rw [abs_div]; norm_num
  rw [h12]
  calc |β| / 12 * |_| ≤ |β| / 12 * ((∑ p ∈ D4Gauge.tri, C p) * h) := by gcongr
    _ = _ := by ring

/-- Controlled-limit form. -/
theorem d4_yang_mills_tendsto {A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ)}
    {x : Fin 4 → ℝ} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    Filter.Tendsto (fun h => d4Density A x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := d4_yang_mills hA hL0 hL hskew β
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε / (C + 1)), by positivity, fun h hh hd => ?_⟩
  have hpos : 0 < h := hh
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos] at hd
  rw [Real.dist_eq]
  have h1 : h ≤ 1 := (hd.trans_le (min_le_left _ _)).le
  have h2 : h < ε / (C + 1) := hd.trans_le (min_le_right _ _)
  calc _ ≤ C * h := hb h hpos h1
    _ ≤ (C + 1) * h := by nlinarith
    _ < (C + 1) * (ε / (C + 1)) := by gcongr
    _ = ε := by field_simp

end D4
end PMAction.VaryingFields
