import PMAction.FluctuationClosure
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

noncomputable section
namespace PMAction.LandauDegeneracy
open Complex

/-! ## 1. Landau gauge: each `y`-momentum is a shifted oscillator -/

/-- The kinetic momentum `π_y = −i∂_y − b x` on functions of `(x, y)`. -/
def piY (b : ℝ) (φ : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -I * deriv (fun y' => φ x y') y - ((b * x : ℝ) : ℂ) * φ x y

/-- The Landau Hamiltonian `π_x² + π_y²` in Landau gauge, with `π_x = −i∂_x`. -/
def landauH (b : ℝ) (ψ : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -deriv (deriv fun x' => ψ x' y) x + piY b (piY b ψ) x y

/-- A plane wave in `y` with profile `f` in `x`. -/
def wave (k : ℝ) (f : ℝ → ℂ) (x y : ℝ) : ℂ := exp (I * k * y) * f x

lemma hasDerivAt_phase (k y : ℝ) :
    HasDerivAt (fun y : ℝ => exp (I * k * y)) (exp (I * k * y) * (I * k)) y := by
  have h := (((hasDerivAt_id y).ofReal_comp).const_mul (I * k)).cexp
  convert h using 1
  · rfl
  change cexp (I * k * y) * (I * k) = cexp (I * k * y) * (I * k * ((1 : ℝ) : ℂ))
  rw [Complex.ofReal_one, mul_one]

lemma piY_wave (b k : ℝ) (f : ℝ → ℂ) :
    piY b (wave k f) = wave k (fun x => ((k - b * x : ℝ) : ℂ) * f x) := by
  funext x y
  simp only [piY, wave]
  rw [((hasDerivAt_phase k y).mul_const (f x)).deriv]
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- **Landau-gauge reduction.** On `e^{iky} f(x)` the Hamiltonian acts as
`e^{iky}(−f'' + (k − b x)² f)`: a harmonic oscillator `−d² + b²(x − x₀)²` centred at
`x₀ = k/b`. -/
theorem landau_gauge (b k : ℝ) (f : ℝ → ℂ) (x y : ℝ) :
    landauH b (wave k f) x y =
      exp (I * k * y) * (-deriv (deriv f) x + ((k - b * x : ℝ) : ℂ) ^ 2 * f x) := by
  simp only [landauH, piY_wave]
  have hx : (deriv fun x' => wave k f x' y) = fun x' => exp (I * k * y) * deriv f x' := by
    show (deriv fun x' => exp (I * k * y) * f x') = _
    exact deriv_const_mul_field' _
  have hxx : deriv (fun x' => exp (I * k * y) * deriv f x') x =
      exp (I * k * y) * deriv (deriv f) x := congrFun (deriv_const_mul_field' _) x
  rw [hx, hxx]
  simp only [wave]
  ring

/-- With `b ≠ 0`, the potential is `b²(x − k/b)²`: the orbit centre is `k/b`. -/
theorem centre (b k x : ℝ) (hb : b ≠ 0) : (k - b * x) ^ 2 = b ^ 2 * (x - k / b) ^ 2 := by
  field_simp; ring

/-! ## 2. Periodicity quantizes the momentum -/

/-- **Momentum quantization.** On a strip of circumference `L`, the phase `e^{iky}` is periodic
exactly when `kL = 2πm` for some integer `m`. -/
theorem periodic_iff (k L : ℝ) :
    (∀ y : ℝ, exp (I * k * (y + L : ℝ)) = exp (I * k * y)) ↔
      ∃ m : ℤ, k * L = 2 * Real.pi * m := by
  constructor
  · intro h
    have h0 := h 0
    simp only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h0
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h0
    refine ⟨m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    linarith
  · rintro ⟨m, hm⟩ y
    have e : I * k * ((y + L : ℝ) : ℂ) = I * k * y + m * (2 * Real.pi * I) := by
      push_cast
      have : ((k * L : ℝ) : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by rw [hm]
      push_cast at this
      linear_combination I * this
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## 3. Counting orbit centres -/

/-- The allowed momenta `k = 2πm/L` whose centres `k/b` lie in `[0, W)`. -/
def centres (b L W : ℝ) : Set ℤ := {m | 0 ≤ 2 * Real.pi * m / L / b ∧ 2 * Real.pi * m / L / b < W}

theorem centres_eq {b L W : ℝ} (hb : 0 < b) (hL : 0 < L) :
    centres b L W = ↑(Finset.Ico (0 : ℤ) ⌈b * W * L / (2 * Real.pi)⌉) := by
  ext m
  change (0 ≤ 2 * Real.pi * m / L / b ∧ 2 * Real.pi * m / L / b < W) ↔
    m ∈ (↑(Finset.Ico (0 : ℤ) ⌈b * W * L / (2 * Real.pi)⌉) : Set ℤ)
  rw [Finset.coe_Ico, Set.mem_Ico, Int.lt_ceil]
  have hpi := Real.pi_pos
  set c := 2 * Real.pi / (L * b) with hcdef
  have hc : 0 < c := by positivity
  have e : 2 * Real.pi * m / L / b = c * m := by rw [hcdef]; field_simp
  have hWc : b * W * L / (2 * Real.pi) = W / c := by rw [hcdef]; field_simp
  rw [e, hWc, mul_nonneg_iff_of_pos_left hc, lt_div_iff₀' hc]
  exact ⟨fun h => ⟨by exact_mod_cast h.1, h.2⟩, fun h => ⟨by exact_mod_cast h.1, h.2⟩⟩

/-- The number of states per Landau level on a `W × L` strip is `⌈bWL/2π⌉`. -/
theorem centre_count {b L W : ℝ} (hb : 0 < b) (hL : 0 < L) (hW : 0 < W) :
    ((Finset.Ico (0 : ℤ) ⌈b * W * L / (2 * Real.pi)⌉).card : ℝ) =
      (⌈b * W * L / (2 * Real.pi)⌉ : ℝ) := by
  rw [Int.card_Ico, sub_zero]
  have : 0 ≤ ⌈b * W * L / (2 * Real.pi)⌉ := Int.ceil_nonneg (by positivity)
  have h := Int.toNat_of_nonneg this
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h

/-- **One state per flux quantum.** The density of states per level differs from `b/2π` by
less than one state per strip area: `|N/(WL) − b/2π| < 1/(WL)`. -/
theorem density_bound {b L W : ℝ} (hb : 0 < b) (hL : 0 < L) (hW : 0 < W) :
    |(⌈b * W * L / (2 * Real.pi)⌉ : ℝ) / (W * L) - b / (2 * Real.pi)| < 1 / (W * L) := by
  set c := b * W * L / (2 * Real.pi)
  have h1 : c ≤ (⌈c⌉ : ℝ) := Int.le_ceil c
  have h2 : (⌈c⌉ : ℝ) < c + 1 := Int.ceil_lt_add_one c
  have hA : 0 < W * L := by positivity
  have e : b / (2 * Real.pi) = c / (W * L) := by
    simp only [c]; field_simp
  rw [e, ← sub_div, abs_div, abs_of_pos hA, div_lt_div_iff_of_pos_right hA, abs_lt]
  constructor <;> linarith

/-- **The density is `b/2π`** in the large-strip limit (`W → ∞` at fixed `L`). -/
theorem density_limit {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    Filter.Tendsto (fun W : ℝ => (⌈b * W * L / (2 * Real.pi)⌉ : ℝ) / (W * L)) Filter.atTop
      (nhds (b / (2 * Real.pi))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (1 / (ε * L) + 1), fun W hW => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : 1 / (ε * L) + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWp : 0 < W := by linarith
  rw [Real.dist_eq]
  refine lt_of_lt_of_le (density_bound hb hL hWp) ?_
  rw [div_le_iff₀ (by positivity)]
  have : 1 / (ε * L) < W := by linarith
  rw [div_lt_iff₀ (by positivity)] at this
  nlinarith

/-! ## 4. The degeneracy closes the earlier hypotheses -/

/-- The derived density `ρ(b) = b/2π`. -/
def rho (b : ℝ) : ℝ := b / (2 * Real.pi)

/-- The dilation-scaling hypothesis of `FluctuationClosure.density_linear` holds. -/
theorem rho_scaling (lam b : ℝ) : rho (lam * b) = lam * rho b := by
  simp only [rho]; ring

lemma sinh_ratio :
    Filter.Tendsto (fun x : ℝ => x / Real.sinh x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  obtain ⟨C, hC, h⟩ := FluctuationPremises.weak_field_normalization
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

/-- The weak-field matching hypothesis of `FluctuationClosure.density_coefficient` holds for
the derived coefficient `ρ(1) = 1/2π`. -/
theorem weak_field_match :
    Filter.Tendsto (fun x : ℝ => 2 * Real.pi * rho 1 * (x / Real.sinh x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have : 2 * Real.pi * rho 1 = 1 := by simp only [rho]; field_simp
  simp only [this, one_mul]
  exact sinh_ratio

/-- Both hypotheses of `FluctuationClosure` now hold. `density_linear` (with `rho_scaling`) gives
linearity, and `density_coefficient` (with `weak_field_match`) gives `ρ(1) = 1/2π`. -/
theorem closure_hypotheses_hold {b : ℝ} (hb : 0 < b) :
    rho b = rho 1 * b ∧ rho 1 = 1 / (2 * Real.pi) :=
  ⟨FluctuationClosure.density_linear rho (fun lam b _ _ => rho_scaling lam b) hb,
    FluctuationClosure.density_coefficient (rho 1) weak_field_match⟩

/-- **The Landau kernel per area.** With density `b/2π` and levels `(2n+1)b`, the heat kernel
per unit area is `(b/2π)/(2 sinh bt)`. Relative to the free kernel `1/(4πt)` it is
`x/sinh x` with `x = bt`. That is the per-component factor of `RunningResponse.pair_kernel`. -/
theorem kernel_per_area {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    HasSum (fun n : ℕ => rho b * Real.exp (-((2 * n + 1) * (b * t))))
        (rho b * (1 / (2 * Real.sinh (b * t)))) ∧
      rho b * (1 / (2 * Real.sinh (b * t))) / (1 / (4 * Real.pi * t)) =
        (b * t) / Real.sinh (b * t) := by
  refine ⟨(RunningResponse.landau_sum (by positivity)).mul_left (rho b), ?_⟩
  have hs : 0 < Real.sinh (b * t) := Real.sinh_pos_iff.mpr (by positivity)
  simp only [rho]
  field_simp
  ring

end PMAction.LandauDegeneracy
