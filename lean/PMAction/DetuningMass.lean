import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Fermion mass from detuning the inter-sector link

In the two-sector domain wall, detuning the on-site mass away from the Wilson point by `δ`
adds `δβ` on both sectors. With `P± = (1 ± Γ)/2` the hops are `h = −β P₊` and `h̄ = −β P₋`.

* `hop_products`: `h h̄ = P₋`, `h̄ h = P₊` and `β h + h β = −1`, from `β² = Γ² = 1` and
  `βΓ = −Γβ` alone. Hence the squared Hamiltonian splits into two-by-two blocks
  `[[δ², −δ], [−δ, δ² + 1]]` acting on the chirality components.
* `light_mass`: the candidate light-mass root is `m = √(δ² + 1/4) − 1/2`. Equivalently
  `m (m + 1) = δ²` (`mass_relation`), and `m²` is the small root of the block
  (`mass_squared_root`). Connecting this block and its multiplicities to the full
  momentum-dependent Hamiltonian is a separate spectral obligation.
* `mass_le`: `0 ≤ m ≤ δ²`. The mass is quadratic in the detuning: a link detuned by `δ`
  gives a fermion lighter than `δ` by a factor of about `δ`.
* `twin_gap`: the corner twins are the same formula at detuning `2n`, so every twin has mass
  above `1.56`.
-/

namespace PMAction.DetuningMass

section Algebra
variable {𝕜 A : Type*} [Field 𝕜] [CharZero 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The hop products depend only on the Clifford relations. -/
theorem hop_products_over (β Γ : A) (hβ : β * β = 1) (hΓ : Γ * Γ = 1) (hac : β * Γ = -(Γ * β)) :
    let Pp : A := (1/2 : 𝕜) • (1 + Γ)
    let Pm : A := (1/2 : 𝕜) • (1 - Γ)
    let h : A := -(β * Pp)
    let hb : A := -(β * Pm)
    h * hb = Pm ∧ hb * h = Pp ∧ β * h + h * β = -1 := by
  intro Pp Pm h hb
  have hPpβ : Pp * β = β * Pm := by
    simp only [Pp, Pm, smul_mul_assoc, mul_smul_comm, add_mul, mul_sub,
      one_mul, mul_one]
    rw [show Γ * β = -(β * Γ) by rw [hac]; abel]
    abel_nf
  have hPmβ : Pm * β = β * Pp := by
    simp only [Pp, Pm, smul_mul_assoc, mul_smul_comm, sub_mul, mul_add,
      one_mul, mul_one]
    rw [show Γ * β = -(β * Γ) by rw [hac]; abel]
    abel_nf
  have hPp2 : Pp * Pp = Pp := by
    simp only [Pp, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hΓ]
    rw [show (1 + Γ + (Γ + 1) : A) = (2 : 𝕜) • (1 + Γ) by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hPm2 : Pm * Pm = Pm := by
    simp only [Pm, smul_mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hΓ]
    rw [show (1 - Γ - (Γ - 1) : A) = (2 : 𝕜) • (1 - Γ) by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hsum : Pp + Pm = 1 := by
    simp only [Pp, Pm, ← smul_add]
    rw [show (1 + Γ + (1 - Γ) : A) = (2 : 𝕜) • 1 by rw [two_smul]; abel, smul_smul]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [h, hb, neg_mul_neg]
    rw [mul_assoc, ← mul_assoc Pp, hPpβ, mul_assoc, hPm2, ← mul_assoc, hβ, one_mul]
  · simp only [h, hb, neg_mul_neg]
    rw [mul_assoc, ← mul_assoc Pm, hPmβ, mul_assoc, hPp2, ← mul_assoc, hβ, one_mul]
  · simp only [h, neg_mul, mul_neg]
    rw [← mul_assoc, hβ, one_mul, mul_assoc, hPpβ, ← mul_assoc, hβ, one_mul, ← neg_add, hsum]

end Algebra

/-- The original rational-algebra interface is retained. -/
theorem hop_products {A : Type*} [Ring A] [Algebra ℚ A]
    (β Γ : A) (hβ : β*β = 1) (hΓ : Γ*Γ = 1) (hac : β*Γ = -(Γ*β)) :
    let Pp : A := (1/2 : ℚ) • (1+Γ)
    let Pm : A := (1/2 : ℚ) • (1-Γ)
    let h : A := -(β*Pp)
    let hb : A := -(β*Pm)
    h*hb = Pm ∧ hb*h = Pp ∧ β*h+h*β = -1 :=
  hop_products_over (𝕜 := ℚ) β Γ hβ hΓ hac


/-- The light mass as a function of the detuning. -/
noncomputable def lightMass (δ : ℝ) : ℝ := Real.sqrt (δ^2 + 1/4) - 1/2

theorem mass_relation (δ : ℝ) : lightMass δ * (lightMass δ + 1) = δ^2 := by
  unfold lightMass
  have h := Real.sq_sqrt (show (0:ℝ) ≤ δ^2 + 1/4 by positivity)
  nlinarith [h]

/-- `m²` is the smaller eigenvalue of `[[δ², −δ], [−δ, δ² + 1]]`. -/
theorem mass_squared_root (δ : ℝ) :
    let m := lightMass δ
    (m^2 - δ^2) * (m^2 - δ^2 - 1) = δ^2 := by
  intro m
  have hr := mass_relation δ
  have : m^2 - δ^2 = -m := by simp only [m] at hr ⊢; nlinarith [hr]
  rw [this]; nlinarith [hr]

theorem mass_le (δ : ℝ) : 0 ≤ lightMass δ ∧ lightMass δ ≤ δ^2 := by
  have hs := Real.sqrt_nonneg (δ^2 + 1/4)
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ δ^2 + 1/4 by positivity)
  have h0 : 0 ≤ lightMass δ := by
    unfold lightMass
    have : (1/2 : ℝ) ≤ Real.sqrt (δ^2 + 1/4) := by
      rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
        rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
    linarith
  refine ⟨h0, ?_⟩
  have hr := mass_relation δ
  nlinarith [hr, h0]

theorem light_mass_zero : lightMass 0 = 0 := by
  unfold lightMass; simp
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-- Twins are maximally detuned modes. At a corner of the momentum cell with `n` components
equal to `π` the momentum term vanishes and the Wilson term acts as a detuning `2n` (at
`r = 1`), so the lightest mode there has mass `lightMass (2n)`. For `n ≥ 1` this exceeds
`1.56`, matching the numerical corner gaps (1.562, 3.531, 5.521). -/
theorem twin_gap {n : ℕ} (hn : 1 ≤ n) : (1.56 : ℝ) < lightMass (2 * n) := by
  unfold lightMass
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (2.06 : ℝ) < Real.sqrt ((2 * n)^2 + 1/4) := by
    rw [show (2.06 : ℝ) = Real.sqrt (2.06^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    nlinarith
  linarith

end PMAction.DetuningMass
