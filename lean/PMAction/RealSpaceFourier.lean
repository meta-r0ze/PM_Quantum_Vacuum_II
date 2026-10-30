import PMAction.GlobalTickInterval
import PMAction.SplitSymbol

/-!
# Real-space Fourier identification of the split update

On the periodic lattice `(Fin 3 → Fin (n+1)) × Sites`, the actual real-space split update
`VacuumSplit.update (n+1) τ` is identified with the momentum-space update
`VacuumSplit.momentumUpdate k τ` at the lattice momenta `k = 2π c/(n+1)`:

* `update_acts`: a plane wave `χ_c ⊗ v` is mapped to `χ_c ⊗ (momentumUpdate (2πc/(n+1)) τ v)`.
* `chi_orth`, `inversion`: the plane waves with centred labels are orthogonal and complete.
* `hat_update`: every discrete Fourier coefficient evolves by its momentum block.
* `eigen_iff`: the real-space spectrum is the union of the momentum-block spectra.
* `real_fixed_iff`: with one tick bound `δ` uniform in the torus size, for `0 < |τ| < δ` the
  fixed fields are exactly the spatially constant fields whose internal vector lies in
  `ker VacuumSplit.wall`.

No continuum limit, tick selection or species identification is inferred.
-/

noncomputable section
namespace PMAction.RealSpaceFourier
open Matrix ConcreteFermion Complex
open scoped Kronecker

variable (n : ℕ)

/-- `e^{2π i c y/(n+1)}` on the cyclic chain `Fin (n+1)`. -/
def phase (c : ℤ) (y : Fin (n + 1)) : ℂ :=
  exp (((2 * Real.pi * c * (y : ℕ) / (n + 1) : ℝ) : ℂ) * I)

/-- The lattice momentum `2π c/(n+1)`. -/
def kOf (c : ℤ) : ℝ := 2 * Real.pi * c / (n + 1)

/-- **A shift multiplies a plane wave by its phase.** -/
theorem phase_shift (c : ℤ) (y : Fin (n + 1)) :
    phase n c (finRotate (n + 1) y) = exp ((kOf n c : ℂ) * I) * phase n c y := by
  unfold phase kOf
  rw [← exp_add]
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, exp_zero,
      Fin.val_last]
    symm
    have : ((2 * Real.pi * c / (n + 1) : ℝ) : ℂ) * I + ((2 * Real.pi * c * (n : ℕ) / (n + 1) : ℝ) : ℂ) * I
        = (c : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp; ring
    rw [this, exp_int_mul_two_pi_mul_I]
  · congr 1
    push_cast; field_simp; ring

theorem phase_succ (c : ℤ) (y : Fin (n + 1)) :
    phase n c (y + 1) = exp ((kOf n c : ℂ) * I) * phase n c y := by
  rw [← finRotate_apply]; exact phase_shift n c y

/-- The lattice. -/
abbrev Lat := Fin 3 → Fin (n + 1)

/-- Plane wave with integer wave numbers `c`. -/
def chi (c : Fin 3 → ℤ) (x : Lat n) : ℂ := ∏ j, phase n (c j) (x j)

/-- The momentum of `c`. -/
def kvec (c : Fin 3 → ℤ) : Fin 3 → ℝ := fun j => kOf n (c j)

lemma exp_kOf (c : ℤ) : exp ((kOf n c : ℂ) * I) = (Real.cos (kOf n c) : ℂ) + I * (Real.sin (kOf n c) : ℂ) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]; ring

theorem chi_shift (c : Fin 3 → ℤ) (j : Fin 3) (x : Lat n) :
    chi n c (SplitUpdate.axisShift (n + 1) j x) = exp ((kOf n (c j) : ℂ) * I) * chi n c x := by
  unfold chi
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  fin_cases j <;>
    simp [SplitUpdate.axisShift, phase_succ] <;> ring

theorem chi_unshift (c : Fin 3 → ℤ) (j : Fin 3) (x : Lat n) :
    chi n c ((SplitUpdate.axisShift (n + 1) j)⁻¹ x) =
      exp (-(kOf n (c j) : ℂ) * I) * chi n c x := by
  have h := chi_shift n c j ((SplitUpdate.axisShift (n + 1) j)⁻¹ x)
  rw [show (SplitUpdate.axisShift (n + 1) j) ((SplitUpdate.axisShift (n + 1) j)⁻¹ x) = x by simp] at h
  rw [h, ← mul_assoc, ← exp_add]; simp

/-- Plane wave times an internal vector. -/
def pw (c : Fin 3 → ℤ) (v : Sites → ℂ) : Lat n × Sites → ℂ := fun p => chi n c p.1 * v p.2

lemma kron_pw {Y : Type*} [Fintype Y] (A : Matrix (Lat n) (Lat n) ℂ) (B : Matrix Sites Y ℂ)
    (f : Lat n → ℂ) (g : Y → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p : Lat n × Y => f p.1 * g p.2) = fun p => (A *ᵥ f) p.1 * (B *ᵥ g) p.2 := by
  funext ⟨x, a⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `A` acts on plane waves of momentum `c` as the internal matrix `M`. -/
def ActsAs (c : Fin 3 → ℤ) (A : Matrix (Lat n × Sites) (Lat n × Sites) ℂ) (M : Matrix Sites Sites ℂ) :
    Prop := ∀ v, A *ᵥ pw n c v = pw n c (M *ᵥ v)

lemma actsAs_mul (c : Fin 3 → ℤ) {A B : Matrix (Lat n × Sites) (Lat n × Sites) ℂ} {M K : Matrix Sites Sites ℂ}
    (hA : ActsAs n c A M) (hB : ActsAs n c B K) : ActsAs n c (A * B) (M * K) := by
  intro v; rw [← mulVec_mulVec, hB, hA, mulVec_mulVec]

lemma actsAs_one (c : Fin 3 → ℤ) : ActsAs n c 1 1 := by intro v; simp

lemma actsAs_add (c : Fin 3 → ℤ) {A B : Matrix (Lat n × Sites) (Lat n × Sites) ℂ} {M K : Matrix Sites Sites ℂ}
    (hA : ActsAs n c A M) (hB : ActsAs n c B K) : ActsAs n c (A + B) (M + K) := by
  intro v; rw [add_mulVec, hA, hB, add_mulVec]; funext p; simp [pw, mul_add]

lemma actsAs_smul (c : Fin 3 → ℤ) (z : ℂ) {A : Matrix (Lat n × Sites) (Lat n × Sites) ℂ}
    {M : Matrix Sites Sites ℂ} (hA : ActsAs n c A M) : ActsAs n c (z • A) (z • M) := by
  intro v; rw [smul_mulVec, hA, smul_mulVec]; funext p; simp [pw]; ring

/-- **The on-site coin acts as itself.** -/
theorem onsite_acts (c : Fin 3 → ℤ) (Q : Matrix Sites Sites ℂ) :
    ActsAs n c (SplitUpdate.onsite Q) Q := by
  intro v
  unfold pw
  rw [SplitUpdate.onsite, kron_pw, one_mulVec]

/-- **A neighbour link acts as its Fourier symbol.** -/
theorem neighbor_acts (c : Fin 3 → ℤ) (j : Fin 3) :
    ActsAs n c (SplitUpdate.neighbor (SplitUpdate.axisShift (n + 1) j) j)
      (WilsonSplit.directionSymbol j (kOf n (c j))) := by
  intro v
  unfold pw
  rw [WilsonSplit.directionSymbol_phase, SplitUpdate.neighbor, add_mulVec, kron_pw, kron_pw,
    permMatrix_mulVec, conjTranspose_permMatrix, permMatrix_mulVec]
  funext ⟨x, a⟩
  simp only [Function.comp, chi_shift, chi_unshift, add_mulVec, smul_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have h1 := exp_kOf n (c j)
  have h2 : exp (-(kOf n (c j) : ℂ) * I) =
      (Real.cos (kOf n (c j)) : ℂ) - I * (Real.sin (kOf n (c j)) : ℂ) := by
    rw [show -(kOf n (c j) : ℂ) * I = ((-kOf n (c j) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]; push_cast; ring
  rw [h1, h2]; ring

/-- **A directional step acts as the rotation of its symbol.** -/
theorem direction_acts (c : Fin 3 → ℤ) (j : Fin 3) (τ : ℝ) :
    ActsAs n c (SplitUpdate.direction (SplitUpdate.axisShift (n + 1) j) j τ)
      (LocalUnitary.rotation (WilsonSplit.directionSymbol j (kOf n (c j))) τ) := by
  unfold SplitUpdate.direction LocalUnitary.rotation
  exact actsAs_add n c (actsAs_smul n c _ (actsAs_one n c))
    (actsAs_smul n c _ (neighbor_acts n c j))

/-- **Real-space Fourier identification.** The real-space split update on the torus
`(Fin (n+1))³` acts on every plane wave as the momentum-space update at `k = 2πc/(n+1)`. -/
theorem update_acts (c : Fin 3 → ℤ) (τ : ℝ) :
    ActsAs n c (VacuumSplit.update (n + 1) τ) (VacuumSplit.momentumUpdate (kvec n c) τ) := by
  unfold VacuumSplit.update SplitUpdate.cubicUpdate SplitUpdate.update VacuumSplit.momentumUpdate
  have h := actsAs_mul n c (onsite_acts n c (VacuumSplit.onsiteCoin τ))
    (actsAs_mul n c (actsAs_mul n c (direction_acts n c 0 τ) (direction_acts n c 1 τ))
      (direction_acts n c 2 τ))
  simpa [kvec, Matrix.mul_assoc] using h

/-! ### Orthogonality -/

/-- Root-of-unity sum: `Σ_{y<n+1} e^{2πi d y/(n+1)} = n+1` if `(n+1) ∣ d`, else `0`. -/
theorem root_sum (d : ℤ) :
    ∑ y : Fin (n + 1), exp (((2 * Real.pi * d * (y : ℕ) / (n + 1) : ℝ) : ℂ) * I) =
      if ((n + 1 : ℕ) : ℤ) ∣ d then (n + 1 : ℂ) else 0 := by
  set ζ := exp (((2 * Real.pi * d / (n + 1) : ℝ) : ℂ) * I) with hζ
  have hterm : ∀ y : Fin (n + 1), exp (((2 * Real.pi * d * (y : ℕ) / (n + 1) : ℝ) : ℂ) * I) =
      ζ ^ (y : ℕ) := by
    intro y; rw [hζ, ← exp_nat_mul]; congr 1; push_cast; ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => ζ ^ i)]
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hpow : ζ ^ (n + 1) = 1 := by
    rw [hζ, ← exp_nat_mul]
    have : ((n + 1 : ℕ) : ℂ) * (((2 * Real.pi * d / (n + 1) : ℝ) : ℂ) * I) = (d : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp
    rw [this, exp_int_mul_two_pi_mul_I]
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    have : ζ = 1 := by
      rw [hζ]
      have : (((2 * Real.pi * d / (n + 1) : ℝ) : ℂ) * I) = (q : ℂ) * (2 * Real.pi * I) := by
        rw [hq]; push_cast; field_simp
      rw [this, exp_int_mul_two_pi_mul_I]
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ, exp_eq_one_iff] at h1
      obtain ⟨q, hq⟩ := h1
      apply h
      refine ⟨q, ?_⟩
      have h2 : ((2 * Real.pi * d / (n + 1) : ℝ) : ℂ) = (q : ℂ) * (2 * Real.pi) := by
        have hI : I ≠ 0 := I_ne_zero
        have := congrArg (· / I) hq
        rw [mul_div_assoc, div_self hI, mul_one] at this
        rw [this]; field_simp
      have h3 : (2 * Real.pi * d / (n + 1) : ℝ) = q * (2 * Real.pi) := by exact_mod_cast h2
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have h4 : (d : ℝ) = ((n + 1 : ℕ) : ℝ) * q := by
        field_simp at h3; push_cast; linarith
      exact_mod_cast h4
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma phase_mul_star (c c' : ℤ) (y : Fin (n + 1)) :
    star (phase n c' y) * phase n c y =
      exp (((2 * Real.pi * (c - c') * (y : ℕ) / (n + 1) : ℝ) : ℂ) * I) := by
  unfold phase
  rw [star_def, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_add]
  congr 1; push_cast; ring

/-- **Plane-wave orthogonality on the torus.** -/
theorem chi_orth (c c' : Fin 3 → ℤ) :
    ∑ x : Lat n, star (chi n c' x) * chi n c x =
      ∏ j, (if ((n + 1 : ℕ) : ℤ) ∣ (c j - c' j) then (n + 1 : ℂ) else 0) := by
  unfold chi
  simp only [star_prod, ← Finset.prod_mul_distrib, phase_mul_star]
  rw [← Fintype.prod_sum (fun j (y : Fin (n + 1)) =>
    exp (((2 * Real.pi * ((c j : ℝ) - (c' j : ℝ)) * ((y : ℕ) : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * I))]
  refine Finset.prod_congr rfl fun j _ => ?_
  have := root_sum n (c j - c' j)
  push_cast at this ⊢
  exact this

/-- Centered wave number in `[−(n+1)/2, (n+1)/2]`. -/
def cen (m : Fin (n + 1)) : ℤ := if 2 * (m : ℕ) ≤ n + 1 then (m : ℤ) else (m : ℤ) - (n + 1)

def cvec (m : Lat n) : Fin 3 → ℤ := fun j => cen n (m j)

lemma cen_dvd_iff (m m' : Fin (n + 1)) : ((n + 1 : ℕ) : ℤ) ∣ (cen n m - cen n m') ↔ m = m' := by
  constructor
  · intro h
    have hm := m.isLt; have hm' := m'.isLt
    have h' : ((n + 1 : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) - ((m' : ℕ) : ℤ) := by
      unfold cen at h
      split_ifs at h <;> push_cast at h ⊢
      · exact h
      · have := dvd_sub h (dvd_refl ((n : ℤ) + 1)); simpa [sub_sub, add_comm] using this
      · have := dvd_add h (dvd_refl ((n : ℤ) + 1)); simpa [sub_add] using this
      · have : ((m : ℤ) - (n + 1) - ((m' : ℤ) - (n + 1))) = (m : ℤ) - m' := by ring
        rwa [this] at h
    obtain ⟨q, hq⟩ := h'
    apply Fin.ext
    have a1 : ((m : ℕ) : ℤ) < n + 1 := by exact_mod_cast hm
    have a2 : ((m' : ℕ) : ℤ) < n + 1 := by exact_mod_cast hm'
    have a3 : (0 : ℤ) ≤ ((m : ℕ) : ℤ) := by positivity
    have a4 : (0 : ℤ) ≤ ((m' : ℕ) : ℤ) := by positivity
    push_cast at hq
    have hq0 : q = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · have : q ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ q := by omega
        nlinarith
    rw [hq0] at hq; omega
  · rintro rfl; simp

lemma cen_bound (m : Fin (n + 1)) : 2 * |cen n m| ≤ n + 1 := by
  have hm := m.isLt
  unfold cen; split_ifs with h
  · rw [abs_of_nonneg (by positivity)]; exact_mod_cast h
  · rw [abs_of_neg (by omega)]; omega

lemma cen_zero_iff (m : Fin (n + 1)) : cen n m = 0 ↔ m = 0 := by
  have hm := m.isLt
  unfold cen; constructor
  · intro h; split_ifs at h with h1
    · apply Fin.ext; simp only [Fin.val_zero]; exact_mod_cast h
    · omega
  · rintro rfl; simp

/-- Fourier coefficient. -/
def hat (ψ : Lat n × Sites → ℂ) (m : Lat n) : Sites → ℂ :=
  fun a => ∑ x, star (chi n (cvec n m) x) * ψ (x, a)

/-- **The coefficient of a plane wave.** -/
theorem hat_pw (m m' : Lat n) (w : Sites → ℂ) :
    hat n (pw n (cvec n m) w) m' = if m = m' then ((n + 1 : ℂ) ^ 3) • w else 0 := by
  funext a
  have h := chi_orth n (cvec n m) (cvec n m')
  simp only [hat, pw]
  simp_rw [← mul_assoc, ← Finset.sum_mul, h, cvec, cen_dvd_iff]
  rw [Fin.prod_univ_three]
  by_cases hmm : m = m'
  · subst hmm
    simp only [↓reduceIte, Pi.smul_apply, smul_eq_mul]
    ring
  · have : ¬ (m 0 = m' 0 ∧ m 1 = m' 1 ∧ m 2 = m' 2) := by
      rintro ⟨h0, h1, h2⟩; apply hmm; funext j; fin_cases j <;> assumption
    simp only [hmm, ↓reduceIte, Pi.zero_apply]
    by_cases h0 : m 0 = m' 0 <;> by_cases h1 : m 1 = m' 1 <;> by_cases h2 : m 2 = m' 2 <;>
      simp_all

lemma dual_phase (m x y : Fin (n + 1)) :
    phase n (cen n m) x * star (phase n (cen n m) y) =
      exp (((2 * Real.pi * (((x : ℕ) : ℤ) - ((y : ℕ) : ℤ) : ℤ) * (m : ℕ) / (n + 1) : ℝ) : ℂ) * I) := by
  unfold phase cen
  rw [star_def, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_add]
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  split_ifs
  · congr 1; push_cast; ring
  · have : (((2 * Real.pi * (((m : ℕ) : ℤ) - (n + 1) : ℤ) * (x : ℕ) / (n + 1) : ℝ) : ℂ) * I +
        (((2 * Real.pi * (((m : ℕ) : ℤ) - (n + 1) : ℤ) * (y : ℕ) / (n + 1) : ℝ) : ℂ) * -I)) =
        (((2 * Real.pi * (((x : ℕ) : ℤ) - ((y : ℕ) : ℤ) : ℤ) * (m : ℕ) / (n + 1) : ℝ) : ℂ) * I) +
          ((-(((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp; ring
    rw [show ((((m : ℕ) : ℤ) - (n + 1) : ℤ) : ℝ) = ((m : ℕ) : ℝ) - (n + 1) by push_cast; ring] at *
    push_cast at this ⊢
    have hz := exp_int_mul_two_pi_mul_I (-(((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)))
    push_cast at hz
    rw [this, exp_add, hz, mul_one]

/-- **Dual orthogonality.** -/
theorem chi_dual (x y : Lat n) :
    ∑ m : Lat n, chi n (cvec n m) x * star (chi n (cvec n m) y) =
      if x = y then (n + 1 : ℂ) ^ 3 else 0 := by
  unfold chi cvec
  simp only [star_prod, ← Finset.prod_mul_distrib, dual_phase]
  rw [← Fintype.prod_sum (fun j (m : Fin (n + 1)) =>
    exp (((2 * Real.pi * (((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ) : ℤ) * (m : ℕ) / (n + 1) : ℝ) : ℂ) * I))]
  have hj : ∀ j, (∑ m : Fin (n + 1),
      exp (((2 * Real.pi * (((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ) : ℤ) * (m : ℕ) / (n + 1) : ℝ) : ℂ) * I)) =
      if x j = y j then (n + 1 : ℂ) else 0 := by
    intro j
    rw [root_sum]
    have hx := (x j).isLt; have hy := (y j).isLt
    congr 1
    apply propext
    constructor
    · rintro ⟨q, hq⟩
      apply Fin.ext
      have a1 : (((x j : ℕ)) : ℤ) < n + 1 := by exact_mod_cast hx
      have a2 : (((y j : ℕ)) : ℤ) < n + 1 := by exact_mod_cast hy
      have a3 : (0 : ℤ) ≤ ((x j : ℕ) : ℤ) := by positivity
      have a4 : (0 : ℤ) ≤ ((y j : ℕ) : ℤ) := by positivity
      push_cast at hq
      have hq0 : q = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hl | hl
        · have : q ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ q := by omega
          nlinarith
      rw [hq0] at hq; omega
    · intro h; rw [h]; simp
  simp only [hj, Fin.prod_univ_three]
  by_cases hxy : x = y
  · subst hxy; simp; ring
  · simp only [hxy, ↓reduceIte]
    have : ¬ (x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2) := by
      rintro ⟨h0, h1, h2⟩; apply hxy; funext j; fin_cases j <;> assumption
    by_cases h0 : x 0 = y 0 <;> by_cases h1 : x 1 = y 1 <;> by_cases h2 : x 2 = y 2 <;>
      simp_all

/-- **Fourier inversion on the torus.** -/
theorem inversion (ψ : Lat n × Sites → ℂ) :
    ψ = ((1 : ℂ) / (n + 1) ^ 3) • ∑ m : Lat n, pw n (cvec n m) (hat n ψ m) := by
  funext ⟨x, a⟩
  simp only [Pi.smul_apply, Finset.sum_apply, pw, hat, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hN : ((n : ℂ) + 1) ^ 3 ≠ 0 := by
    have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact pow_ne_zero 3 this
  have : ∀ y : Lat n, (∑ m : Lat n, 1 / ((n : ℂ) + 1) ^ 3 *
      (chi n (cvec n m) x * (star (chi n (cvec n m) y) * ψ (y, a)))) =
      if x = y then ψ (y, a) else 0 := by
    intro y
    rw [show (∑ m : Lat n, 1 / ((n : ℂ) + 1) ^ 3 *
      (chi n (cvec n m) x * (star (chi n (cvec n m) y) * ψ (y, a)))) =
      1 / ((n : ℂ) + 1) ^ 3 * (∑ m : Lat n, chi n (cvec n m) x * star (chi n (cvec n m) y)) * ψ (y, a) by
        rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun m _ => by ring]
    rw [chi_dual]
    split_ifs
    · field_simp
    · simp
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ### The real-space stationary states -/

lemma kvec_cell (m : Lat n) : GlobalTickInterval.InCell (kvec n (cvec n m)) := by
  intro j
  have hb := cen_bound n (m j)
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hb' : 2 * |(cen n (m j) : ℝ)| ≤ n + 1 := by exact_mod_cast hb
  have hk : |kOf n (cen n (m j))| ≤ Real.pi := by
    unfold kOf
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
      abs_of_pos hN, div_le_iff₀ hN]
    nlinarith [Real.pi_pos]
  exact abs_le.mp hk

lemma kvec_zero_iff (m : Lat n) : kvec n (cvec n m) = 0 ↔ m = 0 := by
  constructor
  · intro h; funext j
    have := congrFun h j
    simp only [kvec, cvec, kOf, Pi.zero_apply] at this
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hc : (cen n (m j) : ℝ) = 0 := by
      field_simp at this; nlinarith [Real.pi_pos]
    exact (cen_zero_iff n (m j)).mp (by exact_mod_cast hc)
  · rintro rfl; funext j; simp [kvec, cvec, kOf, (cen_zero_iff n 0).mpr rfl]

lemma chi_zero (x : Lat n) : chi n (cvec n 0) x = 1 := by
  simp [chi, cvec, phase, (cen_zero_iff n 0).mpr rfl]

lemma hat_smul (z : ℂ) (ψ : Lat n × Sites → ℂ) (m : Lat n) : hat n (z • ψ) m = z • hat n ψ m := by
  funext a; simp [hat, Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring

lemma hat_sum (w : Lat n → Sites → ℂ) (m' : Lat n) :
    hat n (∑ m, pw n (cvec n m) (w m)) m' = ((n + 1 : ℂ) ^ 3) • w m' := by
  have : hat n (∑ m, pw n (cvec n m) (w m)) m' = ∑ m, hat n (pw n (cvec n m) (w m)) m' := by
    funext a; simp [hat, Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]
  rw [this]; simp [hat_pw]

/-- **Fourier coefficients evolve blockwise.**  The real-space split update acts on the
discrete Fourier coefficient at every lattice momentum by the momentum-space update. -/
theorem hat_update (τ : ℝ) (ψ : Lat n × Sites → ℂ) (m : Lat n) :
    hat n (VacuumSplit.update (n + 1) τ *ᵥ ψ) m =
      VacuumSplit.momentumUpdate (kvec n (cvec n m)) τ *ᵥ hat n ψ m := by
  have hN : ((n : ℂ) + 1) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast Nat.succ_ne_zero n)
  have hU : VacuumSplit.update (n + 1) τ *ᵥ ψ = ((1 : ℂ) / (n + 1) ^ 3) •
      ∑ m', pw n (cvec n m') (VacuumSplit.momentumUpdate (kvec n (cvec n m')) τ *ᵥ hat n ψ m') := by
    conv_lhs => rw [inversion n ψ]
    rw [mulVec_smul, mulVec_sum]
    congr 1
    exact Finset.sum_congr rfl fun m' _ => update_acts n (cvec n m') τ (hat n ψ m')
  rw [hU, hat_smul, hat_sum, smul_smul, show (1 : ℂ) / (n + 1) ^ 3 * ((n : ℂ) + 1) ^ 3 = 1 by
    field_simp, one_smul]

lemma chi_ne_zero (c : Fin 3 → ℤ) (x : Lat n) : chi n c x ≠ 0 := by
  unfold chi phase; exact Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _

/-- **Spectral identification.**  The real-space split update on the `(n+1)³` torus has
eigenvalue `λ` exactly when some momentum-space update at a lattice momentum
`k = 2π c/(n+1)` does. -/
theorem eigen_iff (τ : ℝ) (μ : ℂ) :
    (∃ ψ : Lat n × Sites → ℂ, ψ ≠ 0 ∧ VacuumSplit.update (n + 1) τ *ᵥ ψ = μ • ψ) ↔
      ∃ m : Lat n, ∃ v : Sites → ℂ, v ≠ 0 ∧
        VacuumSplit.momentumUpdate (kvec n (cvec n m)) τ *ᵥ v = μ • v := by
  constructor
  · rintro ⟨ψ, hψ, he⟩
    by_contra hno
    push Not at hno
    apply hψ
    have hz : ∀ m, hat n ψ m = 0 := by
      intro m
      by_contra hne
      apply hno m (hat n ψ m) hne
      rw [← hat_update, he, hat_smul]
    rw [inversion n ψ]
    have : ∀ m : Lat n, pw n (cvec n m) (hat n ψ m) = 0 := fun m => by
      funext p; simp [pw, hz]
    simp [this]
  · rintro ⟨m, v, hv, he⟩
    refine ⟨pw n (cvec n m) v, ?_, ?_⟩
    · intro h0
      apply hv
      funext a
      have := congrFun h0 (0, a)
      simp only [pw, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left (chi_ne_zero n _ _)
    · rw [update_acts, he]
      funext p; simp [pw]; ring

/-- **Real-space stationary states.** For every small nonzero tick, a field on the whole torus is
left fixed by the real-space split update exactly when it is spatially constant with internal
vector in the wall kernel (the four free chiral components). -/
theorem real_fixed_iff :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ τ : ℝ, τ ≠ 0 → |τ| < δ → ∀ ψ : Lat n × Sites → ℂ,
      VacuumSplit.update (n + 1) τ *ᵥ ψ = ψ ↔
        ∃ v : Sites → ℂ, VacuumSplit.wall *ᵥ v = 0 ∧ ψ = fun p => v p.2 := by
  obtain ⟨δ1, hδ1, -, hfar⟩ := GlobalTickInterval.global_fixed_only_at_origin
  obtain ⟨δ2, hδ2, hiff⟩ := GlobalTickInterval.global_fixed_iff
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro n τ hτ hs ψ
  have hs1 : |τ| < δ1 := hs.trans_le (min_le_left _ _)
  have hs2 : |τ| < δ2 := hs.trans_le (min_le_right _ _)
  have h0cell : GlobalTickInterval.InCell (0 : Fin 3 → ℝ) := by
    intro j; simp [Real.pi_pos.le]
  have horigin : ∀ v, VacuumSplit.momentumUpdate 0 τ *ᵥ v = v ↔ VacuumSplit.wall *ᵥ v = 0 := by
    intro v
    rw [hiff τ hτ hs2 0 h0cell v]
    simp [VacuumSplit.wall, DomainWallSpectrum.wilson]
  constructor
  · intro hfix
    set c : ℂ := (1 : ℂ) / (n + 1) ^ 3
    have hN : ((n : ℂ) + 1) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast Nat.succ_ne_zero n)
    -- coefficients are fixed by the momentum updates
    have hcoef : ∀ m, VacuumSplit.momentumUpdate (kvec n (cvec n m)) τ *ᵥ hat n ψ m = hat n ψ m := by
      intro m
      have hU : VacuumSplit.update (n + 1) τ *ᵥ ψ =
          c • ∑ m', pw n (cvec n m') (VacuumSplit.momentumUpdate (kvec n (cvec n m')) τ *ᵥ hat n ψ m') := by
        conv_lhs => rw [inversion n ψ]
        rw [mulVec_smul, mulVec_sum]
        congr 1
        exact Finset.sum_congr rfl fun m' _ => update_acts n (cvec n m') τ (hat n ψ m')
      have h1 := congrArg (fun φ => hat n φ m) hU
      simp only [hat_smul, hat_sum] at h1
      rw [hfix] at h1
      rw [smul_smul, show c * ((n : ℂ) + 1) ^ 3 = 1 by simp [c, hN], one_smul] at h1
      exact h1.symm
    have hvanish : ∀ m, m ≠ 0 → hat n ψ m = 0 := by
      intro m hm
      by_contra hne
      exact hm ((kvec_zero_iff n m).mp (hfar τ hτ hs1 _ (kvec_cell n m) _ hne (hcoef m)))
    refine ⟨c • hat n ψ 0, ?_, ?_⟩
    · rw [mulVec_smul, (horigin _).mp (by simpa [(kvec_zero_iff n 0).mpr rfl] using hcoef 0),
        smul_zero]
    · conv_lhs => rw [inversion n ψ]
      rw [Finset.sum_eq_single (0 : Lat n) (fun m _ hm => by rw [hvanish m hm]; funext p; simp [pw])
        (by simp)]
      funext p; simp [pw, chi_zero, c]
  · rintro ⟨v, hv, rfl⟩
    have hpw : (fun p : Lat n × Sites => v p.2) = pw n (cvec n 0) v := by
      funext p; simp [pw, chi_zero]
    rw [hpw, update_acts, (kvec_zero_iff n 0).mpr rfl, (horigin v).mpr hv]

end PMAction.RealSpaceFourier
