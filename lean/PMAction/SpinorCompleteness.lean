import PMAction.VATrace

/-!
# Normalized massive Dirac spinor completeness

With the Dirac matrices of `PMAction.VATrace` (proved equal to `WallChiralCurrent.diracGamma`
by `VATrace.g_eq`), real `m` and real on-shell `p` with `p₀ > 0`, `p₀² = p₁² + p₂² + p₃² + m²`:

  `P = p̸ = VATrace.sl p`,  `D = P − m`,  `A = (P + m) γ⁰`,  `Q = A / (2p₀)`.

Algebra (no mass shell needed unless stated):
* `g0_sq`: `γ⁰γ⁰ = 1`; `slash_sq`: `P P = p² · 1`; `anticomm0`: `P γ⁰ + γ⁰ P = 2p₀`.
* `A_hermitian`: `Aᴴ = A`.
* `A_eq`: `A = 2p₀ − γ⁰ D` (the key identity).
* `trace_A`: `Tr A = 4p₀`.
* On shell: `DA_zero`: `D A = 0`; `A_sq`: `A² = 2p₀ A`.

Projector and range:
* `Q_hermitian`, `Q_idempotent`: `Q` is an orthogonal projector.
* `Q_fixes_kernel`: `D v = 0 → Q v = v`; `range_in_kernel`: `D (Q v) = 0`; `range_eq_kernel`:
  range `Q` = ker `D` exactly.

Completeness (main theorem, basis-independent):
* `completeness`: for **any** finite family `e` of spinors that is orthonormal, lies in ker `D` and
  spans ker `D`, `Σ_s e_s e_s† = Q`.
* `rank_two`: such a family has exactly two members (`Tr Q = 2`).
* `spin_sums`: with `u_s = √(2p₀) e_s` and `ū_s = u_s† γ⁰`: `Σ u_s u_s† = A` and
  `Σ u_s ū_s = p̸ + m`.
* `antiparticle_spin_sums`: the same with `m ↦ −m`: for an orthonormal basis of ker `(p̸ + m)`,
  `Σ v_s v̄_s = p̸ − m`.
* `massless_A`: at `m = 0`, `A = p̸ γ⁰`, the matrix of Paper V's `MuonAmplitude.spin_projector`.

Not claimed: that these spinors are the physical states of the substrate dynamics, statistics, or
the full muon amplitude (that needs the amplitude-to-trace bridge, and the muon is massive).
-/

noncomputable section
namespace PMAction.SpinorCompleteness
open Matrix ConcreteFermion VATrace

/-- Real components as complex. -/
def cp (p : Fin 4 → ℝ) : Fin 4 → ℂ := fun i => (p i : ℂ)

def P (p : Fin 4 → ℝ) : Spin := sl (cp p)
def D (p : Fin 4 → ℝ) (m : ℝ) : Spin := P p - (m : ℂ) • 1
def A (p : Fin 4 → ℝ) (m : ℝ) : Spin := (P p + (m : ℂ) • 1) * g 0
def Q (p : Fin 4 → ℝ) (m : ℝ) : Spin := ((1 / (2 * p 0) : ℝ) : ℂ) • A p m

/-- Minkowski square. -/
def msq (p : Fin 4 → ℝ) : ℝ := p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2

theorem g0_sq : g 0 * g 0 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [g, mul_apply, Fin.sum_univ_four, one_apply]

set_option maxHeartbeats 1000000 in
theorem slash_sq (p : Fin 4 → ℝ) : P p * P p = ((msq p : ℝ) : ℂ) • (1 : Spin) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [P, sl, cp, msq, mul_apply, Fin.sum_univ_four, one_apply] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem anticomm0 (p : Fin 4 → ℝ) : P p * g 0 + g 0 * P p = ((2 * p 0 : ℝ) : ℂ) • (1 : Spin) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [P, sl, cp, g, one_apply] <;> ring

theorem A_hermitian (p : Fin 4 → ℝ) (m : ℝ) : (A p m)ᴴ = A p m := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [A, P, sl, cp, g, mul_apply, Fin.sum_univ_four, one_apply, conjTranspose_apply] <;> ring

/-- **The key identity `A = 2p₀ − γ⁰ D`.** -/
theorem A_eq (p : Fin 4 → ℝ) (m : ℝ) :
    A p m = ((2 * p 0 : ℝ) : ℂ) • (1 : Spin) - g 0 * D p m := by
  have h := anticomm0 p
  rw [A, D, add_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one, ← h]
  abel

theorem trace_A (p : Fin 4 → ℝ) (m : ℝ) : (A p m).trace = 4 * (p 0 : ℂ) := by
  simp [A, P, sl, cp, g, Matrix.trace, mul_apply, Fin.sum_univ_four, one_apply]; ring

/-- On shell, `(p̸ + m)(p̸ − m) = 0` and `(p̸ − m)(p̸ + m) = 0`. -/
lemma shell_products (p : Fin 4 → ℝ) (m : ℝ) (hs : msq p = m ^ 2) :
    (P p + (m : ℂ) • 1) * D p m = 0 ∧ D p m * (P p + (m : ℂ) • 1) = 0 := by
  have h2 := slash_sq p
  rw [hs] at h2
  constructor
  · rw [D, mul_sub, add_mul, add_mul, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, mul_one, smul_smul]
    push_cast; ring_nf; abel_nf; simp [pow_two]
  · rw [D, sub_mul, mul_add, mul_add, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, mul_one, smul_smul]
    push_cast; ring_nf; abel_nf; simp [pow_two]

theorem DA_zero (p : Fin 4 → ℝ) (m : ℝ) (hs : msq p = m ^ 2) : D p m * A p m = 0 := by
  rw [A, ← Matrix.mul_assoc, (shell_products p m hs).2, Matrix.zero_mul]

theorem A_sq (p : Fin 4 → ℝ) (m : ℝ) (hs : msq p = m ^ 2) :
    A p m * A p m = ((2 * p 0 : ℝ) : ℂ) • A p m := by
  have hAg : A p m * g 0 = P p + (m : ℂ) • 1 := by rw [A, Matrix.mul_assoc, g0_sq, mul_one]
  conv_lhs => rw [show A p m * A p m = A p m * (((2 * p 0 : ℝ) : ℂ) • (1 : Spin) - g 0 * D p m) by
    rw [← A_eq]]
  rw [mul_sub, Matrix.mul_smul, mul_one, ← Matrix.mul_assoc, hAg, (shell_products p m hs).1, sub_zero]

/-! ### The projector -/

variable (p : Fin 4 → ℝ) (m : ℝ)

theorem Q_hermitian : (Q p m)ᴴ = Q p m := by
  rw [Q, conjTranspose_smul, A_hermitian]; simp

theorem Q_idempotent (hp : 0 < p 0) (hs : msq p = m ^ 2) : Q p m * Q p m = Q p m := by
  rw [Q, Matrix.smul_mul, Matrix.mul_smul, A_sq p m hs, smul_smul, smul_smul]
  congr 1
  have : p 0 ≠ 0 := hp.ne'
  push_cast; field_simp

/-- `Q = 1 − γ⁰ D/(2p₀)`. -/
lemma Q_eq (hp : 0 < p 0) : Q p m = 1 - ((1 / (2 * p 0) : ℝ) : ℂ) • (g 0 * D p m) := by
  rw [Q, A_eq, smul_sub, smul_smul]
  have : p 0 ≠ 0 := hp.ne'
  congr 1
  rw [show ((1 / (2 * p 0) : ℝ) : ℂ) * ((2 * p 0 : ℝ) : ℂ) = 1 by
    rw [← Complex.ofReal_mul]; field_simp; simp]
  simp

/-- **`Q` fixes the kernel of `D`.** -/
theorem Q_fixes_kernel (hp : 0 < p 0) (v : Fin 4 → ℂ) (hv : D p m *ᵥ v = 0) : Q p m *ᵥ v = v := by
  rw [Q_eq p m hp, sub_mulVec, one_mulVec, smul_mulVec, ← mulVec_mulVec, hv, mulVec_zero,
    smul_zero, sub_zero]

/-- **`Q` maps into the kernel of `D`.** -/
theorem range_in_kernel (hs : msq p = m ^ 2) (v : Fin 4 → ℂ) : D p m *ᵥ (Q p m *ᵥ v) = 0 := by
  rw [mulVec_mulVec, Q, Matrix.mul_smul, DA_zero p m hs, smul_zero, zero_mulVec]

/-- **Range of `Q` = ker `D`.** -/
theorem range_eq_kernel (hp : 0 < p 0) (hs : msq p = m ^ 2) :
    Set.range (fun v => Q p m *ᵥ v) = {v | D p m *ᵥ v = 0} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩; exact range_in_kernel p m hs v
  · intro hw; exact ⟨w, Q_fixes_kernel p m hp w hw⟩

/-! ### Completeness -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_s e_s e_s†` as a matrix. -/
def outerSum (e : ι → Fin 4 → ℂ) : Spin := ∑ s, vecMulVec (e s) (star (e s))

omit [DecidableEq ι] in
lemma outerSum_mulVec (e : ι → Fin 4 → ℂ) (v : Fin 4 → ℂ) :
    outerSum e *ᵥ v = ∑ s, (star (e s) ⬝ᵥ v) • e s := by
  ext a
  simp only [outerSum, sum_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

/-- **Basis-independent completeness.** For any orthonormal family spanning ker `D`,
`Σ_s e_s e_s† = Q`. -/
theorem completeness (hp : 0 < p 0) (hs : msq p = m ^ 2) (e : ι → Fin 4 → ℂ)
    (horth : ∀ s t, star (e s) ⬝ᵥ e t = if s = t then 1 else 0)
    (hker : ∀ s, D p m *ᵥ e s = 0)
    (hspan : ∀ v, D p m *ᵥ v = 0 → v ∈ Submodule.span ℂ (Set.range e)) :
    outerSum e = Q p m := by
  -- `outerSum e` is the identity on the span.
  have hfix : ∀ v ∈ Submodule.span ℂ (Set.range e), outerSum e *ᵥ v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [outerSum_mulVec]
      simp only [horth, ite_smul, one_smul, zero_smul]
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, hx]
  -- `Q * outerSum = outerSum`: columns of `outerSum` lie in ker `D`.
  have h1 : Q p m * outerSum e = outerSum e := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← mulVec_mulVec]
    apply Q_fixes_kernel p m hp
    rw [outerSum_mulVec, mulVec_sum]
    simp [mulVec_smul, hker]
  -- `outerSum * Q = Q`: columns of `Q` lie in ker `D`, hence in the span.
  have h2 : outerSum e * Q p m = Q p m := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← mulVec_mulVec]
    exact hfix _ (hspan _ (range_in_kernel p m hs _))
  -- Both Hermitian, so `Q = Q * outerSum` and `outerSum = Q * outerSum`.
  have hOh : (outerSum e)ᴴ = outerSum e := by
    rw [outerSum, conjTranspose_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ext a b
    simp [vecMulVec, conjTranspose_apply, mul_comm]
  have h3 : Q p m * outerSum e = Q p m := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, hOh, Q_hermitian] at this
  rw [← h1, h3]

/-- **Rank two.** -/
theorem rank_two (hp : 0 < p 0) (hs : msq p = m ^ 2) (e : ι → Fin 4 → ℂ)
    (horth : ∀ s t, star (e s) ⬝ᵥ e t = if s = t then 1 else 0)
    (hker : ∀ s, D p m *ᵥ e s = 0)
    (hspan : ∀ v, D p m *ᵥ v = 0 → v ∈ Submodule.span ℂ (Set.range e)) :
    Fintype.card ι = 2 := by
  have hc := congrArg Matrix.trace (completeness p m hp hs e horth hker hspan)
  have hl : (outerSum e).trace = Fintype.card ι := by
    simp only [outerSum, trace_sum]
    have : ∀ s, (vecMulVec (e s) (star (e s))).trace = 1 := by
      intro s
      have h1 := horth s s
      simp only [↓reduceIte] at h1
      have ht : (vecMulVec (e s) (star (e s))).trace = star (e s) ⬝ᵥ e s := by
        simp [Matrix.trace, vecMulVec, dotProduct, mul_comm]
      rw [ht, h1]
    simp [this]
  have hr : (Q p m).trace = 2 := by
    rw [Q, trace_smul, trace_A, smul_eq_mul]
    have hc : (p 0 : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    push_cast; field_simp; norm_num
  rw [hl, hr] at hc
  exact_mod_cast hc

/-- **The spin sums.** -/
theorem spin_sums (hp : 0 < p 0) (hs : msq p = m ^ 2) (e : ι → Fin 4 → ℂ)
    (horth : ∀ s t, star (e s) ⬝ᵥ e t = if s = t then 1 else 0)
    (hker : ∀ s, D p m *ᵥ e s = 0)
    (hspan : ∀ v, D p m *ᵥ v = 0 → v ∈ Submodule.span ℂ (Set.range e)) :
    let u := fun s => ((Real.sqrt (2 * p 0) : ℝ) : ℂ) • e s
    (∑ s, vecMulVec (u s) (star (u s))) = A p m ∧
      (∑ s, vecMulVec (u s) (star (u s) ᵥ* g 0)) = P p + (m : ℂ) • 1 := by
  intro u
  have hsum : (∑ s, vecMulVec (u s) (star (u s))) = ((2 * p 0 : ℝ) : ℂ) • outerSum e := by
    simp only [u, outerSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hr : (Real.sqrt (2 * p 0)) * Real.sqrt (2 * p 0) = 2 * p 0 :=
      Real.mul_self_sqrt (by linarith)
    have hc : ((Real.sqrt (2 * p 0) : ℝ) : ℂ) * ((Real.sqrt (2 * p 0) : ℝ) : ℂ) =
        ((2 * p 0 : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, hr]
    ext a b
    simp only [vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul',
      Complex.star_def, Complex.conj_ofReal, Matrix.smul_apply]
    linear_combination (e s a * (starRingEnd ℂ) (e s b)) * hc
  have hA : (∑ s, vecMulVec (u s) (star (u s))) = A p m := by
    rw [hsum, completeness p m hp hs e horth hker hspan, Q, smul_smul]
    have : p 0 ≠ 0 := hp.ne'
    rw [show ((2 * p 0 : ℝ) : ℂ) * ((1 / (2 * p 0) : ℝ) : ℂ) = 1 by
      rw [← Complex.ofReal_mul]; field_simp; simp, one_smul]
  refine ⟨hA, ?_⟩
  have hbar : (∑ s, vecMulVec (u s) (star (u s) ᵥ* g 0)) =
      (∑ s, vecMulVec (u s) (star (u s))) * g 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    ext a b
    simp [vecMulVec, vecMul, mul_apply, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hbar, hA, A, Matrix.mul_assoc, g0_sq, mul_one]

/-- **Antiparticles**: the same with `m ↦ −m`. For an orthonormal basis of ker `(p̸ + m)`, the
spin sum with `v̄ = v† γ⁰` is `p̸ − m`. -/
theorem antiparticle_spin_sums (hp : 0 < p 0) (hs : msq p = m ^ 2) (e : ι → Fin 4 → ℂ)
    (horth : ∀ s t, star (e s) ⬝ᵥ e t = if s = t then 1 else 0)
    (hker : ∀ s, D p (-m) *ᵥ e s = 0)
    (hspan : ∀ v, D p (-m) *ᵥ v = 0 → v ∈ Submodule.span ℂ (Set.range e)) :
    let v := fun s => ((Real.sqrt (2 * p 0) : ℝ) : ℂ) • e s
    (∑ s, vecMulVec (v s) (star (v s) ᵥ* g 0)) = P p - (m : ℂ) • 1 := by
  intro v
  have hs' : msq p = (-m) ^ 2 := by rw [hs]; ring
  have := (spin_sums p (-m) hp hs' e horth hker hspan).2
  rw [show P p - (m : ℂ) • 1 = P p + ((-m : ℝ) : ℂ) • 1 by push_cast; rw [neg_smul, sub_eq_add_neg]]
  exact this

/-- At `m = 0`, `A = p̸ γ⁰`, the matrix of Paper V's massless results. -/
theorem massless_A : A p 0 = P p * g 0 := by simp [A]

end PMAction.SpinorCompleteness
