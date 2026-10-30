import PMAction.GaugeFluctuation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section
namespace PMAction.FluctuationPremises
open Finset PMAction.GaugeFluctuation

/-! ## 1. Gauge invariance of the Hessian and the gauge parameter -/

section Ward
variable {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ}
  (br : M →ₗ[ℝ] M →ₗ[ℝ] M) (D : Fin n → Module.End ℝ M) (F : Fin n → Fin n → M)

/-- The Yang–Mills fluctuation operator before gauge fixing:
`(K₀ a)_ν = −Σ D_μD_μ a_ν + Σ D_μD_ν a_μ + Σ [F_μν, a_μ]`. -/
def bare (a : Fin n → M) (ν : Fin n) : M :=
  -(∑ μ, D μ (D μ (a ν))) + ∑ μ, D μ (D ν (a μ)) + ∑ μ, br (F μ ν) (a μ)

/-- A pure-gauge fluctuation `a_μ = D_μ ω`. -/
def gaugeMode (ω : M) : Fin n → M := fun μ => D μ ω

/-- The Faddeev–Popov operator `−Σ D_μD_μ`. -/
def ghost (ω : M) : M := -(∑ μ, D μ (D μ ω))

/-- Gauge-fixed operator with parameter `ξ`: `K_ξ a = K₀ a − ξ⁻¹ D(D·a)`. -/
def fixed (ξ : ℝ) (a : Fin n → M) (ν : Fin n) : M := bare br D F a ν - ξ⁻¹ • D ν (gdiv D a)

variable {br D F}

/-- At `ξ = 1` the gauge-fixed operator is `GaugeFluctuation.hess`. -/
theorem feynman (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = br (F μ ν) x)
    (a : Fin n → M) (ν : Fin n) : fixed br D F 1 a ν = hess br D F a ν := by
  have h : ∑ μ, D μ (D ν (a μ)) - D ν (gdiv D a) = ∑ μ, br (F μ ν) (a μ) := by
    rw [gdiv, map_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun μ _ => hcurv μ ν (a μ)
  simp only [fixed, bare, hess, inv_one, one_smul, two_smul]
  rw [← h]; abel

/-- **Ward identity.** If the background is on shell (`Σ_μ D_μ F_μν = 0`) and `D` is a
derivation of the bracket, pure-gauge fluctuations are null modes of `K₀`. -/
theorem gauge_null (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = br (F μ ν) x)
    (hleib : ∀ μ f x, D μ (br f x) = br (D μ f) x + br f (D μ x))
    (heom : ∀ ν, ∑ μ, D μ (F μ ν) = 0) (ω : M) (ν : Fin n) :
    bare br D F (gaugeMode D ω) ν = 0 := by
  have h1 : ∀ μ, D μ (D ν (D μ ω)) =
      D μ (D μ (D ν ω)) - br (D μ (F μ ν)) ω - br (F μ ν) (D μ ω) := by
    intro μ
    have e : D ν (D μ ω) = D μ (D ν ω) - br (F μ ν) ω := by rw [← hcurv μ ν ω]; abel
    rw [e, map_sub, hleib]; abel
  have h2 : ∑ μ, br (D μ (F μ ν)) ω = 0 := by
    rw [← LinearMap.sum_apply, ← map_sum, heom, map_zero, LinearMap.zero_apply]
  simp only [bare, gaugeMode, h1, sum_sub_distrib, h2]
  abel

/-- **Gauge-parameter dependence.** On pure-gauge modes, `K_ξ` acts as `ξ⁻¹` times the ghost
operator transported by `D`: `K_ξ (Dω) = ξ⁻¹ D(Gω)`. -/
theorem gauge_mode_fixed (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = br (F μ ν) x)
    (hleib : ∀ μ f x, D μ (br f x) = br (D μ f) x + br f (D μ x))
    (heom : ∀ ν, ∑ μ, D μ (F μ ν) = 0) (ξ : ℝ) (ω : M) (ν : Fin n) :
    fixed br D F ξ (gaugeMode D ω) ν = ξ⁻¹ • D ν (ghost D ω) := by
  rw [fixed, gauge_null hcurv hleib heom, ghost, map_neg, smul_neg, zero_sub]
  rfl

/-- Modes with `D·a = 0` see no gauge parameter. -/
theorem transverse_fixed (ξ : ℝ) (a : Fin n → M) (h : gdiv D a = 0) (ν : Fin n) :
    fixed br D F ξ a ν = bare br D F a ν := by
  simp [fixed, h]

end Ward

/-! ## 2. A concrete instance: Paper II's matrix gauge fields -/

section Matrices
variable {N : ℕ}

/-- The commutator as an `ℝ`-bilinear map on complex `N × N` matrices. -/
def comm : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.mk₂ ℝ (fun x y => x * y - y * x)
    (fun x x' y => by noncomm_ring)
    (fun c x y => by rw [smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun x y y' => by noncomm_ring)
    (fun c x y => by rw [smul_mul_assoc, mul_smul_comm, smul_sub])

/-- The trace pairing `−Re tr(xy)` (positive on anti-Hermitian matrices). -/
def tracePair : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(Matrix.trace (x * y)).re)
    (fun x x' y => by rw [add_mul, Matrix.trace_add, Complex.add_re]; ring)
    (fun c x y => by
      rw [smul_mul_assoc, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, smul_eq_mul]; ring)
    (fun x y y' => by rw [mul_add, Matrix.trace_add, Complex.add_re]; ring)
    (fun c x y => by
      rw [mul_smul_comm, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, smul_eq_mul]; ring)

@[simp] lemma comm_apply (x y : Matrix (Fin N) (Fin N) ℂ) : comm x y = x * y - y * x := rfl
@[simp] lemma tracePair_apply (x y : Matrix (Fin N) (Fin N) ℂ) :
    tracePair x y = -(Matrix.trace (x * y)).re := rfl

lemma trace_cyc (a b c : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (a * (b * c)) = Matrix.trace (b * (c * a)) := by
  rw [Matrix.trace_mul_comm, mul_assoc]

/-- **The hypotheses of `GaugeFluctuation` hold for matrix gauge fields.** Take a constant
background connection `A`, with `D_μ = [A_μ, ·]` and `F_μν = [A_μ, A_ν]`. Then the pairing is
symmetric and invariant, each `D_μ` is antisymmetric, the curvature acts as `[F_μν, ·]`, and
`D_μ` is a derivation of the bracket. -/
theorem matrix_instance {n : ℕ} (A : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    (∀ x y : Matrix (Fin N) (Fin N) ℂ, tracePair x y = tracePair y x) ∧
    (∀ f x y : Matrix (Fin N) (Fin N) ℂ, tracePair f (comm x y) = tracePair (comm f x) y) ∧
    (∀ μ, ∀ x y : Matrix (Fin N) (Fin N) ℂ, tracePair (comm (A μ) x) y = -tracePair x (comm (A μ) y)) ∧
    (∀ μ ν, ∀ x : Matrix (Fin N) (Fin N) ℂ, comm (A μ) (comm (A ν) x) - comm (A ν) (comm (A μ) x) =
      comm (comm (A μ) (A ν)) x) ∧
    (∀ μ, ∀ f x : Matrix (Fin N) (Fin N) ℂ, comm (A μ) (comm f x) = comm (comm (A μ) f) x + comm f (comm (A μ) x)) := by
  refine ⟨fun x y => ?_, fun f x y => ?_, fun μ x y => ?_, fun μ ν x => ?_, fun μ f x => ?_⟩
  · simp [Matrix.trace_mul_comm x y]
  · simp only [tracePair_apply, comm_apply, mul_sub, sub_mul, Matrix.trace_sub, Complex.sub_re]
    rw [Matrix.trace_mul_comm f (y * x), mul_assoc y x f, Matrix.trace_mul_comm y (x * f),
      mul_assoc f x y]
  · simp only [tracePair_apply, comm_apply, mul_sub, sub_mul, Matrix.trace_sub, Complex.sub_re,
      neg_neg, mul_assoc]
    rw [trace_cyc (A μ) x y]; ring
  · simp only [comm_apply]; noncomm_ring
  · simp only [comm_apply]; noncomm_ring

/-- `GaugeFluctuation.quad_eq_hess` holds for matrix gauge fields with a constant background:
the fluctuation operator is `−D² + 2[F, ·]` with `F_μν = [A_μ, A_ν]`. -/
theorem matrix_hessian {n : ℕ} (A : Fin n → Matrix (Fin N) (Fin N) ℂ)
    (a : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    quad tracePair comm (fun μ => comm (A μ)) (fun μ ν => comm (A μ) (A ν)) a =
      (1 / 2) * ∑ ν, tracePair (a ν)
        (hess comm (fun μ => comm (A μ)) (fun μ ν => comm (A μ) (A ν)) a ν) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := matrix_instance A
  exact quad_eq_hess _ _ _ _ h1 h3 h2 h4 a

/-- The Ward identity for matrix gauge fields, for an on-shell constant background
`Σ_μ [A_μ, [A_μ, A_ν]] = 0`. -/
theorem matrix_ward {n : ℕ} (A : Fin n → Matrix (Fin N) (Fin N) ℂ)
    (heom : ∀ ν, ∑ μ, comm (A μ) (comm (A μ) (A ν)) = 0) (ξ : ℝ) (ω : Matrix (Fin N) (Fin N) ℂ)
    (ν : Fin n) :
    fixed comm (fun μ => comm (A μ)) (fun μ ν => comm (A μ) (A ν)) ξ
        (gaugeMode (fun μ => comm (A μ)) ω) ν =
      ξ⁻¹ • comm (A ν) (ghost (fun μ => comm (A μ)) ω) := by
  obtain ⟨-, -, -, h4, h5⟩ := matrix_instance A
  exact gauge_mode_fixed h4 h5 heom ξ ω ν

/-- An `SU(2)` field direction `f = b · diag(i/2, −i/2)`. It is anti-Hermitian and traceless. -/
def cartan (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * b / 2, 0; 0, -(Complex.I * b / 2)]

/-- **Charge action derived.** The charged modes `E₁₂`, `E₂₁` (the `W^±` directions) are
eigenvectors of `[f, ·]` with eigenvalues `i q b`, `q = ±1`, and the Cartan direction is
neutral. -/
theorem charge_action (b : ℝ) :
    comm (cartan b) !![0, 1; 0, 0] = (Complex.I * b) • !![0, 1; 0, 0] ∧
    comm (cartan b) !![0, 0; 1, 0] = (-(Complex.I * b)) • !![0, 0; 1, 0] ∧
    comm (cartan b) (cartan 1) = 0 ∧
    Matrix.conjTranspose (cartan b) = -cartan b ∧ Matrix.trace (cartan b) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cartan]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cartan]
    ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cartan] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cartan, Matrix.conjTranspose_apply, Complex.ext_iff] <;> ring
  · simp [cartan, Matrix.trace_fin_two]

end Matrices

/-! ## 3. The Landau spectrum from `[π₁, π₂] = i b` -/

section Ladder

/-- **Ladder algebra.** With `c = π₁ + iπ₂` and `c† = π₁ − iπ₂`, the relation `[π₁, π₂] = i b`
gives `c†c = π₁² + π₂² − b` and `[c, c†] = 2b`. -/
theorem ladder_algebra {R : Type*} [Ring R] [Algebra ℂ R] (p1 p2 : R) (b : ℝ)
    (h : p1 * p2 - p2 * p1 = (Complex.I * b) • (1 : R)) :
    (p1 - Complex.I • p2) * (p1 + Complex.I • p2) = p1 ^ 2 + p2 ^ 2 - (b : ℂ) • (1 : R) ∧
    (p1 + Complex.I • p2) * (p1 - Complex.I • p2) -
        (p1 - Complex.I • p2) * (p1 + Complex.I • p2) = (2 * b : ℂ) • (1 : R) := by
  have hI : Complex.I * (Complex.I * (b : ℂ)) = -(b : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  have e1 : (p1 - Complex.I • p2) * (p1 + Complex.I • p2) =
      p1 * p1 + p2 * p2 + Complex.I • (p1 * p2 - p2 * p1) := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
      smul_sub]
    module
  have e2 : (p1 + Complex.I • p2) * (p1 - Complex.I • p2) =
      p1 * p1 + p2 * p2 - Complex.I • (p1 * p2 - p2 * p1) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul,
      Complex.I_mul_I, neg_one_smul]
    module
  rw [h, smul_smul, hI] at e1 e2
  constructor
  · rw [e1, sq, sq]; module
  · rw [e1, e2]; module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (c cd : V →ₗ[ℂ] V) (b : ℝ)

/-- The orbital Hamiltonian `π₁² + π₂² = c†c + b`. -/
def landauH (x : V) : V := cd (c x) + (b : ℂ) • x

variable {c cd b}

lemma lower (hcomm : ∀ x, c (cd x) - cd (c x) = (2 * b : ℂ) • x) {E : ℂ} {x : V}
    (hx : landauH c cd b x = E • x) :
    landauH c cd b (c x) = (E - 2 * b) • c x := by
  have h1 : c (landauH c cd b x) = landauH c cd b (c x) + (2 * b : ℂ) • c x := by
    simp only [landauH, map_add, map_smul]
    rw [sub_eq_iff_eq_add.mp (hcomm (c x))]; abel
  rw [hx, map_smul] at h1
  rw [sub_smul, h1]; abel

lemma raise (hcomm : ∀ x, c (cd x) - cd (c x) = (2 * b : ℂ) • x) {E : ℂ} {x : V}
    (hx : landauH c cd b x = E • x) :
    landauH c cd b (cd x) = (E + 2 * b) • cd x := by
  have e : cd (c (cd x)) = cd (cd (c x)) + (2 * b : ℂ) • cd x := by
    rw [sub_eq_iff_eq_add.mp (hcomm x), map_add, map_smul]; abel
  have h2 : cd (landauH c cd b x) = cd (cd (c x)) + (b : ℂ) • cd x := by
    simp [landauH, map_add]
  rw [hx, map_smul] at h2
  simp only [landauH, e, add_smul]
  rw [show cd (cd (c x)) = E • cd x - (b : ℂ) • cd x by rw [h2]; abel]
  module

/-- **The Landau tower.** A state annihilated by `c` generates the levels `(2n + 1) b`. -/
theorem landau_tower (hcomm : ∀ x, c (cd x) - cd (c x) = (2 * b : ℂ) • x) {ψ : V}
    (h0 : c ψ = 0) (k : ℕ) :
    landauH c cd b ((⇑cd)^[k] ψ) = ((2 * k + 1) * b : ℂ) • (⇑cd)^[k] ψ := by
  induction k with
  | zero => simp [landauH, h0]
  | succ k ih =>
    rw [Function.iterate_succ_apply', raise hcomm ih]
    congr 1; push_cast; ring

/-- Every eigenvalue is at least `b`. -/
lemma eigen_ge (hadj : ∀ x y, inner ℂ (c x) y = inner ℂ x (cd y)) {E : ℝ} {φ : V}
    (hφ : φ ≠ 0) (hE : landauH c cd b φ = (E : ℂ) • φ) : b ≤ E := by
  have key : (E : ℂ) * inner ℂ φ φ = inner ℂ (c φ) (c φ) + (b : ℂ) * inner ℂ φ φ := by
    rw [← inner_smul_right, ← hE, landauH, inner_add_right, inner_smul_right, hadj]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have hr : E * ‖φ‖ ^ 2 = ‖c φ‖ ^ 2 + b * ‖φ‖ ^ 2 := by
    apply Complex.ofReal_injective; push_cast; exact key
  have hp2 : 0 < ‖φ‖ ^ 2 := by have := norm_pos_iff.mpr hφ; positivity
  nlinarith [sq_nonneg ‖c φ‖]

/-- **The Landau spectrum.** If `[c, c†] = 2b` with `b > 0` and `c†` is the adjoint of `c`, every
eigenvalue of `c†c + b` is `(2k + 1) b` for some `k ∈ ℕ`. -/
theorem landau_spectrum (hb : 0 < b) (hcomm : ∀ x, c (cd x) - cd (c x) = (2 * b : ℂ) • x)
    (hadj : ∀ x y, inner ℂ (c x) y = inner ℂ x (cd y)) {E : ℝ} {ψ : V} (hψ : ψ ≠ 0)
    (hE : landauH c cd b ψ = (E : ℂ) • ψ) : ∃ k : ℕ, E = (2 * k + 1) * b := by
  have eig : ∀ k : ℕ, landauH c cd b ((⇑c)^[k] ψ) = ((E - 2 * k * b : ℝ) : ℂ) • (⇑c)^[k] ψ := by
    intro k
    induction k with
    | zero => simpa using hE
    | succ k ih =>
      rw [Function.iterate_succ_apply', lower hcomm ih]
      congr 1; push_cast; ring
  have ex : ∃ k, (⇑c)^[k + 1] ψ = 0 := by
    by_contra hall
    push Not at hall
    have nz : ∀ k, (⇑c)^[k] ψ ≠ 0 := by
      intro k; cases k with
      | zero => simpa using hψ
      | succ k => exact hall k
    obtain ⟨k, hk⟩ := exists_nat_gt (E / (2 * b))
    have := eigen_ge hadj (nz k) (eig k)
    rw [div_lt_iff₀ (by positivity)] at hk
    nlinarith
  classical
  set k := Nat.find ex with hk
  have hz : (⇑c)^[k + 1] ψ = 0 := Nat.find_spec ex
  have hnz : (⇑c)^[k] ψ ≠ 0 := by
    cases hk' : k with
    | zero => simpa using hψ
    | succ j =>
      have : ¬ (⇑c)^[j + 1] ψ = 0 := Nat.find_min ex (by omega)
      simpa using this
  have hb' : landauH c cd b ((⇑c)^[k] ψ) = (b : ℂ) • (⇑c)^[k] ψ := by
    simp only [landauH]
    rw [← Function.iterate_succ_apply' (⇑c), hz, map_zero, zero_add]
  rw [eig k] at hb'
  have hsub : (((E - 2 * k * b : ℝ) : ℂ) - b) • (⇑c)^[k] ψ = 0 := by rw [sub_smul, hb', sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · refine ⟨k, ?_⟩
    have := congrArg Complex.re h
    simp at this
    linarith
  · exact absurd h hnz

end Ladder

/-! ## 4. Weak-field normalization of the degeneracy -/

open Real in
/-- **The degeneracy weight is fixed by the weak-field limit.** With weight `2x` per Landau
level, a pair's kernel tends to the two free states: `|x/sinh x − 1| ≤ C x²`. -/
theorem weak_field_normalization :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → |x / sinh x - 1| ≤ C * x ^ 2 := by
  obtain ⟨C, hC, h⟩ := RunningResponse.pair_coefficient 0
  refine ⟨C / 2 + 1 / 6, by positivity, fun x hx h1 => ?_⟩
  have := h x hx h1 (by simp)
  simp only [zero_mul, neg_zero, exp_zero] at this
  have hx2 : x ^ 4 ≤ x ^ 2 := by
    have : x ^ 4 = x ^ 2 * x ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) (by nlinarith)
  rw [abs_le] at this ⊢
  constructor <;> nlinarith [this.1, this.2, mul_le_mul_of_nonneg_left hx2 hC]

end PMAction.FluctuationPremises
