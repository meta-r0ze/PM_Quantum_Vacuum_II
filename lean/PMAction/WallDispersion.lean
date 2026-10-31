import PMAction.WallExchange
import PMAction.WallSeesaw

/-!
# The complete spectrum of the one-flavour two-wall Hamiltonian

`H_y(k) = [[K(k) + δβ, y·hop], [y·back, K(k) + δβ]]` on the eight components `Fin 4 ⊕ Fin 4`.
`DomainWallSpectrum.energy_branches` shows (for `y = 1`) that every energy lies on one of two
squared branches, but not that both occur or with what multiplicity.

* `S_anticomm`, `S_sq`: `S = [[0, βΓ], [βΓ, 0]]` anticommutes with `H_y` and `S² = −1`. So the
  spectrum is symmetric under `E ↦ −E`.
* `H_sq`, `X_quadratic`: `X = H² − (|k|² + δ²)` satisfies `X² = y² X + y²δ²`.
* `branch_masses`: the two roots give masses `m±² = δ² + (y² ± r)/2` with `r = √(y⁴ + 4y²δ²)`.
  Their product is `δ⁴` (the seesaw) and their sum is `y² + 2δ²`.
* `spectral_decomposition`: four mutually orthogonal idempotents `R (b, σ)`, for branch `b` and
  sign `σ`, sum to `1`. Each satisfies `H R = σ √(|k|² + m_b²) R` and has trace `2`. So the eight
  components are exactly two Dirac particles, of masses `m₋` and `m₊`. Each has two spin states
  at `E = +√(|k|² + m²)` and two at `−√(|k|² + m²)`.
* `eigenvector_exists`: each of the four energies has a nonzero eigenvector.
-/

noncomputable section
namespace PMAction.WallDispersion
open Matrix PMAction ConcreteFermion PMAction.WallExchange

abbrev Ix := Fin 4 ⊕ Fin 4

/-- The one-flavour two-wall Hamiltonian with real link strength `y`. -/
def Hy (k : Fin 3 → ℝ) (δ y : ℝ) : Matrix Ix Ix ℂ :=
  fromBlocks (WallExchange.diag k δ) ((y : ℂ) • hop) ((y : ℂ) • back) (WallExchange.diag k δ)

/-- The chiral flip. -/
def S : Matrix Ix Ix ℂ := fromBlocks 0 (beta * gamma) (beta * gamma) 0

/-- Momentum square. -/
def msq3 (k : Fin 3 → ℝ) : ℝ := k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2

def Pp : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]
def Pm : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1]

set_option maxHeartbeats 4000000 in
theorem S_anticomm (k : Fin 3 → ℝ) (δ y : ℝ) : S * Hy k δ y + Hy k δ y * S = 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [S, Hy, WallExchange.diag, K, hop, back, beta, gamma, alpha, mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_three, Fintype.sum_sum_type] <;> ring

set_option maxHeartbeats 4000000 in
theorem S_sq : S * S = -1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [S, beta, gamma, mul_apply, Fin.sum_univ_four, Fintype.sum_sum_type, one_apply]

set_option maxHeartbeats 8000000 in
/-- **The square.** -/
theorem H_sq (k : Fin 3 → ℝ) (δ y : ℝ) :
    Hy k δ y * Hy k δ y = fromBlocks
      (((msq3 k + δ ^ 2 : ℝ) : ℂ) • 1 + ((y ^ 2 : ℝ) : ℂ) • Pm) (-((y * δ : ℝ) : ℂ) • 1)
      (-((y * δ : ℝ) : ℂ) • 1) (((msq3 k + δ ^ 2 : ℝ) : ℂ) • 1 + ((y ^ 2 : ℝ) : ℂ) • Pp) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [Hy, WallExchange.diag, K, hop, back, beta, alpha, mul_apply, msq3, Pp, Pm,
      Fin.sum_univ_four, Fin.sum_univ_three, Fintype.sum_sum_type, one_apply] <;> ring_nf <;>
    simp [Complex.I_sq]

/-- `X = H² − (|k|² + δ²)`. -/
def X (k : Fin 3 → ℝ) (δ y : ℝ) : Matrix Ix Ix ℂ :=
  Hy k δ y * Hy k δ y - ((msq3 k + δ ^ 2 : ℝ) : ℂ) • 1

theorem X_eq (k : Fin 3 → ℝ) (δ y : ℝ) :
    X k δ y = fromBlocks (((y ^ 2 : ℝ) : ℂ) • Pm) (-((y * δ : ℝ) : ℂ) • 1)
      (-((y * δ : ℝ) : ℂ) • 1) (((y ^ 2 : ℝ) : ℂ) • Pp) := by
  rw [X, H_sq, ← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp only [smul_zero, neg_zero, add_zero]
  congr 1 <;> abel

set_option maxHeartbeats 4000000 in
/-- **The quadratic.** `X² = y² X + y²δ²`. -/
theorem X_quadratic (k : Fin 3 → ℝ) (δ y : ℝ) :
    X k δ y * X k δ y = ((y ^ 2 : ℝ) : ℂ) • X k δ y + ((y ^ 2 * δ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [X_eq]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [Pp, Pm, mul_apply, Fin.sum_univ_four, Fintype.sum_sum_type, one_apply] <;> ring

theorem trace_X (k : Fin 3 → ℝ) (δ y : ℝ) : (X k δ y).trace = 4 * ((y ^ 2 : ℝ) : ℂ) := by
  rw [X_eq]
  simp [Pp, Pm, Matrix.trace, Fin.sum_univ_four, Fintype.sum_sum_type]; ring

/-! ## Generic algebra: two-root quadratic and sign split -/

section Algebra
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Branch projector for root `p` of `X² = (p+q)X − pq`. -/
def proj (X : A) (p q : ℂ) : A := (1 / (p - q)) • (X - q • 1)

lemma factor (X : A) (p q : ℂ) (hX : X * X = (p + q) • X - (p * q) • 1) :
    (X - p • 1) * (X - q • 1) = 0 := by
  have e : (X - p • 1) * (X - q • 1) = X * X - (p + q) • X + (p * q) • 1 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [e, hX]; module

lemma proj_add (X : A) (p q : ℂ) (hpq : p ≠ q) : proj X p q + proj X q p = 1 := by
  have h : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have h' : q - p = -(p - q) := by ring
  simp only [proj, h', one_div, inv_neg, neg_smul, ← smul_neg, ← smul_add]
  rw [show X - q • (1 : A) + -(X - p • 1) = (p - q) • 1 by module, smul_smul, inv_mul_cancel₀ h,
    one_smul]

lemma X_proj (X : A) (p q : ℂ) (hX : X * X = (p + q) • X - (p * q) • 1) :
    X * proj X p q = p • proj X p q := by
  have hf := factor X p q hX
  have e : X * (X - q • 1) = p • (X - q • 1) := by
    have : (X - p • 1) * (X - q • 1) = X * (X - q • 1) - p • (X - q • 1) := by
      simp only [sub_mul, smul_mul_assoc, one_mul]
    rw [this] at hf
    exact sub_eq_zero.mp hf
  simp only [proj, mul_smul_comm, e, smul_comm (1 / (p - q)) p]

lemma proj_mul_other (X : A) (p q : ℂ) (_hpq : p ≠ q) (hX : X * X = (p + q) • X - (p * q) • 1) :
    proj X p q * proj X q p = 0 := by
  have hX' : X * X = (q + p) • X - (q * p) • 1 := by rw [add_comm, mul_comm]; exact hX
  have h := X_proj X q p hX'
  have e : proj X p q * proj X q p = (1 / (p - q)) • (X * proj X q p - q • proj X q p) := by
    simp only [proj, sub_mul, smul_mul_assoc, one_mul, smul_sub]
  rw [e, h, sub_self, smul_zero]

lemma proj_idem (X : A) (p q : ℂ) (hpq : p ≠ q) (hX : X * X = (p + q) • X - (p * q) • 1) :
    proj X p q * proj X p q = proj X p q := by
  have h1 := proj_add X p q hpq
  have h2 := proj_mul_other X p q hpq hX
  calc proj X p q * proj X p q = proj X p q * (1 - proj X q p) := by rw [← h1]; abel_nf
    _ = proj X p q := by rw [mul_sub, mul_one, h2, sub_zero]

/-- Sign projector `½(Q + (σ/E) H Q)`. -/
def signProj (H Q : A) (E : ℂ) (σ : ℂ) : A := (1 / 2 : ℂ) • (Q + (σ / E) • (H * Q))

lemma H_signProj (H Q : A) (E σ : ℂ) (hE : E ≠ 0) (hσ : σ * σ = 1)
    (hsq : H * H * Q = (E * E) • Q) :
    H * signProj H Q E σ = (σ * E) • signProj H Q E σ := by
  simp only [signProj, mul_smul_comm, mul_add, smul_add, smul_smul]
  rw [← mul_assoc, hsq, smul_smul]
  have e1 : (1 / 2 : ℂ) * (σ / E) * (E * E) = σ * E * (1 / 2) := by field_simp
  have e2 : σ * E * (1 / 2 * (σ / E)) = (1 / 2 : ℂ) := by
    rw [show σ * E * (1 / 2 * (σ / E)) = (σ * σ) / 2 by field_simp, hσ]
  rw [e1, e2]; abel


lemma signProj_mul (H Q : A) (E σ τ : ℂ) (hE : E ≠ 0) (hHQ : H * Q = Q * H) (hQ : Q * Q = Q)
    (hsq : H * H * Q = (E * E) • Q) :
    signProj H Q E σ * signProj H Q E τ =
      (1 / 4 : ℂ) • ((1 + σ * τ) • Q + (σ / E + τ / E) • (H * Q)) := by
  have hQHQ : Q * (H * Q) = H * Q := by rw [← mul_assoc, ← hHQ, mul_assoc, hQ]
  have hHQQ : H * Q * Q = H * Q := by rw [mul_assoc, hQ]
  have hHQHQ : H * Q * (H * Q) = (E * E) • Q := by
    rw [mul_assoc, hQHQ, ← mul_assoc, hsq]
  simp only [signProj, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hQ,
    hQHQ, hHQQ, hHQHQ, smul_smul]
  match_scalars <;> field_simp <;> ring

lemma signProj_idem (H Q : A) (E σ : ℂ) (hE : E ≠ 0) (hσ : σ * σ = 1) (hHQ : H * Q = Q * H)
    (hQ : Q * Q = Q) (hsq : H * H * Q = (E * E) • Q) :
    signProj H Q E σ * signProj H Q E σ = signProj H Q E σ := by
  rw [signProj_mul H Q E σ σ hE hHQ hQ hsq, hσ, signProj]
  rw [show (1 + 1 : ℂ) = 2 by norm_num, show σ / E + σ / E = 2 * (σ / E) by ring]
  module

lemma signProj_orth (H Q : A) (E : ℂ) (hE : E ≠ 0) (hHQ : H * Q = Q * H) (hQ : Q * Q = Q)
    (hsq : H * H * Q = (E * E) • Q) : signProj H Q E 1 * signProj H Q E (-1) = 0 := by
  rw [signProj_mul H Q E 1 (-1) hE hHQ hQ hsq]
  simp only [mul_neg, mul_one, add_neg_cancel, zero_smul, neg_div, zero_add, smul_zero]

lemma signProj_sum (H Q : A) (E : ℂ) : signProj H Q E 1 + signProj H Q E (-1) = Q := by
  simp only [signProj, neg_div, neg_smul, ← smul_add]
  rw [show Q + (1 / E) • (H * Q) + (Q + -((1 / E) • (H * Q))) = (2 : ℂ) • Q by module, smul_smul]
  norm_num

end Algebra

/-! ## The spectral decomposition -/

section Spectrum
variable (k : Fin 3 → ℝ) (δ y : ℝ)

/-- `r = √(y⁴ + 4y²δ²)`. -/
def rr : ℝ := Real.sqrt (y ^ 4 + 4 * y ^ 2 * δ ^ 2)

/-- The two roots of `X² = y² X + y²δ²`. -/
def rhoP : ℝ := (y ^ 2 + rr δ y) / 2
def rhoM : ℝ := (y ^ 2 - rr δ y) / 2

/-- Squared masses of the two branches. -/
def massSqP : ℝ := δ ^ 2 + rhoP δ y
def massSqM : ℝ := δ ^ 2 + rhoM δ y

lemma rr_pos (hy : y ≠ 0) : 0 < rr δ y := by
  unfold rr; apply Real.sqrt_pos.mpr; positivity

lemma rr_sq : rr δ y ^ 2 = y ^ 4 + 4 * y ^ 2 * δ ^ 2 := by
  unfold rr; rw [Real.sq_sqrt (by positivity)]

/-- **Masses of the two branches**: product `δ⁴` (seesaw), sum `y² + 2δ²`, both nonnegative. -/
theorem branch_masses (hy : y ≠ 0) :
    massSqP δ y * massSqM δ y = δ ^ 4 ∧ massSqP δ y + massSqM δ y = y ^ 2 + 2 * δ ^ 2 ∧
      0 < massSqP δ y ∧ 0 ≤ massSqM δ y := by
  have h2 := rr_sq δ y
  have hr := rr_pos δ y hy
  have hle : rr δ y ≤ y ^ 2 + 2 * δ ^ 2 := by
    rw [← Real.sqrt_sq (show 0 ≤ y ^ 2 + 2 * δ ^ 2 by positivity), rr]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (δ ^ 2)])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [massSqP, massSqM, rhoP, rhoM]; nlinarith
  · simp only [massSqP, massSqM, rhoP, rhoM]; ring
  · simp only [massSqP, rhoP]; positivity
  · simp only [massSqM, rhoM]; linarith

lemma X_roots :
    X k δ y * X k δ y = (((rhoP δ y : ℝ) : ℂ) + ((rhoM δ y : ℝ) : ℂ)) • X k δ y -
      (((rhoP δ y : ℝ) : ℂ) * ((rhoM δ y : ℝ) : ℂ)) • 1 := by
  rw [X_quadratic]
  have hs : rhoP δ y + rhoM δ y = y ^ 2 := by simp only [rhoP, rhoM]; ring
  have hp : rhoP δ y * rhoM δ y = -(y ^ 2 * δ ^ 2) := by
    simp only [rhoP, rhoM]; nlinarith [rr_sq δ y]
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul, hs, hp, Complex.ofReal_neg, neg_smul,
    sub_neg_eq_add]

lemma roots_ne (hy : y ≠ 0) : ((rhoP δ y : ℝ) : ℂ) ≠ ((rhoM δ y : ℝ) : ℂ) := by
  have hr := rr_pos δ y hy
  rw [Ne, Complex.ofReal_inj]; simp only [rhoP, rhoM]; intro h; linarith

lemma H_X (k : Fin 3 → ℝ) (δ y : ℝ) : Hy k δ y * X k δ y = X k δ y * Hy k δ y := by
  simp only [X, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc]

lemma S_X (k : Fin 3 → ℝ) (δ y : ℝ) : S * X k δ y = X k δ y * S := by
  have ha : S * Hy k δ y = -(Hy k δ y * S) := eq_neg_of_add_eq_zero_left (S_anticomm k δ y)
  have hsq : S * (Hy k δ y * Hy k δ y) = Hy k δ y * Hy k δ y * S := by
    rw [← mul_assoc, ha, neg_mul, mul_assoc, ha, mul_neg, neg_neg, mul_assoc]
  simp only [X, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hsq]

/-- **Odd traces vanish.** For any `Q` commuting with `S`, `tr(H Q) = 0`. -/
lemma trace_HQ (Q : Matrix Ix Ix ℂ) (hQ : S * Q = Q * S) : (Hy k δ y * Q).trace = 0 := by
  have ha : S * Hy k δ y = -(Hy k δ y * S) := eq_neg_of_add_eq_zero_left (S_anticomm k δ y)
  have h1 : S * (Hy k δ y * Q) * S = Hy k δ y * Q := by
    rw [← mul_assoc, ha, neg_mul, mul_assoc, hQ, ← mul_assoc, neg_mul,
      mul_assoc (Hy k δ y * Q) S S, S_sq]; simp
  have h2 : (S * (Hy k δ y * Q) * S).trace = -(Hy k δ y * Q).trace := by
    rw [Matrix.trace_mul_cycle, ← mul_assoc, S_sq]; simp
  rw [h1] at h2
  have : (2 : ℂ) * (Hy k δ y * Q).trace = 0 := by linear_combination h2
  simpa using this

end Spectrum

/-! ## The two Dirac particles -/

section Particles
variable (k : Fin 3 → ℝ) (δ y : ℝ)

/-- Branch projector for root `p` (other root `q`). -/
def Qb (p q : ℝ) : Matrix Ix Ix ℂ := proj (X k δ y) (p : ℂ) (q : ℂ)

/-- Branch energy `√(|k|² + δ² + p) = √(|k|² + m²)`. -/
def Eb (p : ℝ) : ℝ := Real.sqrt (msq3 k + δ ^ 2 + p)

/-- The projector onto energy `σ E_b` in branch `b`. -/
def R (p q : ℝ) (σ : ℂ) : Matrix Ix Ix ℂ :=
  signProj (Hy k δ y) (Qb k δ y p q) ((Eb k δ p : ℝ) : ℂ) σ

/-- The two roots, in either order, satisfy the quadratic. -/
def IsRoots (p q : ℝ) : Prop :=
  p ≠ q ∧ X k δ y * X k δ y = ((p : ℂ) + (q : ℂ)) • X k δ y - ((p : ℂ) * (q : ℂ)) • 1

lemma roots_PM (hy : y ≠ 0) : IsRoots k δ y (rhoP δ y) (rhoM δ y) :=
  ⟨fun h => roots_ne δ y hy (by rw [h]), X_roots k δ y⟩

lemma roots_MP (hy : y ≠ 0) : IsRoots k δ y (rhoM δ y) (rhoP δ y) := by
  refine ⟨fun h => roots_ne δ y hy (by rw [h]), ?_⟩
  rw [add_comm, mul_comm]; exact X_roots k δ y

lemma HQ_comm (p q : ℝ) : Hy k δ y * Qb k δ y p q = Qb k δ y p q * Hy k δ y := by
  simp only [Qb, proj, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, H_X, mul_one, one_mul]

lemma SQ_comm (p q : ℝ) : S * Qb k δ y p q = Qb k δ y p q * S := by
  simp only [Qb, proj, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, S_X, mul_one, one_mul]

lemma Q_idem (p q : ℝ) (h : IsRoots k δ y p q) : Qb k δ y p q * Qb k δ y p q = Qb k δ y p q :=
  proj_idem _ _ _ (fun e => h.1 (Complex.ofReal_injective e)) h.2

lemma HH_Q (p q : ℝ) (h : IsRoots k δ y p q) (hE : 0 ≤ msq3 k + δ ^ 2 + p) :
    Hy k δ y * Hy k δ y * Qb k δ y p q =
      (((Eb k δ p : ℝ) : ℂ) * ((Eb k δ p : ℝ) : ℂ)) • Qb k δ y p q := by
  have hH : Hy k δ y * Hy k δ y = X k δ y + ((msq3 k + δ ^ 2 : ℝ) : ℂ) • 1 := by
    simp [X]
  have hXQ := X_proj (X k δ y) (p : ℂ) (q : ℂ) h.2
  rw [hH, add_mul, smul_mul_assoc, one_mul]
  simp only [Qb] at *
  rw [hXQ, ← add_smul, ← Complex.ofReal_mul, Eb, Real.mul_self_sqrt hE]
  congr 1; push_cast; ring

lemma trace_Q (p q : ℝ) :
    (Qb k δ y p q).trace = (1 / ((p : ℂ) - q)) * (4 * ((y ^ 2 : ℝ) : ℂ) - 8 * q) := by
  simp only [Qb, proj, Matrix.trace_smul, Matrix.trace_sub, trace_X, Matrix.trace_one,
    smul_eq_mul]
  have h8 : ((Fintype.card Ix : ℕ) : ℂ) = 8 := by simp [Fintype.card_sum]
  rw [h8]; ring

theorem trace_QP (hy : y ≠ 0) : (Qb k δ y (rhoP δ y) (rhoM δ y)).trace = 4 := by
  have hr := rr_pos δ y hy
  rw [trace_Q k δ y]
  have hne : ((rhoP δ y : ℝ) : ℂ) - ((rhoM δ y : ℝ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (roots_ne δ y hy)
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hne]
  rw [← Complex.ofReal_sub]; simp only [rhoP, rhoM]; push_cast; ring

theorem trace_QM (hy : y ≠ 0) : (Qb k δ y (rhoM δ y) (rhoP δ y)).trace = 4 := by
  have hne : ((rhoM δ y : ℝ) : ℂ) - ((rhoP δ y : ℝ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun e => roots_ne δ y hy e.symm)
  rw [trace_Q k δ y]
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hne]
  simp only [rhoP, rhoM]; push_cast; ring

/-- **Each branch and sign.** The projector `R` satisfies `H R = σ E_b R` and `R² = R`, and its
trace is half the branch trace. -/
theorem branch_projector (p q : ℝ) (h : IsRoots k δ y p q) (hE : 0 < msq3 k + δ ^ 2 + p)
    (σ : ℂ) (hσ : σ * σ = 1) :
    Hy k δ y * R k δ y p q σ = (σ * (Eb k δ p : ℂ)) • R k δ y p q σ ∧
      R k δ y p q σ * R k δ y p q σ = R k δ y p q σ ∧
      (R k δ y p q σ).trace = (1 / 2) * (Qb k δ y p q).trace := by
  have hE0 : ((Eb k δ p : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, Eb]; exact (Real.sqrt_pos.mpr hE).ne'
  have hsq := HH_Q k δ y p q h hE.le
  refine ⟨H_signProj _ _ _ _ hE0 hσ hsq,
    signProj_idem _ _ _ _ hE0 hσ (HQ_comm k δ y p q) (Q_idem k δ y p q h) hsq, ?_⟩
  simp only [R, signProj, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul,
    trace_HQ k δ y _ (SQ_comm k δ y p q), mul_zero, add_zero]

/-- **Completeness.** The four projectors sum to the identity. -/
theorem complete (hy : y ≠ 0) :
    R k δ y (rhoP δ y) (rhoM δ y) 1 + R k δ y (rhoP δ y) (rhoM δ y) (-1) +
      (R k δ y (rhoM δ y) (rhoP δ y) 1 + R k δ y (rhoM δ y) (rhoP δ y) (-1)) = 1 := by
  simp only [R, signProj_sum, Qb]
  exact proj_add _ _ _ (roots_ne δ y hy)

/-- **Two massive Dirac particles.** For `y ≠ 0` and `|k|² + m₋² > 0`, the eight components split
into four rank-two eigenprojectors with energies `±√(|k|² + m₊²)` and `±√(|k|² + m₋²)`. -/
theorem two_dirac_particles (hy : y ≠ 0) (hM : 0 < msq3 k + massSqM δ y) :
    (∀ σ : ℂ, σ * σ = 1 →
      Hy k δ y * R k δ y (rhoP δ y) (rhoM δ y) σ =
          (σ * (Real.sqrt (msq3 k + massSqP δ y) : ℂ)) • R k δ y (rhoP δ y) (rhoM δ y) σ ∧
        (R k δ y (rhoP δ y) (rhoM δ y) σ).trace = 2) ∧
    (∀ σ : ℂ, σ * σ = 1 →
      Hy k δ y * R k δ y (rhoM δ y) (rhoP δ y) σ =
          (σ * (Real.sqrt (msq3 k + massSqM δ y) : ℂ)) • R k δ y (rhoM δ y) (rhoP δ y) σ ∧
        (R k δ y (rhoM δ y) (rhoP δ y) σ).trace = 2) := by
  have hP : 0 < msq3 k + δ ^ 2 + rhoP δ y := by
    have := (branch_masses δ y hy).2.2.1
    have h0 : 0 ≤ msq3 k := by unfold msq3; positivity
    simp only [massSqP] at this; linarith
  have hM' : 0 < msq3 k + δ ^ 2 + rhoM δ y := by simp only [massSqM] at hM; linarith
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · obtain ⟨h1, -, h3⟩ := branch_projector k δ y _ _ (roots_PM k δ y hy) hP σ hσ
    refine ⟨by simpa [Eb, massSqP, add_assoc] using h1, ?_⟩
    rw [h3, trace_QP k δ y hy]; norm_num
  · obtain ⟨h1, -, h3⟩ := branch_projector k δ y _ _ (roots_MP k δ y hy) hM' σ hσ
    refine ⟨by simpa [Eb, massSqM, add_assoc] using h1, ?_⟩
    rw [h3, trace_QM k δ y hy]; norm_num

/-- A nonzero projector has a nonzero eigen-column. -/
theorem eigenvector_of_projector (Rm : Matrix Ix Ix ℂ) (E : ℂ) (hR : Hy k δ y * Rm = E • Rm)
    (htr : Rm.trace ≠ 0) : ∃ v : Ix → ℂ, v ≠ 0 ∧ Hy k δ y *ᵥ v = E • v := by
  have hne : Rm ≠ 0 := by rintro rfl; simp at htr
  obtain ⟨j, hj⟩ : ∃ j, Rm *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Matrix.ext_of_mulVec_single fun j => by rw [hall j, zero_mulVec])
  refine ⟨Rm *ᵥ Pi.single j 1, hj, ?_⟩
  rw [mulVec_mulVec, hR, smul_mulVec]

end Particles

end PMAction.WallDispersion
