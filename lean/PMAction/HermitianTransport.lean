import PMAction.LinkExpansion
import Mathlib.Analysis.Matrix.Spectrum

/-! Spectral transport and a controlled quadratic response for any supplied finite
Hermitian generator. No field representation, physical scale or clock is selected.
Extracted from Paper III so later papers can use it without a downstream dependency. -/
noncomputable section
namespace PMAction.HermitianTransport
open Matrix Finset PMAction PMAction.LinkExpansion
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Matrix n n ℂ}

def basis (h : H.IsHermitian) : Matrix n n ℂ := h.eigenvectorUnitary

lemma basis_left (h : H.IsHermitian) : (basis h)ᴴ*basis h=1 := by
  exact Unitary.coe_star_mul_self h.eigenvectorUnitary

lemma basis_right (h : H.IsHermitian) : basis h*(basis h)ᴴ=1 := by
  exact Unitary.coe_mul_star_self h.eigenvectorUnitary

lemma generated (h : H.IsHermitian) : H=basis h*genDiag h.eigenvalues*(basis h)ᴴ := by
  simpa [basis,genDiag,Function.comp_def,Matrix.star_eq_conjTranspose] using h.spectral_theorem

def transport (h : H.IsHermitian) (ε : ℝ) : Matrix n n ℂ :=
  basis h*phaseDiag h.eigenvalues ε*(basis h)ᴴ

lemma diagonal_unitary (lam : n → ℝ) (ε : ℝ) :
    phaseDiag lam ε ∈ unitary (Matrix n n ℂ) := by
  have hp : ∀ x : ℝ, star (Complex.exp ((x : ℂ)*Complex.I))*
      Complex.exp ((x : ℂ)*Complex.I)=1 := by
    intro x
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  constructor
  · change (phaseDiag lam ε)ᴴ*phaseDiag lam ε=1
    simp only [phaseDiag,diagonal_conjTranspose,diagonal_mul_diagonal]
    change diagonal (fun k => star (Complex.exp (((ε*lam k : ℝ) : ℂ)*Complex.I))*
      Complex.exp (((ε*lam k : ℝ) : ℂ)*Complex.I))=1
    simp only [hp,diagonal_one]
  · change phaseDiag lam ε*(phaseDiag lam ε)ᴴ=1
    simp only [phaseDiag,diagonal_conjTranspose,diagonal_mul_diagonal]
    change diagonal (fun k => Complex.exp (((ε*lam k : ℝ) : ℂ)*Complex.I)*
      star (Complex.exp (((ε*lam k : ℝ) : ℂ)*Complex.I)))=1
    have hh : ∀ x : ℝ, Complex.exp ((x : ℂ)*Complex.I)*
        star (Complex.exp ((x : ℂ)*Complex.I))=1 := fun x => by rw [mul_comm]; exact hp x
    simp only [hh,diagonal_one]

theorem transport_unitary (h : H.IsHermitian) (ε : ℝ) :
    transport h ε ∈ unitary (Matrix n n ℂ) := by
  have hv : basis h ∈ unitary (Matrix n n ℂ) := h.eigenvectorUnitary.prop
  exact (unitary _).mul_mem ((unitary _).mul_mem hv (diagonal_unitary _ ε)) (Unitary.star_mem hv)

theorem transport_zero (h : H.IsHermitian) : transport h 0=1 := by
  simp only [transport,phaseDiag,zero_mul,Complex.ofReal_zero,Complex.exp_zero,
    diagonal_one,mul_one]
  exact basis_right h

def radius (h : H.IsHermitian) : ℝ := 1/(1+∑ k, |h.eigenvalues k|)

theorem radius_pos (h : H.IsHermitian) : 0 < radius h := by
  have hs : 0 ≤ ∑ k, |h.eigenvalues k| := sum_nonneg (fun _ _ => abs_nonneg _)
  unfold radius; positivity

theorem small_eigenphases (h : H.IsHermitian) {ε : ℝ} (he : |ε| ≤ radius h) :
    ∀ k, |ε*h.eigenvalues k| ≤ 1 := by
  have hs : 0 ≤ ∑ k, |h.eigenvalues k| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hd : 0 < 1+∑ k, |h.eigenvalues k| := by linarith
  have he' : |ε| *(1+∑ k, |h.eigenvalues k|) ≤ 1 := (le_div_iff₀ hd).mp he
  intro k
  have hk : |h.eigenvalues k| ≤ ∑ j, |h.eigenvalues j| :=
    single_le_sum (fun j _ => abs_nonneg (h.eigenvalues j)) (mem_univ k)
  rw [abs_mul]
  nlinarith [abs_nonneg ε, mul_le_mul_of_nonneg_left hk (abs_nonneg ε)]

def coefficient (h : H.IsHermitian) (φ : n → ℂ) : ℝ :=
  5/48*∑ k, Complex.normSq (((basis h)ᴴ*ᵥφ) k)*h.eigenvalues k^4

theorem coefficient_nonneg (h : H.IsHermitian) (φ : n → ℂ) : 0 ≤ coefficient h φ := by
  unfold coefficient
  exact mul_nonneg (by norm_num) (sum_nonneg (fun k _ =>
    mul_nonneg (Complex.normSq_nonneg _) (by positivity)))

/-- Every Hermitian generator has a spectral unitary transport with a positive,
explicit small-step radius and a fourth-order error coefficient. -/
theorem controlled_response (h : H.IsHermitian) (φ : n → ℂ) {ε : ℝ}
    (he : |ε| ≤ radius h) :
    |CommonResponse.nsq (φ-transport h ε*ᵥφ)-ε^2*CommonResponse.nsq (H*ᵥφ)| ≤
      coefficient h φ*ε^4 := by
  have hb := link_expansion (basis h) (basis_left h) (basis_right h)
    h.eigenvalues ε φ (small_eigenphases h he)
  have hn : CommonResponse.nsq ((basis h*genDiag h.eigenvalues*(basis h)ᴴ)*ᵥφ)=
      CommonResponse.nsq (H*ᵥφ) := congrArg (fun M => CommonResponse.nsq (M*ᵥφ)) (generated h).symm
  rw [hn] at hb
  simpa only [transport,coefficient,mul_assoc,mul_comm,mul_left_comm] using hb

end PMAction.HermitianTransport
