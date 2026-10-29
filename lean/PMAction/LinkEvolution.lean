import PMAction.HermitianTransport
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Spectral link transport is the basis-independent matrix exponential and
forms a one-parameter unitary evolution for a fixed Hermitian generator.
This does not select that generator or a physical clock/repair protocol. -/
noncomputable section
namespace PMAction.LinkEvolution
open Matrix PMAction.LinkExpansion PMAction.HermitianTransport
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma phase_add (lam : n → ℝ) (s t : ℝ) :
    phaseDiag lam s*phaseDiag lam t=phaseDiag lam (s+t) := by
  simp only [phaseDiag,diagonal_mul_diagonal]
  congr 1; funext k
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conjugate_mul (V D E : Matrix n n ℂ) (hV : Vᴴ*V=1) :
    (V*D*Vᴴ)*(V*E*Vᴴ)=V*(D*E)*Vᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V (E*Vᴴ),hV,one_mul]

/-- Exponentiating a real diagonal generator gives its phase diagonal. -/
lemma diagonal_exponential (lam : n → ℝ) (t : ℝ) :
    NormedSpace.exp (((t : ℂ)*Complex.I) • genDiag lam)=phaseDiag lam t := by
  rw [genDiag, ← diagonal_smul, Matrix.exp_diagonal]
  apply congrArg diagonal
  funext k
  rw [Pi.coe_exp]
  change NormedSpace.exp (((t : ℂ)*Complex.I)*(lam k : ℂ))=
    Complex.exp (((t*lam k : ℝ) : ℂ)*Complex.I)
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

/-- Every unitary diagonalization of the same generator yields the same matrix
exponential; no preferred basis is a physical premise. -/
theorem diagonalization_exponential (V : Matrix n n ℂ) (lam : n → ℝ)
    (hV1 : Vᴴ*V=1) (hV2 : V*Vᴴ=1) (t : ℝ) :
    NormedSpace.exp (((t : ℂ)*Complex.I) • (V*genDiag lam*Vᴴ))=
      V*phaseDiag lam t*Vᴴ := by
  let U : unitary (Matrix n n ℂ) := ⟨V, hV1,hV2⟩
  have hu : ((Unitary.toUnits U : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)=V := rfl
  have hi : (((Unitary.toUnits U)⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)=Vᴴ := rfl
  have hs : ((t : ℂ)*Complex.I) • (V*genDiag lam*Vᴴ)=
      V*(((t : ℂ)*Complex.I) • genDiag lam)*Vᴴ := by
    simp only [smul_mul_assoc,mul_smul_comm]
  rw [hs]
  have he := Matrix.exp_units_conj (Unitary.toUnits U) (((t : ℂ)*Complex.I) • genDiag lam)
  simpa only [hu,hi,diagonal_exponential] using he

variable {H : Matrix n n ℂ}

theorem transport_eq_exp (h : H.IsHermitian) (t : ℝ) :
    transport h t=NormedSpace.exp (((t : ℂ)*Complex.I) • H) := by
  have he := diagonalization_exponential (basis h) h.eigenvalues (basis_left h) (basis_right h) t
  rw [← generated h] at he
  exact he.symm

theorem basis_independent (h : H.IsHermitian) (V : Matrix n n ℂ) (lam : n → ℝ)
    (hV1 : Vᴴ*V=1) (hV2 : V*Vᴴ=1) (hH : H=V*genDiag lam*Vᴴ) (t : ℝ) :
    V*phaseDiag lam t*Vᴴ=transport h t := by
  rw [transport_eq_exp,hH]
  exact (diagonalization_exponential V lam hV1 hV2 t).symm

/-- Composition holds for a fixed generator, including at finite step size.
It does not assert commutation of links with distinct generators. -/
theorem transport_add (h : H.IsHermitian) (s t : ℝ) :
    transport h (s+t)=transport h s*transport h t := by
  unfold transport
  rw [conjugate_mul _ _ _ (basis_left h),phase_add]

theorem transport_reverse (h : H.IsHermitian) (t : ℝ) :
    transport h (-t)=(transport h t)ᴴ := by
  have hu := transport_unitary h t
  have hu2 : transport h t*(transport h t)ᴴ=1 := hu.2
  calc
    transport h (-t)=transport h (-t)*1 := (mul_one _).symm
    _ = transport h (-t)*(transport h t*(transport h t)ᴴ) := by rw [hu2]
    _ = (transport h (-t)*transport h t)*(transport h t)ᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (transport h t)ᴴ := by rw [← transport_add,neg_add_cancel,transport_zero,one_mul]

/-- A bundled real-parameter unitary group action under addition. -/
def evolution (h : H.IsHermitian) : Multiplicative ℝ →* unitary (Matrix n n ℂ) where
  toFun t := ⟨transport h (Multiplicative.toAdd t),transport_unitary h _⟩
  map_one' := by apply Subtype.ext; exact transport_zero h
  map_mul' s t := by apply Subtype.ext; exact transport_add h _ _

end PMAction.LinkEvolution
