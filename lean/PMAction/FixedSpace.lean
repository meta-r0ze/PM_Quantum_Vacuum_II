import PMAction.LinkEvolution
import PMAction.DomainWall

/-! Full-vector phase-alias exclusion for a supplied finite Hermitian generator.
The bandwidth assumption applies to every eigenvalue. It is not a statement
about a noncommuting split product with the same first derivative. -/
noncomputable section
namespace PMAction.FixedSpace
open Matrix HermitianTransport LinkExpansion
variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}

lemma left_diagonalize (h : H.IsHermitian) (D : Matrix n n ℂ) :
    (basis h)ᴴ * (basis h * D * (basis h)ᴴ) = D * (basis h)ᴴ := by
  simp only [← Matrix.mul_assoc, basis_left, one_mul]

/-- The exact exponential has precisely the Hamiltonian kernel when no
nonzero eigenenergy can wind once around the phase circle in one tick. -/
theorem exponential_fixed_iff (h : H.IsHermitian) (τ : ℝ) (hτ : τ ≠ 0)
    (hb : ∀ i, |τ * h.eigenvalues i| < 2 * Real.pi) (v : n → ℂ) :
    NormedSpace.exp ((((-τ : ℝ) : ℂ) * Complex.I) • H) *ᵥ v = v ↔ H *ᵥ v = 0 := by
  rw [← LinkEvolution.transport_eq_exp h (-τ)]
  let c := (basis h)ᴴ *ᵥ v
  have recon : basis h *ᵥ c = v := by
    simp only [c, mulVec_mulVec, basis_right, one_mulVec]
  have ht : (basis h)ᴴ * transport h (-τ) = phaseDiag h.eigenvalues (-τ) * (basis h)ᴴ :=
    left_diagonalize h _
  have hg : (basis h)ᴴ * H = genDiag h.eigenvalues * (basis h)ᴴ := by
    calc
      (basis h)ᴴ * H = (basis h)ᴴ * (basis h * genDiag h.eigenvalues * (basis h)ᴴ) :=
        congrArg (fun A => (basis h)ᴴ * A) (generated h)
      _ = _ := left_diagonalize h _
  constructor
  · intro hf
    have hc : phaseDiag h.eigenvalues (-τ) *ᵥ c = c := by
      have hh := congrArg (fun w => (basis h)ᴴ *ᵥ w) hf
      simpa only [mulVec_mulVec, ht, c] using hh
    have hz : genDiag h.eigenvalues *ᵥ c = 0 := by
      ext i
      simp only [genDiag, mulVec_diagonal, Pi.zero_apply]
      by_cases hi : c i = 0
      · simp [hi]
      · have he := congrFun hc i
        simp only [phaseDiag, mulVec_diagonal] at he
        have hp : (Complex.exp (((-τ * h.eigenvalues i : ℝ) : ℂ) * Complex.I) - 1) * c i = 0 := by
          linear_combination he
        have he1 := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hi)
        have he0 : h.eigenvalues i = 0 :=
          DomainWall.update_zero_mode hτ (hb i) (by simpa only [neg_mul, Complex.ofReal_neg] using he1)
        simp [he0]
    calc
      H *ᵥ v = (basis h * genDiag h.eigenvalues * (basis h)ᴴ) *ᵥ v :=
        congrArg (fun A => A *ᵥ v) (generated h)
      _ = basis h *ᵥ (genDiag h.eigenvalues *ᵥ c) := by simp only [← mulVec_mulVec, c]
      _ = 0 := by rw [hz, mulVec_zero]
  · intro hf
    have hc : genDiag h.eigenvalues *ᵥ c = 0 := by
      have hh := congrArg (fun w => (basis h)ᴴ *ᵥ w) hf
      simpa only [mulVec_mulVec, hg, mulVec_zero, c] using hh
    have he : phaseDiag h.eigenvalues (-τ) *ᵥ c = c := by
      ext i
      have hi := congrFun hc i
      simp only [genDiag, mulVec_diagonal, Pi.zero_apply] at hi
      simp only [phaseDiag, mulVec_diagonal]
      rcases mul_eq_zero.mp hi with hi | hi
      · have hz : h.eigenvalues i = 0 := by exact_mod_cast hi
        simp [hz]
      · simp [hi]
    change (basis h * phaseDiag h.eigenvalues (-τ) * (basis h)ᴴ) *ᵥ v = v
    simp only [← mulVec_mulVec]
    change basis h *ᵥ (phaseDiag h.eigenvalues (-τ) *ᵥ c) = v
    rw [he]
    exact recon

end PMAction.FixedSpace
