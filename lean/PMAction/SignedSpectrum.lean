import PMAction.ConcreteSpectrum

/-! Signed characteristic polynomial for the specified two-wall Hamiltonian. -/
noncomputable section
namespace PMAction.SignedSpectrum
open Matrix Polynomial ConcreteFermion

/-- Real symplectic spin matrix; transpose, rather than adjoint, is intentional. -/
def spinPair : Spin := !![0,1,0,0; -1,0,0,0; 0,0,0,-1; 0,0,1,0]
def pair : Matrix Sites Sites ℂ := fromBlocks spinPair 0 0 spinPair

theorem pair_square : pair*pair = -1 := by
  have hs : spinPair*spinPair = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [spinPair, mul_apply, Fin.sum_univ_four]
  simp only [pair, fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add, hs]
  rw [← neg_zero, ← fromBlocks_neg, fromBlocks_one]

set_option maxHeartbeats 2000000 in
/-- Transpose pairing implies equal algebraic multiplicities at E and -E. -/
theorem pairing (k : Fin 3 → ℝ) (δ : ℝ) :
    pair*(hamiltonian k δ)ᵀ = -(hamiltonian k δ)*pair := by
  ext x y
  cases x with
  | inl i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;>
        simp [pair, spinPair, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, alpha, beta, gamma, mul_apply, vecMul, dotProduct, transpose_apply,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three] <;> ring
    | inr j => fin_cases i <;> fin_cases j <;>
        norm_num [pair, spinPair, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, alpha, beta, gamma, mul_apply, vecMul, dotProduct, transpose_apply,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]
  | inr i => cases y with
    | inl j => fin_cases i <;> fin_cases j <;>
        norm_num [pair, spinPair, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, alpha, beta, gamma, mul_apply, vecMul, dotProduct, transpose_apply,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]
    | inr j => fin_cases i <;> fin_cases j <;>
        simp [pair, spinPair, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
          DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
          DomainWallSpectrum.minus, alpha, beta, gamma, mul_apply, vecMul, dotProduct, transpose_apply,
          Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three] <;> ring

theorem neg_charpoly (k : Fin 3 → ℝ) (δ : ℝ) :
    (-hamiltonian k δ).charpoly = (hamiltonian k δ).charpoly := by
  have h := charpoly_mul_comm (pair*(hamiltonian k δ)ᵀ) (-pair)
  have hleft : (pair*(hamiltonian k δ)ᵀ)*(-pair) = -hamiltonian k δ := by
    rw [pairing]
    simp only [mul_neg, neg_mul, neg_neg]
    rw [mul_assoc, pair_square, mul_neg_one]
  have hright : (-pair)*(pair*(hamiltonian k δ)ᵀ) = (hamiltonian k δ)ᵀ := by
    rw [← mul_assoc, neg_mul, pair_square, neg_neg, one_mul]
  rw [hleft, hright, charpoly_transpose] at h
  exact h

/-- Generic determinant identity linking a matrix and its square. -/
lemma square_charpoly_identity {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    A.charpoly * (-A).charpoly = (A*A).charpoly.comp (X^2) := by
  let f : ℂ[X] →+* ℂ[X] := compRingHom (X^2)
  have hc : f.mapMatrix (A*A).charmatrix = A.charmatrix * (-A).charmatrix := by
    have hf : f.mapMatrix (A*A).charmatrix =
        scalar n (X^2) - C.mapMatrix (A*A) := by
      apply Matrix.ext; intro i j
      by_cases h : i=j
      · subst j; simp [f, charmatrix_apply, scalar_apply, -Matrix.map_mul]
      · simp [f, charmatrix_apply, scalar_apply, h, -Matrix.map_mul]
    rw [hf]
    simp only [charmatrix, map_neg, sub_neg_eq_add]
    rw [mul_add, sub_mul, sub_mul]
    have hcomm := scalar_comm (n := n) X (Commute.all _) (C.mapMatrix A)
    rw [hcomm]
    simp only [← map_mul, ← map_pow, pow_two]
    abel
  change _ = f (A*A).charmatrix.det
  rw [RingHom.map_det, hc, det_mul]
  rfl

/-- Exact signed characteristic polynomial, including the zero-energy case. -/
theorem signed_charpoly (k : Fin 3 → ℝ) (δ : ℝ) :
    (hamiltonian k δ).charpoly =
      (X^2-C ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ))^2 *
      (X^2-C ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ))^2 := by
  let a : ℂ := ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ)
  let b : ℂ := ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ)
  let q : ℂ[X] := (X^2-C a)^2*(X^2-C b)^2
  have hq : q.Monic := ((monic_X_pow_sub_C a (by decide : 2 ≠ 0)).pow 2).mul
    ((monic_X_pow_sub_C b (by decide : 2 ≠ 0)).pow 2)
  have hs : (hamiltonian k δ).charpoly^2 = q^2 := by
    rw [pow_two]
    nth_rw 2 [← neg_charpoly k δ]
    rw [square_charpoly_identity, ConcreteSpectrum.square_charpoly]
    simp only [mul_comp, pow_comp, sub_comp, X_comp, C_comp]
    change (X^2-C a)^4*(X^2-C b)^4 = q^2
    dsimp [q]; ring
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · exact h
  · have hc := congrArg Polynomial.leadingCoeff h
    rw [(hamiltonian k δ).charpoly_monic.leadingCoeff, leadingCoeff_neg, hq.leadingCoeff] at hc
    norm_num at hc

lemma quadratic_multiplicity (a b e : ℂ) (he : e^2=a) (hne : e ≠ 0) (hab : a ≠ b) :
    ((X^2-C a)^2*(X^2-C b)^2).rootMultiplicity e = 2 := by
  let p : ℂ[X] := (X-C (-e))^2*(X^2-C b)^2
  have hp : p.Monic := ((monic_X_sub_C (-e)).pow 2).mul
    ((monic_X_pow_sub_C b (by decide : 2 ≠ 0)).pow 2)
  have hf : (X^2-C a)^2*(X^2-C b)^2 = p*(X-C e)^2 := by
    rw [← he, map_pow]
    dsimp [p]; simp only [map_neg]; ring
  have heneg : e ≠ -e := by
    intro h
    apply hne
    linear_combination h/2
  rw [hf, rootMultiplicity_mul_X_sub_C_pow hp.ne_zero]
  have hz : p.rootMultiplicity e = 0 :=
    rootMultiplicity_eq_zero (by simp [p, IsRoot, sub_eq_zero, he, heneg, hab, hne])
  rw [hz]

def lightEnergy (k : Fin 3 → ℝ) (δ : ℝ) : ℝ :=
  Real.sqrt (DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2)
def heavyEnergy (k : Fin 3 → ℝ) (δ : ℝ) : ℝ :=
  Real.sqrt (DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2)

lemma kinetic_nonneg (k : Fin 3 → ℝ) : 0 ≤ DomainWallSpectrum.kineticNorm k := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Positive and negative energies on either nonzero branch each occur twice. -/
theorem signed_multiplicity (k : Fin 3 → ℝ) (δ e : ℝ) (he : e ≠ 0)
    (hbranch : e^2=DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 ∨
      e^2=DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2) :
    (hamiltonian k δ).charpoly.rootMultiplicity (e : ℂ) = 2 := by
  rw [signed_charpoly]
  have hd := ne_of_lt (ConcreteSpectrum.branches_distinct (DomainWallSpectrum.kineticNorm k) δ)
  have hdc : ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ) ≠
      ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ) :=
    fun h => hd (Complex.ofReal_injective h)
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he
  rcases hbranch with h | h
  · exact quadratic_multiplicity _ _ _ (by exact_mod_cast h) hec hdc
  · rw [mul_comm]
    exact quadratic_multiplicity _ _ _ (by exact_mod_cast h) hec (Ne.symm hdc)

/-- Heavy energy is always positive; the light branch may meet zero. -/
theorem energy_order (k : Fin 3 → ℝ) (δ : ℝ) :
    0 ≤ lightEnergy k δ ∧ lightEnergy k δ < heavyEnergy k δ := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  exact Real.sqrt_lt_sqrt (add_nonneg (kinetic_nonneg k) (sq_nonneg _))
    (ConcreteSpectrum.branches_distinct _ _)

/-- At the origin there are four zero roots, two +1 roots and two -1 roots. -/
theorem origin_charpoly : (hamiltonian 0 0).charpoly = X^4*(X-1)^2*(X+1)^2 := by
  rw [signed_charpoly]
  simp [DomainWallSpectrum.kineticNorm, DetuningMass.light_mass_zero]
  ring

end PMAction.SignedSpectrum
