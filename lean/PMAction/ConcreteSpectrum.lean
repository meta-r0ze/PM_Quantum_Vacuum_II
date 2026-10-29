import PMAction.ConcreteFermion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Characteristic polynomial of the concrete squared two-wall Hamiltonian.
Four coordinate-pair blocks establish occurrence, not only allowed roots. -/
noncomputable section
namespace PMAction.ConcreteSpectrum
open Matrix Polynomial
open ConcreteFermion

def pairIndex : Sites ≃ Fin 2 × Fin 4 where
  toFun := Sum.elim (fun i => (0,i)) (fun i => (1,i))
  invFun p := if p.1=0 then .inl p.2 else .inr p.2
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨i,j⟩; fin_cases i <;> rfl

def block (s δ : ℝ) (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i.val<2 then
    !![(s+δ^2 : ℝ), -δ; -δ, (s+δ^2+1 : ℝ)]
  else !![(s+δ^2+1 : ℝ), -δ; -δ, (s+δ^2 : ℝ)]

/-- Reorder left/right sector coordinates into four two-coordinate pairs. -/
theorem square_blocks (k : Fin 3 → ℝ) (δ : ℝ) :
    reindex pairIndex pairIndex (hamiltonian k δ*hamiltonian k δ) =
      blockDiagonal (block (DomainWallSpectrum.kineticNorm k) δ) := by
  have hk := DomainWallSpectrum.kinetic_relations alpha beta gamma k clifford alpha_gamma
  rw [hamiltonian, DomainWallSpectrum.hamiltonian_square _ _ _ _ _ beta_square gamma_square
    beta_gamma hk.1 hk.2.1 hk.2.2]
  ext x y
  rcases x with ⟨a,i⟩
  rcases y with ⟨b,j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [reindex, pairIndex, blockDiagonal, block, fromBlocks,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma]

lemma blockDiagonal_charpoly (B : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    (blockDiagonal B).charpoly=∏ i, (B i).charpoly := by
  have hc : (blockDiagonal B).charmatrix=blockDiagonal (fun i => (B i).charmatrix) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hab : a=b
    · subst b
      by_cases hij : i=j
      · subst j; simp [blockDiagonal_apply]
      · simp [blockDiagonal_apply, hij]
    · have hp : (i,a) ≠ (j,b) := fun h => hab (congrArg Prod.snd h)
      simp [blockDiagonal_apply, hab, hp]
  unfold Matrix.charpoly
  rw [hc, det_blockDiagonal]

/-- Both blocks have the same characteristic polynomial. -/
theorem block_polynomial (s δ : ℝ) (i : Fin 4) :
    (block s δ i).charpoly =
      (X-C ((s+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ))*
      (X-C ((s+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ)) := by
  have hd : δ^2=(DetuningMass.lightMass δ)^2+DetuningMass.lightMass δ := by
    nlinarith [DetuningMass.mass_relation δ]
  rw [charpoly_fin_two]
  have ht : (block s δ i).trace = ((s+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ)+
      ((s+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ) := by
    have hreal₁ : s+δ^2+(s+δ^2+1) =
        (s+(DetuningMass.lightMass δ)^2)+(s+(DetuningMass.lightMass δ+1)^2) := by
      nlinarith [DetuningMass.mass_relation δ]
    have hreal₂ : s+δ^2+1+(s+δ^2) =
        (s+(DetuningMass.lightMass δ)^2)+(s+(DetuningMass.lightMass δ+1)^2) := by
      nlinarith [DetuningMass.mass_relation δ]
    unfold block
    split_ifs <;> simp [trace, Fin.sum_univ_two]
    · exact_mod_cast hreal₁
    · exact_mod_cast hreal₂
  have hdet : (block s δ i).det =
      ((s+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ)*
      ((s+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ) := by
    have hreal : (s+δ^2)*(s+δ^2+1)-δ*δ =
        (s+(DetuningMass.lightMass δ)^2)*(s+(DetuningMass.lightMass δ+1)^2) := by
      calc
        _ = (s+δ^2)*(s+δ^2+1)-δ^2 := by ring
        _ = _ := by rw [hd]; ring
    unfold block
    split_ifs <;> simp [det_fin_two]
    · exact_mod_cast hreal
    · exact_mod_cast (by nlinarith [hreal] :
        (s+δ^2+1)*(s+δ^2)-δ*δ =
        (s+(DetuningMass.lightMass δ)^2)*(s+(DetuningMass.lightMass δ+1)^2))
  rw [ht,hdet,map_add,map_mul]
  ring

/-- Both squared-energy branches occur, each with algebraic multiplicity four. -/
theorem square_charpoly (k : Fin 3 → ℝ) (δ : ℝ) :
    (hamiltonian k δ*hamiltonian k δ).charpoly =
      (X-C ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ))^4 *
      (X-C ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ))^4 := by
  rw [← charpoly_reindex pairIndex, square_blocks, blockDiagonal_charpoly]
  simp_rw [block_polynomial]
  simp [mul_pow]

theorem branches_distinct (s δ : ℝ) :
    (s+(DetuningMass.lightMass δ)^2 : ℝ) < s+(DetuningMass.lightMass δ+1)^2 := by
  have hm := (DetuningMass.mass_le δ).1
  nlinarith

/-- Root multiplicity here is the algebraic multiplicity of H², not signed H. -/
theorem square_branch_multiplicities (k : Fin 3 → ℝ) (δ : ℝ) :
    (hamiltonian k δ*hamiltonian k δ).charpoly.rootMultiplicity
      ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ) = 4 ∧
    (hamiltonian k δ*hamiltonian k δ).charpoly.rootMultiplicity
      ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ) = 4 := by
  let a : ℂ := ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 : ℝ) : ℂ)
  let b : ℂ := ((DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 : ℝ) : ℂ)
  have hab : a ≠ b := by
    intro h
    have hr := Complex.ofReal_injective h
    exact (ne_of_lt (branches_distinct (DomainWallSpectrum.kineticNorm k) δ)) hr
  change (hamiltonian k δ*hamiltonian k δ).charpoly.rootMultiplicity a = 4 ∧
    (hamiltonian k δ*hamiltonian k δ).charpoly.rootMultiplicity b = 4
  rw [square_charpoly]
  change (((X-C a)^4)*((X-C b)^4)).rootMultiplicity a = 4 ∧
    (((X-C a)^4)*((X-C b)^4)).rootMultiplicity b = 4
  constructor
  · rw [mul_comm, rootMultiplicity_mul_X_sub_C_pow (pow_ne_zero 4 (X_sub_C_ne_zero b))]
    have hz : ((X-C b)^4).rootMultiplicity a = 0 :=
      rootMultiplicity_eq_zero (by simp [IsRoot, sub_eq_zero, hab])
    rw [hz]
  · rw [rootMultiplicity_mul_X_sub_C_pow (pow_ne_zero 4 (X_sub_C_ne_zero a))]
    have hz : ((X-C a)^4).rootMultiplicity b = 0 :=
      rootMultiplicity_eq_zero (by simp [IsRoot, sub_eq_zero, Ne.symm hab])
    rw [hz]

end PMAction.ConcreteSpectrum
