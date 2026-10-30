import PMAction.StateIdentification
import PMAction.ExponentialLocality

/-! Checking the unobserved sector before assigning a causal stencil to the
Hermitian exponential completion. The coefficient nilpotency used by the
finite-range Clifford split fails on even carrier amplitudes. -/
noncomputable section
namespace PMAction.NativeLocalityBoundary
open Matrix CarrierEvents
open scoped Kronecker

abbrev C := Carrier 0
abbrev L := CarrierVacuumSector.Labels 0

def uniform : C → ℂ := fun _ => 1
def uniformL : L → ℂ := Sum.elim uniform uniform

lemma perm_uniform (e : Equiv.Perm C) : e.permMatrix ℂ *ᵥ uniform=uniform := by
  rw [Matrix.permMatrix_mulVec]
  rfl

lemma coefficient_uniform (p : ℝ) :
    NativeSplit.coef 0 p 0 *ᵥ uniform = ((1+Complex.I)/2 : ℂ) • uniform := by
  simp only [NativeSplit.coef, CarrierVacuumSector.alpha, Matrix.cons_val_zero,
    CarrierVacuumSector.beta, add_mulVec, smul_mulVec, perm_uniform]
  module

lemma coefficientL_uniform (p : ℝ) :
    NativeSplit.coefL 0 p 0 *ᵥ uniformL = ((1+Complex.I)/2 : ℂ) • uniformL := by
  rw [NativeSplit.coefL, uniformL, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add]
  change Sum.elim (NativeSplit.coef 0 p 0 *ᵥ uniform)
    (NativeSplit.coef 0 p 0 *ᵥ uniform) = _
  rw [coefficient_uniform]
  funext v
  cases v <;> rfl

/-- The native coefficient has a nonzero second hop on an even field, whereas
its observed Clifford coefficient squares to zero. -/
theorem coefficient_square_uniform (p : ℝ) :
    (NativeSplit.coefL 0 p 0 * NativeSplit.coefL 0 p 0) *ᵥ uniformL =
      (Complex.I/2 : ℂ) • uniformL := by
  rw [← mulVec_mulVec, coefficientL_uniform, mulVec_smul, coefficientL_uniform, smul_smul]
  congr 1
  calc
    _ = (1+2*Complex.I+Complex.I*Complex.I)/4 := by ring
    _ = Complex.I/2 := by rw [Complex.I_mul_I]; ring

theorem coefficient_not_nilpotent (p : ℝ) :
    NativeSplit.coefL 0 p 0 * NativeSplit.coefL 0 p 0 ≠ 0 := by
  intro h
  have hh := coefficient_square_uniform p
  rw [h, zero_mulVec] at hh
  have hv := congrFun hh (Sum.inl ActualRootRepair.positive)
  have hi := congrArg Complex.im hv
  norm_num [uniformL, uniform] at hi

/-- Spatial second-hop block on a five-site cycle. It is isolated from all
return and reverse-hop terms. -/
lemma second_block (B : Matrix L L ℂ) (i j : L) :
    let S := (finRotate 5).permMatrix ℂ
    ((S ⊗ₖ B + Sᴴ ⊗ₖ Bᴴ) * (S ⊗ₖ B + Sᴴ ⊗ₖ Bᴴ)) (0,i) (2,j) = (B*B) i j := by
  dsimp only
  simp only [add_mul, mul_add, ← mul_kronecker_mul, Matrix.add_apply, kroneckerMap_apply]
  have h0 : (((finRotate 5).permMatrix ℂ * (finRotate 5).permMatrix ℂ) (0 : Fin 5) 2) = 1 := by
    norm_num [mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply,
      Fin.sum_univ_succ, finRotate_apply]
  have h1 : (((finRotate 5).permMatrix ℂ * ((finRotate 5).permMatrix ℂ)ᴴ) (0 : Fin 5) 2) = 0 := by
    simp [conjTranspose_permMatrix, ← permMatrix_mul]
  have h2 : ((((finRotate 5).permMatrix ℂ)ᴴ * (finRotate 5).permMatrix ℂ) (0 : Fin 5) 2) = 0 := by
    simp [conjTranspose_permMatrix, ← permMatrix_mul]
  have h3 : ((((finRotate 5).permMatrix ℂ)ᴴ * ((finRotate 5).permMatrix ℂ)ᴴ) (0 : Fin 5) 2) = 0 := by
    norm_num [conjTranspose_apply, mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Pi.single_apply, Fin.sum_univ_succ, finRotate_apply]
    decide
  rw [h0,h1,h2,h3]
  simp

theorem native_neighbor_not_involution (p : ℝ) :
    NativeSplit.neighborN 0 p (finRotate 5) 0 *
      NativeSplit.neighborN 0 p (finRotate 5) 0 ≠ 1 := by
  intro h
  apply coefficient_not_nilpotent p
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 5 × L) (Fin 5 × L) ℂ => M (0,i) (2,j)) h
  rw [NativeSplit.neighborN, second_block] at hh
  simpa [one_apply] using hh

lemma two_not_near : ¬ SplitUpdate.Near (finRotate 5) (0 : Fin 5) 2 := by
  change ¬ ((2 : Fin 5)=0 ∨ 2=finRotate 5 0 ∨ 2=(finRotate 5).symm 0)
  norm_num [finRotate_apply, finRotate_symm_apply]
  decide

/-- On the five-site cycle, the full-label directional exponential has a
nonzero distance-two matrix entry at arbitrarily small ticks. This does not
contradict finite support of its observed odd-sector update. -/
theorem arbitrarily_small_second_hop (p : ℝ) :
    ∃ i j : L, ∀ ε : ℝ, 0<ε → ∃ t : ℝ, |t|<ε ∧
      NativeSplit.directionN 0 p (finRotate 5) 0 t (0,i) (2,j) ≠ 0 := by
  have hex : ∃ i j : L, (NativeSplit.coefL 0 p 0 * NativeSplit.coefL 0 p 0) i j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply coefficient_not_nilpotent p
    ext i j
    exact hn i j
  obtain ⟨i,j,hij⟩ := hex
  let G := NativeSplit.neighborN 0 p (finRotate 5) 0
  have hg : (G*G) (0,i) (2,j) ≠ 0 := by
    simpa only [G,NativeSplit.neighborN,second_block] using hij
  have ha : ((Complex.I • G)*(Complex.I • G)) (0,i) (2,j) ≠ 0 := by
    simpa only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul, Matrix.neg_apply, ne_eq, neg_eq_zero] using hg
  refine ⟨i,j,?_⟩
  intro ε hε
  obtain ⟨t,ht,hn⟩ := ExponentialLocality.second_hop (Complex.I • G) (0,i) (2,j) ha ε hε
  have he : t • (Complex.I • G)=(Complex.I*(t : ℂ)) • G := by
    ext x y
    change (t : ℂ) * (Complex.I * G x y) = (Complex.I * (t : ℂ)) * G x y
    ring
  rw [he] at hn
  exact ⟨t,ht,hn⟩

end PMAction.NativeLocalityBoundary
