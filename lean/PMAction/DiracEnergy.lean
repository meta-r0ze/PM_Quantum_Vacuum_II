import PMAction.ConcreteFermion
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Real energies of nonzero eigenstates of the supplied first-order Clifford
Hamiltonian. This chooses no physical mass, accessible eigensector, statistics
or clock, and is not an identification of the full finite-tick wall spectrum. -/
noncomputable section
namespace PMAction.DiracEnergy
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spatial squared momentum in the first-order model. -/
def momentumSq (p : Fin 3 → ℝ) : ℝ := p 0^2+p 1^2+p 2^2

def positiveEnergy (p : Fin 3 → ℝ) (m : ℝ) : ℝ := Real.sqrt (momentumSq p+m^2)

/-- Any nonzero eigenstate of a scalar-square matrix lies on the corresponding
real energy shell. The eigenvalue is expressed with the real scalar action. -/
theorem scalar_square_shell (H : Matrix n n ℂ) (s E : ℝ) (v : n → ℂ)
    (hv : v ≠ 0) (hH : H*H=s • (1 : Matrix n n ℂ))
    (he : H *ᵥ v=E • v) : E^2=s := by
  have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ v) hH
  simp only [← mulVec_mulVec,he,mulVec_smul,smul_smul,smul_mulVec,one_mulVec] at h
  have hi : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  obtain ⟨i,hi⟩ := hi
  have hc := congrFun h i
  simp only [Pi.smul_apply,Complex.real_smul] at hc
  have hc' : ((E*E : ℝ) : ℂ)=(s : ℂ) := mul_right_cancel₀ hi hc
  have hr : E*E=s := by exact_mod_cast hc'
  nlinarith only [hr]

/-- Clifford dispersion from `Dirac` now gives the real eigenvalue shell. -/
theorem clifford_shell (α : Fin 3 → Matrix n n ℂ) (β : Matrix n n ℂ)
    (hC : Dirac.Clifford α β) (p : Fin 3 → ℝ) (m E : ℝ) (v : n → ℂ)
    (hv : v ≠ 0) (he : Dirac.H α β p m *ᵥ v=E • v) :
    E^2=momentumSq p+m^2 := by
  exact scalar_square_shell _ _ E v hv ((Dirac.dispersion_iff_clifford α β).mpr hC p m) he

/-- Positive-branch selection is an explicit hypothesis; the shell itself
also permits negative energy. -/
theorem positive_branch (α : Fin 3 → Matrix n n ℂ) (β : Matrix n n ℂ)
    (hC : Dirac.Clifford α β) (p : Fin 3 → ℝ) (m E : ℝ) (v : n → ℂ)
    (hv : v ≠ 0) (he : Dirac.H α β p m *ᵥ v=E • v) (hE : 0 ≤ E) :
    E=positiveEnergy p m := by
  rw [positiveEnergy,← clifford_shell α β hC p m E v hv he,Real.sqrt_sq hE]

/-- Specialization to Paper II's checked four-component Clifford representation. -/
theorem concrete_positive_branch (p : Fin 3 → ℝ) (m E : ℝ) (v : Fin 4 → ℂ)
    (hv : v ≠ 0) (he : Dirac.H ConcreteFermion.alpha ConcreteFermion.beta p m *ᵥ v=E • v)
    (hE : 0 ≤ E) : E=positiveEnergy p m :=
  positive_branch _ _ ConcreteFermion.clifford p m E v hv he hE

/-- A scalar-square, traceless four-component matrix has a positive-energy
eigenstate whenever E>0. The proof chooses a nonzero column of H+E I. -/
theorem positive_state_of_square_trace (H : Matrix (Fin 4) (Fin 4) ℂ) (E : ℝ)
    (hE : 0<E) (hH : H*H=E^2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (ht : H.trace=0) :
    ∃ v : Fin 4 → ℂ, v ≠ 0 ∧ H *ᵥ v=E • v := by
  let A := H+E • (1 : Matrix (Fin 4) (Fin 4) ℂ)
  have hA : A ≠ 0 := by
    intro hz
    have h := congrArg Matrix.trace hz
    have hc : ((4*E : ℝ) : ℂ)=0 := by
      simpa [A,trace_add,trace_smul,ht,Complex.real_smul] using h
    have hr : 4*E=0 := by exact_mod_cast hc
    linarith
  have hj : ∃ j : Fin 4, A *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hA
    ext i j
    have h := congrFun (hn j) i
    simpa using h
  obtain ⟨j,hj⟩ := hj
  have hprod : H*A=E • A := by
    dsimp [A]
    simp only [mul_add,mul_smul_comm,mul_one,smul_add,smul_smul,hH,pow_two]
    abel
  refine ⟨A *ᵥ Pi.single j 1,hj,?_⟩
  rw [mulVec_mulVec,hprod,smul_mulVec]

lemma concrete_trace (p : Fin 3 → ℝ) (m : ℝ) :
    (Dirac.H ConcreteFermion.alpha ConcreteFermion.beta p m).trace=0 := by
  simp [Dirac.H,ConcreteFermion.alpha,ConcreteFermion.beta,Matrix.trace,Fin.sum_univ_four]

/-- Existence is also internal mathematics: choosing the physical accessible
positive branch, masses and state preparation remains a separate identification. -/
theorem concrete_positive_state_exists (p : Fin 3 → ℝ) (m : ℝ)
    (hp : 0<momentumSq p+m^2) :
    ∃ v : Fin 4 → ℂ, v ≠ 0 ∧
      Dirac.H ConcreteFermion.alpha ConcreteFermion.beta p m *ᵥ v=positiveEnergy p m • v := by
  apply positive_state_of_square_trace _ _ (Real.sqrt_pos.mpr hp) _ (concrete_trace p m)
  rw [Real.sq_sqrt hp.le]
  exact (Dirac.dispersion_iff_clifford _ _).mpr ConcreteFermion.clifford p m

end PMAction.DiracEnergy
