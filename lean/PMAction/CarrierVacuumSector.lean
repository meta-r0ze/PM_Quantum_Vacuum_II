import PMAction.OddCarrierPhase

/-!
# A carrier realization of the full chosen vacuum Hamiltonian

The coordinate-odd sector is intrinsic to each antipodal carrier class.
Two D4 sectors realize the eight-component vacuum model. Native operators
are specified first by root words and four orthogonal-root reconstructed phases.
Their restriction, rather than an arbitrary fitted unitary, gives the model.
Physical selection of this sector, coherent phase admission, the momentum
ansatz and coefficients remain inputs. Zero action on the even complement
is an extension convention, not a persistence theorem.
-/
noncomputable section
namespace PMAction.CarrierVacuumSector
open Matrix CarrierEvents

abbrev Labels (c : Fin 3) := Carrier c ⊕ Carrier c

def embedding (c : Fin 3) : Matrix (Labels c) ConcreteFermion.Sites ℂ :=
  fromBlocks (CarrierParity.embedding c) 0 0 (CarrierParity.embedding c)

theorem isometry (c : Fin 3) : (embedding c)ᴴ * embedding c = 1 := by
  simp [embedding, fromBlocks_conjTranspose, fromBlocks_multiply, CarrierParity.isometry,
    fromBlocks_one]

def parity (c : Fin 3) : Matrix (Labels c) (Labels c) ℂ :=
  fromBlocks ((CarrierParity.antipode c).permMatrix ℂ) 0 0
    ((CarrierParity.antipode c).permMatrix ℂ)

def oddProjector (c : Fin 3) : Matrix (Labels c) (Labels c) ℂ :=
  (1/2 : ℂ) • (1-parity c)

theorem projector (c : Fin 3) : embedding c * (embedding c)ᴴ = oddProjector c := by
  simp only [embedding, fromBlocks_conjTranspose, conjTranspose_zero,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, CarrierParity.projector]
  ext i j
  cases i <;> cases j <;> simp [oddProjector, parity, fromBlocks, Matrix.one_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]

/-- Four coordinate modes in each of two D4 sectors; the even modes are excluded. -/
theorem range_iff_odd (c : Fin 3) (ψ : Labels c → ℂ) :
    (∃ x : ConcreteFermion.Sites → ℂ, embedding c *ᵥ x = ψ) ↔
      parity c *ᵥ ψ = -ψ := by
  have he : parity c * embedding c = -(embedding c) := by
    simp [parity, embedding, fromBlocks_multiply, OddCarrierPhase.antipode_intertwining,
      fromBlocks_neg]
  constructor
  · rintro ⟨x,rfl⟩
    rw [mulVec_mulVec, he, neg_mulVec]
  · intro h
    refine ⟨(embedding c)ᴴ *ᵥ ψ, ?_⟩
    rw [mulVec_mulVec, projector]
    simp only [oddProjector, smul_mulVec, sub_mulVec, one_mulVec, h]
    module

/-- Native signed permutations, with one explicit reconstructed phase. -/
def beta (c : Fin 3) := (CarrierWeyl.lookup c 0).permMatrix ℂ
def gamma (c : Fin 3) := (CarrierWeyl.lookup c 1).permMatrix ℂ
def alpha (c : Fin 3) (p : ℝ) : Fin 3 → Matrix (Carrier c) (Carrier c) ℂ :=
  ![(CarrierWeyl.lookup c 2).permMatrix ℂ, OddCarrierPhase.alpha1 c p,
    (CarrierWeyl.lookup c 3).permMatrix ℂ]

theorem beta_intertwining (c : Fin 3) :
    beta c * CarrierParity.embedding c = CarrierParity.embedding c * ConcreteFermion.beta := by
  simpa [beta, CarrierWeyl.beta_eq] using CarrierWeyl.intertwining c 0

theorem gamma_intertwining (c : Fin 3) :
    gamma c * CarrierParity.embedding c = CarrierParity.embedding c * ConcreteFermion.gamma := by
  simpa [gamma, CarrierWeyl.gamma_eq] using CarrierWeyl.intertwining c 1

theorem alpha_intertwining (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) (j : Fin 3) :
    alpha c p j * CarrierParity.embedding c =
      CarrierParity.embedding c * ConcreteFermion.alpha j := by
  fin_cases j
  · simpa [alpha, CarrierWeyl.alpha0_eq] using CarrierWeyl.intertwining c 2
  · exact OddCarrierPhase.alpha1_intertwining c p hp hp1
  · simpa [alpha, CarrierWeyl.alpha2_eq] using CarrierWeyl.intertwining c 3

/-- The full raw block Hamiltonian uses the native operators, before restriction. -/
def rawHamiltonian (c : Fin 3) (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :=
  DomainWallSpectrum.H (DomainWallSpectrum.momentum (alpha c p) k) (beta c) (gamma c) δ

private lemma h_intertwines {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (E : Matrix n m ℂ)
    (K B G : Matrix n n ℂ) (K' B' G' : Matrix m m ℂ)
    (hK : K*E=E*K') (hB : B*E=E*B') (hG : G*E=E*G') (δ : ℝ) :
    DomainWallSpectrum.H K B G δ * fromBlocks E 0 0 E =
      fromBlocks E 0 0 E * DomainWallSpectrum.H K' B' G' δ := by
  have hp : DomainWallSpectrum.plus G * E = E * DomainWallSpectrum.plus G' := by
    simp [DomainWallSpectrum.plus, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, hG]
  have hm : DomainWallSpectrum.minus G * E = E * DomainWallSpectrum.minus G' := by
    simp [DomainWallSpectrum.minus, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, hG]
  simp only [DomainWallSpectrum.H, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  congr 1
  · simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hK, hB]
  · simp only [DomainWallSpectrum.hop, Matrix.neg_mul, Matrix.mul_neg]
    rw [Matrix.mul_assoc, hp, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
  · simp only [DomainWallSpectrum.back, Matrix.neg_mul, Matrix.mul_neg]
    rw [Matrix.mul_assoc, hm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
  · simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hK, hB]

/-- All momenta and detunings, including both wall couplings, not just a reference walk. -/
theorem full_intertwining (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    rawHamiltonian c p k δ * embedding c = embedding c * ConcreteFermion.hamiltonian k δ := by
  apply h_intertwines
  · simp only [DomainWallSpectrum.momentum, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, alpha_intertwining c p hp hp1]
  · exact beta_intertwining c
  · exact gamma_intertwining c

/-- Intrinsic odd restriction; no claim that the raw even-sector operator is Hermitian. -/
def hamiltonian (c : Fin 3) (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :=
  oddProjector c * rawHamiltonian c p k δ * oddProjector c

/-- The isometric conjugation is a consequence of the root/phase construction. -/
theorem identification (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    hamiltonian c p k δ = embedding c * ConcreteFermion.hamiltonian k δ * (embedding c)ᴴ := by
  unfold hamiltonian
  rw [← projector, Matrix.mul_assoc, ← Matrix.mul_assoc (rawHamiltonian c p k δ),
    full_intertwining c p hp hp1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (embedding c) (embedding c)ᴴ, isometry, Matrix.mul_one]

theorem hermitian (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) : (hamiltonian c p k δ).IsHermitian := by
  rw [identification c p hp hp1]
  exact Matrix.isHermitian_mul_mul_conjTranspose (embedding c)
    (ConcreteFermion.hamiltonian_hermitian k δ)

end PMAction.CarrierVacuumSector
