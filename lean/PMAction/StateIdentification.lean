import Mathlib.LinearAlgebra.Matrix.Kronecker
import PMAction.CarrierClifford
import PMAction.CarrierReadoutQuotient
import PMAction.InvolutionSpectral
import PMAction.LocalUnitary
import PMAction.NativeCarrierProtocol
import PMAction.RealSpaceFourier
import PMAction.RectangularEvolution
import PMAction.RotationAlgebra
import PMAction.SpatialContinuum

/-!
# Native amplitude-state/readout construction

One amplitude index space, `sites × actual carrier labels`, and a supplied coordinate
readout support the spinor sector, the full corrected split update, its branches, the
reference/record streams and the tick schedule:

* `NativeObservation`: observed operators along an isometric readout; an intertwiner that
  commutes with the readout projector is automatically observed (no feedback).
* `NativeSector`: all native root-word/phase operators commute with antipodal parity; the
  Hermitian completion of the native generator is Hermitian on all sixteen labels, preserves
  parity and is observed exactly as the vacuum Hamiltonian; odd eigenvalues lie on the
  light/heavy branches and every vacuum eigenvector is realized.
* `NativeSplit`: the real-space corrected split, built from exponentials of native Hermitian
  generators, is unitary on all labels and observed as `SplitUpdate.update`; on the torus,
  stationary odd fields and spectra are those of `RealSpaceFourier`.
* `Records`: the reference protocol's live and record streams are the axis-0 and axis-1
  contrasts of the same vector-class readout; the native reference lookup is observed and
  its contrasts follow the same two-stream/exchange rule.
* `Clock`: a four-phase clock schedules the native factors; `4m` clock events are `m` ticks.

The clock uses a separate `Fin 4` register; the tick theorems assume initialization
at phase zero. Its capacity, physical phase/timing admission and primitive prices
are not derived. Neither coordinate observations nor the full amplitude model are
selected from persistence here. Hermitian completion is a construction choice;
zero even-sector action is avoided, not proved. Spatial exponentials are unitary
on all labels, but their full-label finite-range support requires a separate check.
The observed odd-sector update has the existing finite stencil.
-/

/-!
# Observed operators along an isometric readout

For an isometry `E` (`Eᴴ E = 1`), `Obs E A B` says that the large operator `A` maps the
coordinate image to itself as `B` does (`A E = E B`) and that the coordinate readout
`Eᴴ` sees `A` as `B` (`Eᴴ A = B Eᴴ`). The second condition is the derived "no-feedback"
statement: unobserved amplitudes never leak into the readout.

`of_commute` is the key reduction: an intertwiner that commutes with the projector
`E Eᴴ` is automatically observed. The class is closed under the operations used to
build updates: products, sums, scalars, adjoints, exponentials and site-local tensoring.
-/
noncomputable section
namespace PMAction.NativeObservation
open Matrix
open scoped Kronecker

variable {a b : Type*} [Fintype a] [Fintype b]

def Obs (E : Matrix a b ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ) : Prop :=
  A * E = E * B ∧ Eᴴ * A = B * Eᴴ

variable {E : Matrix a b ℂ}

theorem of_commute [DecidableEq b] (hE : Eᴴ * E = 1) {A : Matrix a a ℂ} {B : Matrix b b ℂ}
    (h : A * E = E * B) (hc : A * (E * Eᴴ) = (E * Eᴴ) * A) : Obs E A B := by
  refine ⟨h, ?_⟩
  calc Eᴴ * A = (Eᴴ * E) * Eᴴ * A := by rw [hE, Matrix.one_mul]
    _ = Eᴴ * ((E * Eᴴ) * A) := by simp only [Matrix.mul_assoc]
    _ = Eᴴ * (A * (E * Eᴴ)) := by rw [hc]
    _ = Eᴴ * (E * B) * Eᴴ := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = B * Eᴴ := by rw [← Matrix.mul_assoc, hE, Matrix.one_mul]

theorem commutes {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) :
    A * (E * Eᴴ) = (E * Eᴴ) * A := by
  rw [← Matrix.mul_assoc, h.1, Matrix.mul_assoc, ← h.2, Matrix.mul_assoc]

theorem one [DecidableEq a] [DecidableEq b] : Obs E 1 1 := ⟨by simp, by simp⟩

theorem mul {A A' : Matrix a a ℂ} {B B' : Matrix b b ℂ} (h : Obs E A B) (h' : Obs E A' B') :
    Obs E (A * A') (B * B') := by
  constructor
  · rw [Matrix.mul_assoc, h'.1, ← Matrix.mul_assoc, h.1, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, h.2, Matrix.mul_assoc, h'.2, Matrix.mul_assoc]

theorem add {A A' : Matrix a a ℂ} {B B' : Matrix b b ℂ} (h : Obs E A B) (h' : Obs E A' B') :
    Obs E (A + A') (B + B') :=
  ⟨by rw [Matrix.add_mul, Matrix.mul_add, h.1, h'.1],
   by rw [Matrix.mul_add, Matrix.add_mul, h.2, h'.2]⟩

theorem smul (z : ℂ) {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) :
    Obs E (z • A) (z • B) :=
  ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, h.1], by rw [Matrix.mul_smul, Matrix.smul_mul, h.2]⟩

theorem neg {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) : Obs E (-A) (-B) := by
  simpa using smul (-1) h

theorem sub {A A' : Matrix a a ℂ} {B B' : Matrix b b ℂ} (h : Obs E A B) (h' : Obs E A' B') :
    Obs E (A - A') (B - B') := by
  simpa [sub_eq_add_neg] using add h (neg h')

theorem pow [DecidableEq a] [DecidableEq b] {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) (m : ℕ) :
    Obs E (A ^ m) (B ^ m) := by
  induction m with
  | zero => simpa using (one : Obs E 1 1)
  | succ m ih => rw [pow_succ, pow_succ]; exact mul ih h

theorem star {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) : Obs E Aᴴ Bᴴ := by
  constructor
  · have := congrArg conjTranspose h.2
    simpa [conjTranspose_mul] using this
  · have := congrArg conjTranspose h.1
    simpa [conjTranspose_mul] using this

theorem exp [DecidableEq a] [DecidableEq b] {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) (z : ℂ) :
    Obs E (NormedSpace.exp (z • A)) (NormedSpace.exp (z • B)) := by
  constructor
  · exact RectangularEvolution.scaled A B E h.1 z
  · exact (RectangularEvolution.scaled B A Eᴴ h.2.symm z).symm

/-- Hermitian part of an observed operator, observed as the Hermitian target. -/
theorem herm {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) (hB : B.IsHermitian) :
    Obs E ((1 / 2 : ℂ) • (A + Aᴴ)) B := by
  have := smul (1 / 2 : ℂ) (add h (star h))
  rw [hB.eq, ← two_smul ℂ B, smul_smul] at this
  simpa using this

/-- Block-diagonal readout. -/
theorem blocks [DecidableEq a] [DecidableEq b] {A11 A12 A21 A22 : Matrix a a ℂ} {B11 B12 B21 B22 : Matrix b b ℂ}
    (h11 : Obs E A11 B11) (h12 : Obs E A12 B12) (h21 : Obs E A21 B21) (h22 : Obs E A22 B22) :
    Obs (fromBlocks E 0 0 E) (fromBlocks A11 A12 A21 A22) (fromBlocks B11 B12 B21 B22) := by
  constructor
  · simp [fromBlocks_multiply, h11.1, h12.1, h21.1, h22.1]
  · simp [fromBlocks_conjTranspose, fromBlocks_multiply, h11.2, h12.2, h21.2, h22.2]

theorem zero : Obs E (0 : Matrix a a ℂ) (0 : Matrix b b ℂ) := ⟨by simp, by simp⟩

/-- Site-local operators: a spatial matrix tensored with an observed internal one. -/
theorem kron [DecidableEq a] [DecidableEq b] {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℂ)
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) :
    Obs ((1 : Matrix X X ℂ) ⊗ₖ E) (P ⊗ₖ A) (P ⊗ₖ B) := by
  constructor
  · rw [← mul_kronecker_mul, ← mul_kronecker_mul, h.1, Matrix.mul_one, Matrix.one_mul]
  · rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      h.2, Matrix.mul_one, Matrix.one_mul]

omit [Fintype b] in
theorem isometry_kron [DecidableEq b] {X : Type*} [Fintype X] [DecidableEq X] (hE : Eᴴ * E = 1) :
    ((1 : Matrix X X ℂ) ⊗ₖ E)ᴴ * ((1 : Matrix X X ℂ) ⊗ₖ E) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hE,
    one_kronecker_one]

/-- Observed evolution of every initial amplitude: readout commutes with the dynamics. -/
theorem readout {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) (ψ : a → ℂ) :
    Eᴴ *ᵥ (A *ᵥ ψ) = B *ᵥ (Eᴴ *ᵥ ψ) := by
  rw [mulVec_mulVec, h.2, ← mulVec_mulVec]

/-- For an involution, the exponential is the closed-form rotation. -/
theorem exp_involution [DecidableEq b] (G : Matrix b b ℂ) (hG : G * G = 1) (τ : ℝ) :
    NormedSpace.exp ((Complex.I * τ) • G) = LocalUnitary.rotation G τ := by
  have hd : G = InvolutionSpectral.plus G - InvolutionSpectral.minus G := by
    simp only [InvolutionSpectral.plus, InvolutionSpectral.minus, ← smul_sub]
    rw [show (1 + G - (1 - G) : Matrix b b ℂ) = (2 : ℂ) • G by module, smul_smul]; norm_num
  have hs : (Complex.I * τ) • G = (Complex.I * τ) • InvolutionSpectral.plus G +
      (-(Complex.I * τ)) • InvolutionSpectral.minus G := by
    conv_lhs => rw [hd]
    rw [smul_sub, neg_smul, sub_eq_add_neg]
  rw [hs, InvolutionSpectral.exp_sectors G hG]
  have e1 : Complex.exp (Complex.I * τ) = Real.cos τ + Complex.I * Real.sin τ := by
    rw [mul_comm, Complex.exp_mul_I]; push_cast; ring
  have e2 : Complex.exp (-(Complex.I * τ)) = Real.cos τ - Complex.I * Real.sin τ := by
    rw [show -(Complex.I * τ) = ((-τ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring
  rw [e1, e2]
  simp only [LocalUnitary.rotation, InvolutionSpectral.plus, InvolutionSpectral.minus]
  module

/-- Exponentials of `-i t` times a Hermitian matrix are unitary, on any finite index type. -/
theorem exp_unitary [DecidableEq a] (A : Matrix a a ℂ) (ha : A.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • A) ∈ unitary (Matrix a a ℂ) := by
  have hs : ((-Complex.I * (t : ℂ)) • A)ᴴ = -((-Complex.I * (t : ℂ)) • A) := by
    simp only [conjTranspose_neg, conjTranspose_smul, ha.eq, RCLike.star_def, map_mul,
      Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_smul, neg_mul]
  have he : (NormedSpace.exp ((-Complex.I * (t : ℂ)) • A))ᴴ =
      NormedSpace.exp (-((-Complex.I * (t : ℂ)) • A)) := by
    rw [← Matrix.exp_conjTranspose, hs]
  constructor
  · change (NormedSpace.exp _)ᴴ * NormedSpace.exp _ = 1
    rw [he, ← Matrix.exp_add_of_commute _ _ (Commute.refl ((-Complex.I * (t : ℂ)) • A)).neg_left]
    simp
  · change NormedSpace.exp _ * (NormedSpace.exp _)ᴴ = 1
    rw [he, ← Matrix.exp_add_of_commute _ _ (Commute.refl ((-Complex.I * (t : ℂ)) • A)).neg_right]
    simp

end PMAction.NativeObservation

/-!
# Native carrier operators are parity-covariant and observed exactly

Every native operator used for the vacuum model (the root-word lookups and the four
orthogonal-root phases) commutes with antipodal inversion, because root reflections are
linear lattice maps. With `NativeObservation.of_commute` this makes the earlier
"no-feedback" condition a theorem and removes the need for an even-complement
convention: the Hermitian completion `nativeHamiltonian`, built only from native
operators and adjoints, is Hermitian on all sixteen labels, preserves both parity
sectors, and its coordinate readout evolves exactly by the vacuum Hamiltonian for every
initial amplitude. Its odd eigenvalues obey the light/heavy branch law.
-/
noncomputable section
namespace PMAction.NativeSector
open Matrix CarrierEvents CarrierParity NativeObservation

/-! ## Parity commutation of native permutations -/

lemma lookup_antipode : ∀ (c : Fin 3) (g : Fin 6) (v : Carrier c),
    CarrierWeyl.lookup c g (antipode c v) = antipode c (CarrierWeyl.lookup c g v) := by
  decide +kernel

lemma event_antipode : ∀ (c : Fin 3) (j : Fin 4) (v : Carrier c),
    OrthogonalRootPhase.event c j (antipode c v) = antipode c (OrthogonalRootPhase.event c j v) := by
  decide +kernel

/-- Antipodal parity matrix of one carrier class. -/
abbrev N (c : Fin 3) : Matrix (Carrier c) (Carrier c) ℂ := (antipode c).permMatrix ℂ

lemma perm_commute (c : Fin 3) (σ : Equiv.Perm (Carrier c))
    (h : ∀ v, σ (antipode c v) = antipode c (σ v)) :
    σ.permMatrix ℂ * N c = N c * σ.permMatrix ℂ := by
  have he : antipode c * σ = σ * antipode c := by
    ext v; simp [Equiv.Perm.mul_apply, h]
  rw [N, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, he]

lemma phase_commute (c : Fin 3) (j : Fin 4) (p t : ℝ) :
    RootTransferPhase.phase (OrthogonalRootPhase.event c j) p t * N c =
      N c * RootTransferPhase.phase (OrthogonalRootPhase.event c j) p t := by
  have hc := perm_commute c _ (event_antipode c j)
  rw [RootTransferPhase.phase_formula _ (OrthogonalRootPhase.event_involutive c j)]
  simp only [InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hc]

/-- Products of matrices commuting with `N` commute with `N`. -/
lemma comm_mul {c : Fin 3} {A B : Matrix (Carrier c) (Carrier c) ℂ}
    (ha : A * N c = N c * A) (hb : B * N c = N c * B) : (A * B) * N c = N c * (A * B) := by
  rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]

lemma phaseI_commute (c : Fin 3) (p : ℝ) : OddCarrierPhase.phaseI c p * N c =
    N c * OddCarrierPhase.phaseI c p := by
  unfold OddCarrierPhase.phaseI OrthogonalRootPhase.phase
  exact comm_mul (comm_mul (comm_mul (phase_commute c 0 _ _) (phase_commute c 1 _ _))
    (phase_commute c 2 _ _)) (phase_commute c 3 _ _)

lemma lookup_commute (c : Fin 3) (g : Fin 6) :
    (CarrierWeyl.lookup c g).permMatrix ℂ * N c = N c * (CarrierWeyl.lookup c g).permMatrix ℂ :=
  perm_commute c _ (lookup_antipode c g)

/-! ## Observation at carrier level -/

lemma proj_eq (c : Fin 3) : embedding c * (embedding c)ᴴ = (1/2 : ℂ) • (1 - N c) :=
  projector c

lemma obs_of (c : Fin 3) {A : Matrix (Carrier c) (Carrier c) ℂ} {B : Matrix (Fin 4) (Fin 4) ℂ}
    (h : A * embedding c = embedding c * B) (hc : A * N c = N c * A) :
    Obs (embedding c) A B := by
  apply of_commute (isometry c) h
  rw [proj_eq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, hc]

theorem beta_obs (c : Fin 3) : Obs (embedding c) (CarrierVacuumSector.beta c) ConcreteFermion.beta :=
  obs_of c (CarrierVacuumSector.beta_intertwining c) (lookup_commute c 0)

theorem gamma_obs (c : Fin 3) :
    Obs (embedding c) (CarrierVacuumSector.gamma c) ConcreteFermion.gamma :=
  obs_of c (CarrierVacuumSector.gamma_intertwining c) (lookup_commute c 1)

theorem alpha_obs (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (j : Fin 3) :
    Obs (embedding c) (CarrierVacuumSector.alpha c p j) (ConcreteFermion.alpha j) := by
  apply obs_of c (CarrierVacuumSector.alpha_intertwining c p hp hp1 j)
  fin_cases j
  · exact lookup_commute c 2
  · exact comm_mul (phaseI_commute c p) (lookup_commute c 4)
  · exact lookup_commute c 3

/-! ## The native Hermitian vacuum generator on all sixteen labels -/

section Labels
open DomainWallSpectrum ConcreteFermion

lemma obs_rsmul {a b : Type*} [Fintype a] [Fintype b] {E : Matrix a b ℂ} (r : ℝ)
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (h : Obs E A B) : Obs E (r • A) (r • B) := by
  have := NativeObservation.smul (r : ℂ) h
  simpa only [Complex.coe_smul] using this

lemma diag_hermitian (k : Fin 3 → ℝ) (δ : ℝ) :
    (DomainWallSpectrum.momentum alpha k + δ • beta).IsHermitian :=
  (momentum_hermitian k).add (beta_hermitian.smul (IsSelfAdjoint.all δ))

lemma hop_adjoint : (DomainWallSpectrum.hop beta gamma)ᴴ = DomainWallSpectrum.back beta gamma := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [DomainWallSpectrum.hop, DomainWallSpectrum.back,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma,
      conjTranspose_apply, mul_apply, vecMul, dotProduct, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four]

variable (c : Fin 3) (p : ℝ)

/-- Native diagonal block, Hermitian part of the native momentum/mass operator. -/
def diag (k : Fin 3 → ℝ) (δ : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  (1/2 : ℂ) • ((DomainWallSpectrum.momentum (CarrierVacuumSector.alpha c p) k +
      δ • CarrierVacuumSector.beta c) +
    (DomainWallSpectrum.momentum (CarrierVacuumSector.alpha c p) k +
      δ • CarrierVacuumSector.beta c)ᴴ)

/-- Native wall hop. -/
def hopN : Matrix (Carrier c) (Carrier c) ℂ :=
  DomainWallSpectrum.hop (CarrierVacuumSector.beta c) (CarrierVacuumSector.gamma c)

/-- Hermitian completion of the native generator: diagonal blocks are Hermitian parts and
the return hop is the adjoint of the native hop. Only native operators and adjoints occur. -/
def nativeHamiltonian (k : Fin 3 → ℝ) (δ : ℝ) : Matrix (CarrierVacuumSector.Labels c) (CarrierVacuumSector.Labels c) ℂ :=
  fromBlocks (diag c p k δ) (hopN c) (hopN c)ᴴ (diag c p k δ)

theorem nativeHamiltonian_hermitian (k : Fin 3 → ℝ) (δ : ℝ) :
    (nativeHamiltonian c p k δ).IsHermitian := by
  have hd : (diag c p k δ)ᴴ = diag c p k δ := by
    simp only [diag, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  unfold IsHermitian nativeHamiltonian
  rw [fromBlocks_conjTranspose, hd, conjTranspose_conjTranspose]

variable {c p}

theorem diag_obs (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ) :
    Obs (CarrierParity.embedding c) (diag c p k δ)
      (DomainWallSpectrum.momentum alpha k + δ • beta) := by
  have hK : Obs (CarrierParity.embedding c)
      (DomainWallSpectrum.momentum (CarrierVacuumSector.alpha c p) k)
      (DomainWallSpectrum.momentum alpha k) := by
    simp only [DomainWallSpectrum.momentum, Fin.sum_univ_three]
    exact NativeObservation.add (NativeObservation.add (obs_rsmul _ (alpha_obs c p hp hp1 0))
      (obs_rsmul _ (alpha_obs c p hp hp1 1))) (obs_rsmul _ (alpha_obs c p hp hp1 2))
  exact NativeObservation.herm (NativeObservation.add hK (obs_rsmul δ (beta_obs c)))
    (diag_hermitian k δ)

theorem hop_obs : Obs (CarrierParity.embedding c) (hopN c) (DomainWallSpectrum.hop beta gamma) := by
  unfold hopN DomainWallSpectrum.hop DomainWallSpectrum.plus
  exact NativeObservation.neg (NativeObservation.mul (beta_obs c)
    (obs_rsmul _ (NativeObservation.add NativeObservation.one (gamma_obs c))))

/-- **Native observation.** The coordinate readout sees the native Hermitian generator as
the full two-wall vacuum Hamiltonian, in both directions. -/
theorem native_obs (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ) :
    Obs (CarrierVacuumSector.embedding c) (nativeHamiltonian c p k δ)
      (ConcreteFermion.hamiltonian k δ) := by
  have hb := NativeObservation.star (hop_obs (c := c))
  rw [hop_adjoint] at hb
  exact NativeObservation.blocks (diag_obs hp hp1 k δ) hop_obs hb (diag_obs hp hp1 k δ)

/-- The native generator commutes with antipodal parity on all sixteen labels. -/
theorem native_parity (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ) :
    nativeHamiltonian c p k δ * CarrierVacuumSector.parity c = CarrierVacuumSector.parity c * nativeHamiltonian c p k δ := by
  have h := NativeObservation.commutes (native_obs (c := c) hp hp1 k δ)
  rw [CarrierVacuumSector.projector, CarrierVacuumSector.oddProjector] at h
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul] at h
  have h2 := congrArg (fun M => (-2 : ℂ) • M + nativeHamiltonian c p k δ) h
  simp only [smul_sub, smul_smul] at h2
  norm_num at h2
  exact h2

/-- **Exact observed evolution for every initial amplitude**, with no restriction, no
even-complement convention and no supplied no-feedback hypothesis. -/
theorem observed_evolution (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ)
    (ψ : CarrierVacuumSector.Labels c → ℂ) :
    CarrierReadoutQuotient.readout c *ᵥ (NormedSpace.exp (z • nativeHamiltonian c p k δ) *ᵥ ψ) =
      NormedSpace.exp (z • ConcreteFermion.hamiltonian k δ) *ᵥ
        (CarrierReadoutQuotient.readout c *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (native_obs hp hp1 k δ) z) ψ

/-- **Branches in the carrier model.** Every odd native eigenvalue lies on the light or
heavy branch of the vacuum model. -/
theorem odd_branches (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ E : ℝ)
    (v : CarrierVacuumSector.Labels c → ℂ) (hodd : CarrierVacuumSector.parity c *ᵥ v = -v) (hv : v ≠ 0)
    (he : nativeHamiltonian c p k δ *ᵥ v = E • v) :
    E ^ 2 = kineticNorm k + (DetuningMass.lightMass δ) ^ 2 ∨
      E ^ 2 = kineticNorm k + (DetuningMass.lightMass δ + 1) ^ 2 := by
  set w := CarrierReadoutQuotient.readout c *ᵥ v
  have hw : w ≠ 0 := by
    intro h0
    have heven := (CarrierReadoutQuotient.invisible_iff_even c v).mp h0
    apply hv
    have : v = -v := heven.symm.trans hodd
    have h2 : (2 : ℂ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [this]; simp
    simpa using h2
  have hew : ConcreteFermion.hamiltonian k δ *ᵥ w = E • w := by
    have := NativeObservation.readout (native_obs hp hp1 k δ) v
    rw [he, mulVec_smul] at this
    simpa [w, CarrierReadoutQuotient.readout] using this.symm
  have hk := kinetic_relations alpha beta gamma k clifford alpha_gamma
  exact energy_branches (momentum alpha k) beta gamma δ (kineticNorm k) E
    beta_square gamma_square beta_gamma hk.1 hk.2.1 hk.2.2 w hw hew

/-- Every vacuum eigenvector is carried by an odd native eigenvector with the same energy. -/
theorem branch_realized (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ E : ℝ)
    (w : ConcreteFermion.Sites → ℂ) (he : ConcreteFermion.hamiltonian k δ *ᵥ w = E • w) :
    nativeHamiltonian c p k δ *ᵥ (CarrierVacuumSector.embedding c *ᵥ w) =
      E • (CarrierVacuumSector.embedding c *ᵥ w) := by
  rw [mulVec_mulVec, (native_obs hp hp1 k δ).1, ← mulVec_mulVec, he, mulVec_smul]

end Labels

end PMAction.NativeSector

/-!
# The native real-space split update on actual carrier labels

On `space × sixteen carrier labels`, every factor of the corrected split is the
exponential of a Hermitian operator built only from native root-word/phase operators,
spatial permutations and adjoints. The native update is unitary on all labels, and the
sitewise coordinate readout sees it as the actual `SplitUpdate.update`; on the periodic
torus this is `VacuumSplit.update`. Hence the real-space spectral identification and the
uniform small-tick stationary-field classification transfer to the carrier model.
-/
noncomputable section
namespace PMAction.NativeSplit
open Matrix CarrierEvents NativeObservation ConcreteFermion
open scoped Kronecker

variable (c : Fin 3) (p : ℝ)
abbrev L := CarrierVacuumSector.Labels c

/-- Native carrier-level neighbour coefficient `(β + i α_j)/2`. -/
def coef (j : Fin 3) : Matrix (Carrier c) (Carrier c) ℂ :=
  (1/2 : ℂ) • CarrierVacuumSector.beta c + (Complex.I/2) • CarrierVacuumSector.alpha c p j

def coefL (j : Fin 3) : Matrix (L c) (L c) ℂ := fromBlocks (coef c p j) 0 0 (coef c p j)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Native hopping generator; Hermitian by construction. -/
def neighborN (e : Equiv.Perm X) (j : Fin 3) : Matrix (X × L c) (X × L c) ℂ :=
  e.permMatrix ℂ ⊗ₖ coefL c p j + (e.permMatrix ℂ)ᴴ ⊗ₖ (coefL c p j)ᴴ

omit [Fintype X] in
lemma neighborN_hermitian (e : Equiv.Perm X) (j : Fin 3) : (neighborN c p e j).IsHermitian := by
  simp [IsHermitian, neighborN, conjTranspose_add, conjTranspose_kronecker, add_comm]

def directionN (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) : Matrix (X × L c) (X × L c) ℂ :=
  NormedSpace.exp ((Complex.I * τ) • neighborN c p e j)

/-- Hermitian part of the native beta on both walls. -/
def betaL : Matrix (L c) (L c) ℂ :=
  fromBlocks ((1/2 : ℂ) • (CarrierVacuumSector.beta c + (CarrierVacuumSector.beta c)ᴴ)) 0 0
    ((1/2 : ℂ) • (CarrierVacuumSector.beta c + (CarrierVacuumSector.beta c)ᴴ))

lemma betaL_hermitian : (betaL c).IsHermitian := by
  unfold IsHermitian betaL
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, conjTranspose_zero]
  congr 1 <;> (rw [add_comm]; congr 1; simp)

/-- Native on-site coin: wall evolution after undoing three beta rotations. -/
def coinN (τ : ℝ) : Matrix (L c) (L c) ℂ :=
  NormedSpace.exp ((-Complex.I * τ) • NativeSector.nativeHamiltonian c p 0 0) *
    NormedSpace.exp ((-Complex.I * ((3 * τ : ℝ) : ℂ)) • betaL c)

/-- The native split update: on-site coin after the three directional exponentials. -/
def updateN (e : Fin 3 → Equiv.Perm X) (τ : ℝ) : Matrix (X × L c) (X × L c) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ coinN c p τ) *
    (directionN c p (e 0) 0 τ * directionN c p (e 1) 1 τ * directionN c p (e 2) 2 τ)

/-- Sitewise readout embedding. -/
def emb : Matrix (X × L c) (X × Sites) ℂ := (1 : Matrix X X ℂ) ⊗ₖ CarrierVacuumSector.embedding c

lemma emb_isometry : (emb (X := X) c)ᴴ * emb (X := X) c = 1 :=
  isometry_kron (CarrierVacuumSector.isometry c)

theorem updateN_unitary (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    updateN c p e τ ∈ unitary (Matrix (X × L c) (X × L c) ℂ) := by
  have hd : ∀ (f : Equiv.Perm X) (j : Fin 3), directionN c p f j τ ∈ unitary _ := by
    intro f j
    have := exp_unitary (neighborN c p f j) (neighborN_hermitian c p f j) (-τ)
    simpa [directionN, neg_mul, mul_neg, neg_neg] using this
  have hc : coinN c p τ ∈ unitary _ :=
    (unitary _).mul_mem (exp_unitary _ (NativeSector.nativeHamiltonian_hermitian c p 0 0) τ)
      (exp_unitary _ (betaL_hermitian c) (3 * τ))
  have hk : ((1 : Matrix X X ℂ) ⊗ₖ coinN c p τ) ∈ unitary _ := by
    constructor
    · change ((1 : Matrix X X ℂ) ⊗ₖ coinN c p τ)ᴴ * _ = 1
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
        show (coinN c p τ)ᴴ * coinN c p τ = 1 from hc.1, one_kronecker_one]
    · change _ * ((1 : Matrix X X ℂ) ⊗ₖ coinN c p τ)ᴴ = 1
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
        show coinN c p τ * (coinN c p τ)ᴴ = 1 from hc.2, one_kronecker_one]
  exact (unitary _).mul_mem hk ((unitary _).mul_mem ((unitary _).mul_mem (hd _ _) (hd _ _)) (hd _ _))

variable {c p}

lemma coef_obs (hp : 0 < p) (hp1 : p < 1/2) (j : Fin 3) :
    Obs (CarrierParity.embedding c) (coef c p j) (LocalUnitary.coefficient j) :=
  add (smul _ (NativeSector.beta_obs c)) (smul _ (NativeSector.alpha_obs c p hp hp1 j))

lemma coefL_obs (hp : 0 < p) (hp1 : p < 1/2) (j : Fin 3) :
    Obs (CarrierVacuumSector.embedding c) (coefL c p j) (SplitUpdate.coefficient j) :=
  blocks (coef_obs hp hp1 j) zero zero (coef_obs hp hp1 j)

lemma neighbor_obs (hp : 0 < p) (hp1 : p < 1/2) (e : Equiv.Perm X) (j : Fin 3) :
    Obs (emb c) (neighborN c p e j) (SplitUpdate.neighbor e j) :=
  add (kron _ (coefL_obs hp hp1 j)) (kron _ (star (coefL_obs hp hp1 j)))

lemma direction_obs (hp : 0 < p) (hp1 : p < 1/2) (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    Obs (emb c) (directionN c p e j τ) (SplitUpdate.direction e j τ) := by
  have h := exp (neighbor_obs (c := c) hp hp1 e j) (Complex.I * τ)
  rwa [exp_involution _ (SplitUpdate.neighbor_square e j)] at h

lemma beta8_obs : Obs (CarrierVacuumSector.embedding c) (betaL c) VacuumSplit.beta8 := by
  have hb := herm (NativeSector.beta_obs c) ConcreteFermion.beta_hermitian
  exact blocks hb zero zero hb

lemma coin_obs (hp : 0 < p) (hp1 : p < 1/2) (τ : ℝ) :
    Obs (CarrierVacuumSector.embedding c) (coinN c p τ) (VacuumSplit.onsiteCoin τ) := by
  have hw := exp (NativeSector.native_obs (c := c) hp hp1 0 0) (-Complex.I * τ)
  have hb := exp (beta8_obs (c := c)) (-Complex.I * ((3 * τ : ℝ) : ℂ))
  have hr : NormedSpace.exp ((-Complex.I * ((3 * τ : ℝ) : ℂ)) • VacuumSplit.beta8) =
      ((VacuumSplit.rotation τ)ᴴ) ^ 3 := by
    rw [VacuumSplit.rotation, RotationAlgebra.rotation_adjoint _ VacuumSplit.beta8_hermitian,
      RotationAlgebra.rotation_nsmul _ VacuumSplit.beta8_square,
      ← exp_involution _ VacuumSplit.beta8_square]
    congr 2; push_cast; ring
  rw [hr] at hb
  exact mul hw hb

/-- **Native observation of the split update**, for any spatial permutations. -/
theorem update_obs (hp : 0 < p) (hp1 : p < 1/2) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    Obs (emb c) (updateN c p e τ) (SplitUpdate.update e (VacuumSplit.onsiteCoin τ) τ) :=
  mul (kron 1 (coin_obs hp hp1 τ))
    (mul (mul (direction_obs hp hp1 _ 0 τ) (direction_obs hp hp1 _ 1 τ))
      (direction_obs hp hp1 _ 2 τ))

/-! ## The periodic torus -/

variable (n : ℕ)
abbrev Lat := RealSpaceFourier.Lat n

theorem torus_obs (hp : 0 < p) (hp1 : p < 1/2) (τ : ℝ) :
    Obs (emb (X := Lat n) c) (updateN c p (SplitUpdate.axisShift (n + 1)) τ)
      (VacuumSplit.update (n + 1) τ) :=
  update_obs hp hp1 _ τ

/-- A sitewise odd carrier field. -/
def Odd (ψ : Lat n × L c → ℂ) : Prop :=
  emb c *ᵥ ((emb c)ᴴ *ᵥ ψ) = ψ

/-- **Stationary carrier fields.** For one tick bound uniform in the torus size, an odd
carrier field is fixed by the native update exactly when its readout is spatially constant
with internal vector in the wall kernel. -/
theorem stationary_iff (hp : 0 < p) (hp1 : p < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ τ : ℝ, τ ≠ 0 → |τ| < δ → ∀ ψ : Lat n × L c → ℂ, Odd n ψ →
      (updateN c p (SplitUpdate.axisShift (n + 1)) τ *ᵥ ψ = ψ ↔
        ∃ v : Sites → ℂ, VacuumSplit.wall *ᵥ v = 0 ∧
          (emb c)ᴴ *ᵥ ψ = fun q => v q.2) := by
  obtain ⟨δ, hδ, h⟩ := RealSpaceFourier.real_fixed_iff
  refine ⟨δ, hδ, fun n τ hτ hs ψ hodd => ?_⟩
  have ho := torus_obs (c := c) n hp hp1 τ
  rw [← h n τ hτ hs]
  constructor
  · intro hf
    have := readout ho ψ
    rw [hf] at this
    exact this.symm
  · intro hf
    rw [← hodd, mulVec_mulVec, ho.1, ← mulVec_mulVec, hf]

/-- **Spectral identification in the carrier model.** An odd native eigenvector exists
exactly when some momentum block has the eigenvalue. -/
theorem eigen_iff (hp : 0 < p) (hp1 : p < 1/2) (τ : ℝ) (μ : ℂ) :
    (∃ ψ : Lat n × L c → ℂ, ψ ≠ 0 ∧ Odd n ψ ∧
        updateN c p (SplitUpdate.axisShift (n + 1)) τ *ᵥ ψ = μ • ψ) ↔
      ∃ m : Lat n, ∃ v : Sites → ℂ, v ≠ 0 ∧
        VacuumSplit.momentumUpdate (RealSpaceFourier.kvec n (RealSpaceFourier.cvec n m)) τ *ᵥ v =
          μ • v := by
  have ho := torus_obs (c := c) n hp hp1 τ
  rw [← RealSpaceFourier.eigen_iff]
  constructor
  · rintro ⟨ψ, hψ, hodd, he⟩
    refine ⟨(emb c)ᴴ *ᵥ ψ, fun h0 => hψ ?_, ?_⟩
    · rw [← hodd, h0, mulVec_zero]
    · rw [← readout ho ψ, he, mulVec_smul]
  · rintro ⟨φ, hφ, he⟩
    refine ⟨emb c *ᵥ φ, fun h0 => hφ ?_, ?_, ?_⟩
    · have := congrArg (fun w => (emb (X := Lat n) c)ᴴ *ᵥ w) h0
      simpa [mulVec_mulVec, emb_isometry c] using this
    · unfold Odd
      rw [show (emb (X := Lat n) c)ᴴ *ᵥ (emb c *ᵥ φ) = φ by
        rw [mulVec_mulVec, emb_isometry c, one_mulVec]]
    · rw [mulVec_mulVec, ho.1, ← mulVec_mulVec, he, mulVec_smul]

end PMAction.NativeSplit

/-!
# Records and live streams on the same coordinate readout as wall spinors

The reference protocol's four moving vector-class carriers are two antipodal pairs:
live `±2e₀` and record `±2e₁` (the existing root swaps axes `0,1`). Hence the native
reference lookup commutes with antipodal parity, and the coordinate readout of the
vector class (the first-wall readout of the vacuum carrier model at `c = 0`) sees the
reference field as two contrasts: live on axis `0`, record on axis `1`. These contrasts
evolve by exactly the same two-stream/exchange rule. The reference protocol and the
vacuum split are thus two observed operators on one state space and one readout; neither
is identified with the other.
-/
noncomputable section
namespace PMAction.Records
open Matrix CarrierEvents NativeObservation
open scoped Kronecker

abbrev C := ActualRootRepair.C
abbrev Ports := ActualRootRepair.Ports

def swapIdx : Ports → Ports := Sum.map (fun i : Fin 2 => 1 - i) (fun i : Fin 2 => 1 - i)

lemma antipode_label : ∀ j : Ports,
    CarrierParity.antipode 0 (ActualRootRepair.label j) = ActualRootRepair.label (swapIdx j) := by
  decide +kernel

/-- Coordinates of the four moving labels: live on axis 0, record on axis 1. -/
lemma label_vector : ∀ (j : Ports) (i : Fin 4), vector (ActualRootRepair.label j) i =
    (match j with
      | .inl a => if i = 0 then (if a = 0 then 2 else -2) else 0
      | .inr a => if i = 1 then (if a = 0 then 2 else -2) else 0) := by
  decide +kernel

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
lemma portStep_swap (o : X) (e : Equiv.Perm X) (x : X) (j : Ports) :
    NativeCarrierProtocol.portStep o e (x, swapIdx j) =
      ((NativeCarrierProtocol.portStep o e (x, j)).1,
        swapIdx (NativeCarrierProtocol.portStep o e (x, j)).2) := by
  rcases j with j | j <;> by_cases h : x = o <;>
    simp [NativeCarrierProtocol.portStep, NativeCarrierProtocol.couple,
      NativeCarrierProtocol.stream, swapIdx, h]

/-- Sitewise antipodal inversion. -/
def antipodeSite : Equiv.Perm (X × C) := Equiv.prodCongrRight fun _ => CarrierParity.antipode 0

omit [Fintype X] in
/-- **The native reference lookup commutes with antipodal parity.** -/
theorem lookup_antipode (o : X) (e : Equiv.Perm X) (q : X × C) :
    NativeCarrierProtocol.lookup o e (antipodeSite q) =
      antipodeSite (NativeCarrierProtocol.lookup o e q) := by
  rcases q with ⟨x, v⟩
  by_cases hv : v ∈ Set.range ActualRootRepair.label
  · obtain ⟨j, rfl⟩ := hv
    simp only [antipodeSite, Equiv.prodCongrRight_apply, antipode_label]
    rw [NativeCarrierProtocol.lookup_label, NativeCarrierProtocol.lookup_label, portStep_swap]
    simp [antipode_label]
  · have hv' : CarrierParity.antipode 0 v ∉ Set.range ActualRootRepair.label := by
      rintro ⟨j, hj⟩
      apply hv
      refine ⟨swapIdx j, ?_⟩
      rw [← antipode_label, hj, CarrierParity.antipode_involutive]
    simp only [antipodeSite, Equiv.prodCongrRight_apply]
    rw [NativeCarrierProtocol.lookup_unused o e x _ hv', NativeCarrierProtocol.lookup_unused o e x _ hv]
    rfl

/-- Sitewise vector-class readout embedding. -/
def emb : Matrix (X × C) (X × Fin 4) ℂ := (1 : Matrix X X ℂ) ⊗ₖ CarrierParity.embedding 0

lemma emb_proj : emb (X := X) * (emb (X := X))ᴴ =
    (1 / 2 : ℂ) • (1 - (antipodeSite (X := X)).permMatrix ℂ) := by
  have hp : (antipodeSite (X := X)).permMatrix ℂ =
      (1 : Matrix X X ℂ) ⊗ₖ (CarrierParity.antipode 0).permMatrix ℂ := by
    ext ⟨x, v⟩ ⟨y, w⟩
    simp [antipodeSite, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, one_apply,
      Equiv.toPEquiv_apply, Prod.ext_iff, kroneckerMap_apply]
    by_cases h : x = y <;> simp [h, eq_comm]
  rw [hp, emb, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
    CarrierParity.projector]
  ext ⟨x, v⟩ ⟨y, w⟩
  simp only [kroneckerMap_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases h : x = y <;> by_cases h' : v = w <;> simp [one_apply, h, h']

/-- **Records are observed.** The coordinate readout sees the native reference lookup as
its own compression; no unobserved amplitude feeds the readout. -/
theorem reference_obs (o : X) (e : Equiv.Perm X) :
    Obs (emb (X := X)) ((NativeCarrierProtocol.lookup o e).permMatrix ℂ)
      ((emb (X := X))ᴴ * (NativeCarrierProtocol.lookup o e).permMatrix ℂ * emb (X := X)) := by
  have hiso : (emb (X := X))ᴴ * emb (X := X) = 1 := isometry_kron (X := X) (CarrierParity.isometry 0)
  have hc : (NativeCarrierProtocol.lookup o e).permMatrix ℂ * (antipodeSite (X := X)).permMatrix ℂ =
      (antipodeSite (X := X)).permMatrix ℂ * (NativeCarrierProtocol.lookup o e).permMatrix ℂ := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
    congr 1
    exact Equiv.ext fun q => by simp only [Equiv.Perm.mul_apply, lookup_antipode]
  have hcomm : (NativeCarrierProtocol.lookup o e).permMatrix ℂ * (emb * (emb (X := X))ᴴ) =
      (emb * (emb (X := X))ᴴ) * (NativeCarrierProtocol.lookup o e).permMatrix ℂ := by
    rw [emb_proj]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hc]
  refine of_commute hiso ?_ hcomm
  symm
  calc emb * ((emb (X := X))ᴴ * (NativeCarrierProtocol.lookup o e).permMatrix ℂ * emb (X := X))
      = (emb * (emb (X := X))ᴴ) * (NativeCarrierProtocol.lookup o e).permMatrix ℂ * emb (X := X) := by
        simp only [Matrix.mul_assoc]
    _ = (NativeCarrierProtocol.lookup o e).permMatrix ℂ * (emb * ((emb (X := X))ᴴ * emb (X := X))) := by
        rw [← hcomm]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hiso, Matrix.mul_one]

/-- Live and record contrasts. -/
def contrast (live record : X → Fin 2 → ℂ) : X × Fin 4 → ℂ := fun q =>
  ((2 : ℂ) * CarrierParity.scale) *
    (if q.2 = 0 then live q.1 0 - live q.1 1 else if q.2 = 1 then record q.1 0 - record q.1 1 else 0)

lemma emb_readout (f : X × C → ℂ) (x : X) (i : Fin 4) :
    ((emb (X := X))ᴴ *ᵥ f) (x, i) = ∑ v, star (CarrierParity.embedding 0 v i) * f (x, v) := by
  simp only [emb, mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    conjTranspose_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [one_apply, hy]
  · simp

/-- **The readout of a reference field is its live/record contrast.** -/
theorem readout_field (live record : X → Fin 2 → ℂ) :
    (emb (X := X))ᴴ *ᵥ RootCarrierWalk.field live record = contrast live record := by
  ext ⟨x, i⟩
  rw [emb_readout]
  have hsum : (∑ v : C, star (CarrierParity.embedding 0 v i) *
        ActualRootRepair.pack (live x) (record x) v) =
      ∑ j : Ports, star (CarrierParity.embedding 0 (ActualRootRepair.label j) i) *
        Sum.elim (live x) (record x) j := by
    simp only [ActualRootRepair.pack, ActualRootRepair.embedding, mulVec, dotProduct,
      ite_mul, one_mul, zero_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (ActualRootRepair.label j)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  change (∑ v : C, star (CarrierParity.embedding 0 v i) *
    ActualRootRepair.pack (live x) (record x) v) = _
  rw [hsum]
  simp only [CarrierParity.embedding, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_two, label_vector, contrast]
  fin_cases i <;> simp [CarrierParity.scale] <;> ring

/-- **Observed reference step.** The contrasts evolve by the same two-stream rule, with the
record contrast exchanged into the live contrast at the coupling site. -/
theorem observed_step (o : X) (e : Equiv.Perm X) (live record : X → Fin 2 → ℂ) :
    (emb (X := X))ᴴ *ᵥ ((NativeCarrierProtocol.lookup o e).permMatrix ℂ *ᵥ
        RootCarrierWalk.field live record) =
      contrast (fun x => if x = o then record (e x) else live (e⁻¹ x))
        (fun x => if x = o then live (e⁻¹ x) else record (e x)) := by
  rw [NativeCarrierProtocol.field_step, readout_field]

end PMAction.Records

/-!
# One clock for the native update

A four-phase clock register schedules the four native factors of one split tick:
the three directional exponentials and the on-site coin. The clocked operator applies
the factor indexed by the clock phase and advances the clock. Every four clock events
return the clock to phase zero and apply exactly one native tick, independent of the
state. With the native observation theorems, the readout at every clock phase follows
the concrete clocked split. Which clock events carry a physical price is not inferred.
-/
noncomputable section
namespace PMAction.Clock
open Matrix

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- Clock-controlled schedule: apply `F j` at phase `j`, then advance to `j + 1`. -/
def clocked (F : Fin 4 → Matrix a a ℂ) : Matrix (Fin 4 × a) (Fin 4 × a) ℂ :=
  fun q r => if q.1 = r.1 + 1 then F r.1 q.2 r.2 else 0

/-- A state held at clock phase `j`. -/
def held (j : Fin 4) (ψ : a → ℂ) : Fin 4 × a → ℂ := fun q => if q.1 = j then ψ q.2 else 0

omit [DecidableEq a] in
theorem step (F : Fin 4 → Matrix a a ℂ) (j : Fin 4) (ψ : a → ℂ) :
    clocked F *ᵥ held j ψ = held (j + 1) (F j *ᵥ ψ) := by
  ext ⟨i, x⟩
  simp only [mulVec, dotProduct, clocked, held, Fintype.sum_prod_type, ite_mul, zero_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_eq_single j]
  · by_cases h : i = j + 1 <;> simp [h]
  · intro k _ hk; simp [hk]
  · simp

/-- Native tick from four clock events. -/
def tick (F : Fin 4 → Matrix a a ℂ) : Matrix a a ℂ := F 3 * F 2 * F 1 * F 0

theorem cycle (F : Fin 4 → Matrix a a ℂ) (ψ : a → ℂ) :
    (clocked F) ^ 4 *ᵥ held 0 ψ = held 0 (tick F *ᵥ ψ) := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← mulVec_mulVec, step]
  simp only [tick, ← mulVec_mulVec]
  congr 1

/-- **Clock calibration.** `4m` clock events from phase zero are `m` ticks, for every state. -/
theorem ticks (F : Fin 4 → Matrix a a ℂ) (m : ℕ) (ψ : a → ℂ) :
    (clocked F) ^ (4 * m) *ᵥ held 0 ψ = held 0 ((tick F) ^ m *ᵥ ψ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 4 * (m + 1) = 4 + 4 * m by ring, pow_add, ← mulVec_mulVec, ih, cycle,
      pow_succ', ← mulVec_mulVec]

omit [DecidableEq a] in
/-- **Observed clock.** If each native factor is observed as a concrete factor, the readout
of the clocked native schedule follows the clocked concrete schedule at every event. -/
theorem observed {b : Type*} [Fintype b] [DecidableEq b] (E : Matrix a b ℂ)
    (F : Fin 4 → Matrix a a ℂ) (f : Fin 4 → Matrix b b ℂ)
    (h : ∀ j, NativeObservation.Obs E (F j) (f j)) (j : Fin 4) (ψ : a → ℂ) :
    held (j + 1) (Eᴴ *ᵥ (F j *ᵥ ψ)) = clocked f *ᵥ held j (Eᴴ *ᵥ ψ) := by
  rw [step, NativeObservation.readout (h j)]

/-! ## The native carrier split on its clock -/

open NativeSplit
open scoped Kronecker

variable (c : Fin 3) (p : ℝ) {X : Type*} [Fintype X] [DecidableEq X]

instance : DecidableEq (Fin 4 × (X × L c)) := instDecidableEqProd

/-- Factor order: directions 2, 1, 0, then the on-site coin. -/
def factors (e : Fin 3 → Equiv.Perm X) (τ : ℝ) : Fin 4 → Matrix (X × L c) (X × L c) ℂ :=
  ![directionN c p (e 2) 2 τ, directionN c p (e 1) 1 τ, directionN c p (e 0) 0 τ,
    (1 : Matrix X X ℂ) ⊗ₖ coinN c p τ]

theorem tick_eq (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    tick (factors c p e τ) = updateN c p e τ := by
  simp [tick, factors, updateN, Matrix.mul_assoc]

/-- **One clock, one native update.** Four clock events per tick realize the native
split on carrier labels, for every state. -/
theorem native_ticks (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (m : ℕ) (ψ : X × L c → ℂ) :
    (clocked (factors c p e τ)) ^ (4 * m : ℕ) *ᵥ held 0 ψ = held 0 ((updateN c p e τ) ^ m *ᵥ ψ) := by
  rw [ticks, tick_eq]

end PMAction.Clock
