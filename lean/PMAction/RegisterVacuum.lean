import PMAction.RegisterHamiltonian
import PMAction.WallChiralCurrent

/-!
# Shared vacuum/readout model on independent register banks

Every native glue-class vacuum and every supplied finite payload have this
configuration realization. The full Hermitian generator, its evolution, and
the intrinsic chiral projector are observed exactly. The banks and the Boolean
higher-occupation completion are constructions, not selected physical states,
statistics, admitted primitive gates or event prices.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RegisterVacuum
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker
variable (c : Fin 3) {b : Type*} [Fintype b] [DecidableEq b]

abbrev Labels := CarrierVacuumSector.Labels c
abbrev Config := Configuration (Labels c) b
abbrev Modes := ConcreteFermion.Sites × b

def coordinate : Matrix (Labels c × b) (Modes (b := b)) ℂ :=
  CarrierVacuumSector.embedding c ⊗ₖ (1 : Matrix b b ℂ)

def embedding : Matrix (Config (b := b) c) (Modes (b := b)) ℂ :=
  IndependentRegisters.embedding * coordinate c

theorem isometry : (embedding (b := b) c)ᴴ * embedding (b := b) c = 1 :=
  compose_isometry _ _ IndependentRegisters.isometry
    (tensor_isometry _ _ (CarrierVacuumSector.isometry c) (by simp))

/-- Supplied payload relabelings act without borrowing spinor coordinates. -/
theorem payload_permutation_observed (e : Equiv.Perm b) :
    Obs (embedding (b := b) c)
      ((update (Equiv.refl (Labels c)) e).permMatrix ℂ)
      ((1 : Matrix ConcreteFermion.Sites ConcreteFermion.Sites ℂ) ⊗ₖ e.permMatrix ℂ) := by
  apply NativeObservation.compose (tensor_observed (Equiv.refl (Labels c)) e)
  apply NativeObservation.tensor
  · simpa using (NativeObservation.one : Obs (CarrierVacuumSector.embedding c) 1 1)
  · exact ⟨by simp, by simp⟩

def generator (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) : Matrix (Config (b := b) c) (Config (b := b) c) ℂ :=
  RegisterHamiltonian.generator (NativeSector.nativeHamiltonian c p k δ)

def observedGenerator (k : Fin 3 → ℝ) (δ : ℝ) : Matrix (Modes (b := b)) (Modes (b := b)) ℂ :=
  ConcreteFermion.hamiltonian k δ ⊗ₖ (1 : Matrix b b ℂ)

theorem hermitian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :
    (generator (b := b) c p k δ).IsHermitian := RegisterHamiltonian.generator_hermitian _

theorem observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ) :
    Obs (embedding (b := b) c) (generator c p k δ) (observedGenerator k δ) := by
  apply NativeObservation.compose
    (RegisterHamiltonian.generator_observed (NativeSector.nativeHamiltonian c p k δ)
      (NativeSector.nativeHamiltonian_hermitian c p k δ))
  exact NativeObservation.tensor (NativeSector.native_obs hp hp1 k δ)
    (NativeObservation.one : Obs (1 : Matrix b b ℂ) 1 1)

theorem evolution_unitary (p : ℝ) (k : Fin 3 → ℝ) (δ t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • generator (b := b) c p k δ) ∈ unitary _ :=
  NativeObservation.exp_unitary _ (hermitian c p k δ) t

theorem evolution_readout (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ)
    (δ : ℝ) (z : ℂ) (ψ : Config (b := b) c → ℂ) :
    (embedding c)ᴴ *ᵥ (NormedSpace.exp (z • generator c p k δ) *ᵥ ψ) =
      NormedSpace.exp (z • observedGenerator k δ) *ᵥ ((embedding c)ᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (observed c p hp hp1 k δ) z) ψ

/-- Actual native gamma word on the two walls, followed by Hermitian completion. -/
def nativeChirality : Matrix (Labels c) (Labels c) ℂ :=
  let G := fromBlocks (CarrierVacuumSector.gamma c) 0 0 (CarrierVacuumSector.gamma c)
  (1/2 : ℂ) • (G + Gᴴ)

def nativeProjector : Matrix (Labels c) (Labels c) ℂ :=
  (1/2 : ℂ) • (1-nativeChirality c)

theorem chirality_hermitian : (nativeChirality c).IsHermitian := by
  unfold IsHermitian nativeChirality
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  norm_num

theorem projector_hermitian : (nativeProjector c).IsHermitian := by
  unfold IsHermitian nativeProjector
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, (chirality_hermitian c).eq]
  congr 1
  norm_num

theorem native_projector_observed : Obs (CarrierVacuumSector.embedding c)
    (nativeProjector c) WallChiralCurrent.projector := by
  have hg := NativeObservation.blocks (NativeSector.gamma_obs c) NativeObservation.zero
    NativeObservation.zero (NativeSector.gamma_obs c)
  have hherm : WallChiralCurrent.chirality.IsHermitian := by
    unfold IsHermitian WallChiralCurrent.chirality
    simp [fromBlocks_conjTranspose, ConcreteFermion.gamma_hermitian.eq]
  exact NativeObservation.smul (1/2)
    (NativeObservation.sub NativeObservation.one (NativeObservation.herm hg hherm))

end PMAction.RegisterVacuum
