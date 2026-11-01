import PMAction.SectorObservation
import PMAction.SplitCovariance

/-!
# Common vacuum dynamics across the three native glue-class sectors

Each actual glue class has its own two-wall native amplitude space and the
same coordinate-observed vacuum Hamiltonian. Their direct sum therefore has
48 native labels and 24 coordinate modes, with class-independent wall parity.
This is a consistent representation route, rather than a selection of three
physical generations. Admitting all three classes simultaneously, coordinate
observations, coherent phases, controls and microscopic prices remain inputs.
The wall-covariance theorem below is at the readout; full native wall symmetry
is not inferred from an observed symmetry.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.CarrierClassBundle
open Matrix NativeObservation
open scoped Matrix.Norms.L2Operator

abbrev Native := Σ c : Fin 3, CarrierVacuumSector.Labels c
abbrev Modes := Σ _ : Fin 3, ConcreteFermion.Sites

def encoding : Matrix Native Modes ℂ :=
  SectorObservation.encoding CarrierVacuumSector.embedding

def generator (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) : Matrix Native Native ℂ :=
  blockDiagonal' (fun c => NativeSector.nativeHamiltonian c p k δ)

def observedGenerator (k : Fin 3 → ℝ) (δ : ℝ) : Matrix Modes Modes ℂ :=
  blockDiagonal' (fun _ : Fin 3 => ConcreteFermion.hamiltonian k δ)

theorem native_card : Fintype.card Native = 48 := by
  simp [Native, CarrierVacuumSector.Labels, Fintype.card_sigma, Fintype.card_sum,
    CarrierEvents.carrier_card]

theorem observed_card : Fintype.card Modes = 24 := by decide

theorem isometry : encodingᴴ * encoding = 1 :=
  SectorObservation.isometry _ CarrierVacuumSector.isometry

theorem generator_hermitian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :
    (generator p k δ).IsHermitian :=
  SectorObservation.hermitian _ (fun c => NativeSector.nativeHamiltonian_hermitian c p k δ)

theorem generator_observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) : Obs encoding (generator p k δ) (observedGenerator k δ) :=
  SectorObservation.observed _ _ _ (fun _ => NativeSector.native_obs hp hp1 k δ)

/-- No invisible-mode feedback, for every ambient amplitude and complex evolution parameter. -/
theorem evolution_readout (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ) (ψ : Native → ℂ) :
    encodingᴴ *ᵥ (NormedSpace.exp (z • generator p k δ) *ᵥ ψ) =
      NormedSpace.exp (z • observedGenerator k δ) *ᵥ (encodingᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (generator_observed p hp hp1 k δ) z) ψ

/-- Native wall exchange with the already certified spinor parity word in each class. -/
def wallParityNative : Matrix Native Native ℂ := blockDiagonal' (fun c : Fin 3 =>
  fromBlocks 0 (CarrierVacuumSector.beta c) (CarrierVacuumSector.beta c) 0)

def wallParity : Matrix Modes Modes ℂ := blockDiagonal' (fun _ : Fin 3 => SplitCovariance.P8)

theorem wallParity_observed : Obs encoding wallParityNative wallParity := by
  apply SectorObservation.observed
  intro c
  exact NativeObservation.blocks NativeObservation.zero (NativeSector.beta_obs c)
    (NativeSector.beta_obs c) NativeObservation.zero

theorem wallParity_preserves_class (c d : Fin 3) (i j : ConcreteFermion.Sites) (h : c ≠ d) :
    wallParity ⟨c, i⟩ ⟨d, j⟩ = 0 :=
  blockDiagonal'_apply_ne (fun _ : Fin 3 => SplitCovariance.P8) i j h

/-- Wall parity is the same operator in every class sector, rather than a
class-dependent permutation of packet labels. -/
theorem wallParity_same (c : Fin 3) (i j : ConcreteFermion.Sites) :
    wallParity ⟨c, i⟩ ⟨c, j⟩ = SplitCovariance.P8 i j :=
  blockDiagonal'_apply_eq (fun _ : Fin 3 => SplitCovariance.P8) c i j

theorem wall_covariance (k : Fin 3 → ℝ) (δ : ℝ) :
    wallParity * observedGenerator k δ * wallParity = observedGenerator (-k) δ := by
  simp only [wallParity, observedGenerator, ← blockDiagonal'_mul,
    SplitCovariance.hamiltonian_conjugates]

/-- The native conjugated update has the correct readout covariance. No equality
on its unobserved complement is asserted. -/
theorem native_observed_covariance (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    Obs encoding (wallParityNative * generator p k δ * wallParityNative)
      (observedGenerator (-k) δ) := by
  have h := NativeObservation.mul (NativeObservation.mul wallParity_observed
    (generator_observed p hp hp1 k δ)) wallParity_observed
  rwa [wall_covariance] at h

/-- The unsplit class sectors have the same energy eigenvalue for every class
superposition. Replicating the native vacuum does not select mass splittings
or a preferred class basis. -/
theorem common_eigenvalue (k : Fin 3 → ℝ) (δ : ℝ) (energy : ℂ)
    (v : ConcreteFermion.Sites → ℂ)
    (hv : ConcreteFermion.hamiltonian k δ *ᵥ v = energy • v) (w : Fin 3 → ℂ) :
    observedGenerator k δ *ᵥ (fun q : Modes => w q.1 * v q.2) =
      energy • (fun q : Modes => w q.1 * v q.2) := by
  ext ⟨c, i⟩
  rw [observedGenerator, SectorObservation.action_fibre]
  change (ConcreteFermion.hamiltonian k δ *ᵥ (w c • v)) i = _
  rw [Matrix.mulVec_smul, hv]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end PMAction.CarrierClassBundle
