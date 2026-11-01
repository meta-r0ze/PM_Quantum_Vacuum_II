import PMAction.RegisterVacuum
import PMAction.TensorEvolution
import PMAction.ClockDynamics

/-!
# The full real-space split and four-phase clock on register configurations

The first bank carries spatial site × native carrier; the payload bank remains
independent. The three directional generators and the two on-site generators
are lifted by the number-conserving Boolean construction. Their five exponential
pulses form the existing four high-level factors. Every tick and every clock
phase has exact all-state readout as the corrected split.

This extends the directional-exponential completion; it does not assert its
finite-range locality or identify it with `LocalIsometricDynamics`. Banks,
preparation, phase admission, physical clock calibration and primitive prices
remain inputs. Four phases and five pulses are not primitive E8 event prices.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RegisterSplit
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker
variable (c : Fin 3) (p : ℝ) {X b : Type*}
  [Fintype X] [DecidableEq X] [Fintype b] [DecidableEq b]

abbrev Native := X × CarrierVacuumSector.Labels c
abbrev Config := Configuration (Native (X := X) c) b
abbrev Modes := (X × ConcreteFermion.Sites) × b

def embedding : Matrix (Config (X := X) (b := b) c) (Modes (X := X) (b := b)) ℂ :=
  IndependentRegisters.embedding * (NativeSplit.emb c ⊗ₖ (1 : Matrix b b ℂ))

theorem isometry : (embedding (X := X) (b := b) c)ᴴ * embedding (X := X) (b := b) c = 1 :=
  compose_isometry _ _ IndependentRegisters.isometry
    (tensor_isometry _ _ (NativeSplit.emb_isometry c) (by simp))

def pulse (A : Matrix (Native (X := X) c) (Native (X := X) c) ℂ) (t : ℝ) :
    Matrix (Config (X := X) (b := b) c) (Config (X := X) (b := b) c) ℂ :=
  NormedSpace.exp ((-Complex.I * t) • RegisterHamiltonian.generator A)

theorem pulse_unitary (A : Matrix (Native (X := X) c) (Native (X := X) c) ℂ) (t : ℝ) :
    pulse (b := b) c A t ∈ unitary _ := RegisterHamiltonian.evolution_unitary A t

theorem pulse_observed (A : Matrix (Native (X := X) c) (Native (X := X) c) ℂ)
    (hA : A.IsHermitian) (t : ℝ) :
    Obs IndependentRegisters.embedding (pulse (b := b) c A t)
      (NormedSpace.exp ((-Complex.I * t) • A) ⊗ₖ (1 : Matrix b b ℂ)) := by
  have hh := NativeObservation.exp (RegisterHamiltonian.generator_observed (b := b) A hA)
    (-Complex.I * (t : ℂ))
  rwa [TensorEvolution.scaled_right] at hh

def direction (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :=
  pulse (b := b) c (NativeSplit.neighborN c p e j) (-τ)

private theorem direction_observed (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    Obs IndependentRegisters.embedding (direction (b := b) c p e j τ)
      (NativeSplit.directionN c p e j τ ⊗ₖ (1 : Matrix b b ℂ)) := by
  simpa [direction, NativeSplit.directionN, mul_neg, neg_mul] using
    pulse_observed (b := b) c (NativeSplit.neighborN c p e j)
      (NativeSplit.neighborN_hermitian c p e j) (-τ)

def coin (τ : ℝ) : Matrix (Config (X := X) (b := b) c) (Config (X := X) (b := b) c) ℂ :=
  pulse c ((1 : Matrix X X ℂ) ⊗ₖ NativeSector.nativeHamiltonian c p 0 0) τ *
    pulse c ((1 : Matrix X X ℂ) ⊗ₖ NativeSplit.betaL c) (3 * τ)

omit [Fintype X] in
private theorem one_tensor_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ((1 : Matrix X X ℂ) ⊗ₖ A).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_kronecker, conjTranspose_one, hA.eq]

private theorem coin_observed (τ : ℝ) :
    Obs IndependentRegisters.embedding (coin (X := X) (b := b) c p τ)
      (((1 : Matrix X X ℂ) ⊗ₖ NativeSplit.coinN c p τ) ⊗ₖ (1 : Matrix b b ℂ)) := by
  have h1 := pulse_observed (b := b) c
    ((1 : Matrix X X ℂ) ⊗ₖ NativeSector.nativeHamiltonian c p 0 0)
    (one_tensor_hermitian _ (NativeSector.nativeHamiltonian_hermitian c p 0 0)) τ
  have h2 := pulse_observed (b := b) c
    ((1 : Matrix X X ℂ) ⊗ₖ NativeSplit.betaL c)
    (one_tensor_hermitian _ (NativeSplit.betaL_hermitian c)) (3 * τ)
  have hh := NativeObservation.mul h1 h2
  simpa only [TensorEvolution.scaled_left, ← mul_kronecker_mul, Matrix.one_mul,
    NativeSplit.coinN, coin] using hh

def factors (e : Fin 3 → Equiv.Perm X) (τ : ℝ) : Fin 4 →
    Matrix (Config (X := X) (b := b) c) (Config (X := X) (b := b) c) ℂ :=
  ![direction c p (e 2) 2 τ, direction c p (e 1) 1 τ,
    direction c p (e 0) 0 τ, coin c p τ]

def observedFactors (e : Fin 3 → Equiv.Perm X) (τ : ℝ) : Fin 4 →
    Matrix (X × ConcreteFermion.Sites) (X × ConcreteFermion.Sites) ℂ :=
  ![SplitUpdate.direction (e 2) 2 τ, SplitUpdate.direction (e 1) 1 τ,
    SplitUpdate.direction (e 0) 0 τ, (1 : Matrix X X ℂ) ⊗ₖ VacuumSplit.onsiteCoin τ]

theorem factor_unitary (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (j : Fin 4) :
    factors (b := b) c p e τ j ∈ unitary _ := by
  fin_cases j
  · exact pulse_unitary c _ _
  · exact pulse_unitary c _ _
  · exact pulse_unitary c _ _
  · exact (unitary _).mul_mem (pulse_unitary c _ _) (pulse_unitary c _ _)

theorem clock_unitary (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    Clock.clocked (factors (b := b) c p e τ) ∈ unitary _ :=
  ClockDynamics.clocked_unitary (factors (b := b) c p e τ) (factor_unitary (b := b) c p e τ)

theorem factor_observed (hp : 0 < p) (hp1 : p < 1/2)
    (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (j : Fin 4) :
    Obs (embedding (b := b) c) (factors c p e τ j)
      (observedFactors e τ j ⊗ₖ (1 : Matrix b b ℂ)) := by
  have hfirst : Obs IndependentRegisters.embedding (factors (b := b) c p e τ j)
      (Clock.factors c p e τ j ⊗ₖ (1 : Matrix b b ℂ)) := by
    fin_cases j
    · exact direction_observed c p _ _ _
    · exact direction_observed c p _ _ _
    · exact direction_observed c p _ _ _
    · exact coin_observed c p τ
  have hsecond : Obs (NativeSplit.emb c) (Clock.factors c p e τ j)
      (observedFactors e τ j) := by
    fin_cases j
    · exact NativeSplit.direction_obs hp hp1 _ _ _
    · exact NativeSplit.direction_obs hp hp1 _ _ _
    · exact NativeSplit.direction_obs hp hp1 _ _ _
    · exact NativeObservation.kron 1 (NativeSplit.coin_obs hp hp1 τ)
  exact NativeObservation.compose hfirst (NativeObservation.tensor hsecond
    (NativeObservation.one : Obs (1 : Matrix b b ℂ) 1 1))

def update (e : Fin 3 → Equiv.Perm X) (τ : ℝ) := Clock.tick (factors (b := b) c p e τ)

def observedUpdate (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    Matrix (Modes (X := X) (b := b)) (Modes (X := X) (b := b)) ℂ :=
  SplitUpdate.update e (VacuumSplit.onsiteCoin τ) τ ⊗ₖ (1 : Matrix b b ℂ)

theorem update_unitary (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    update (b := b) c p e τ ∈ unitary _ :=
  (unitary _).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem
    (factor_unitary (b := b) c p e τ 3) (factor_unitary (b := b) c p e τ 2))
    (factor_unitary (b := b) c p e τ 1)) (factor_unitary (b := b) c p e τ 0)

theorem update_observed (hp : 0 < p) (hp1 : p < 1/2) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    Obs (embedding (b := b) c) (update c p e τ) (observedUpdate e τ) := by
  have hh := NativeObservation.mul (NativeObservation.mul (NativeObservation.mul
    (factor_observed (b := b) c p hp hp1 e τ 3) (factor_observed (b := b) c p hp hp1 e τ 2))
    (factor_observed (b := b) c p hp hp1 e τ 1)) (factor_observed (b := b) c p hp hp1 e τ 0)
  simpa [update, Clock.tick, observedUpdate, observedFactors, SplitUpdate.update, SplitUpdate.onsite,
    ← mul_kronecker_mul, Matrix.mul_assoc] using hh

theorem history_readout (hp : 0 < p) (hp1 : p < 1/2) (e : Fin 3 → Equiv.Perm X)
    (τ : ℝ) (m : ℕ) (ψ : Config (X := X) (b := b) c → ℂ) :
    (embedding c)ᴴ *ᵥ ((update c p e τ) ^ m *ᵥ ψ) =
      (observedUpdate e τ) ^ m *ᵥ ((embedding c)ᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.pow (update_observed c p hp hp1 e τ) m) ψ

/-- Four high-level clock events per tick, initialized at phase zero. -/
theorem clock_ticks (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (m : ℕ)
    (ψ : Config (X := X) (b := b) c → ℂ) :
    (Clock.clocked (factors c p e τ)) ^ (4 * m) *ᵥ Clock.held 0 ψ =
      Clock.held 0 ((update c p e τ) ^ m *ᵥ ψ) := Clock.ticks _ m ψ

theorem clock_phase_readout (hp : 0 < p) (hp1 : p < 1/2)
    (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (j : Fin 4)
    (ψ : Config (X := X) (b := b) c → ℂ) :
    Clock.held (j+1) ((embedding c)ᴴ *ᵥ (factors c p e τ j *ᵥ ψ)) =
      Clock.clocked (fun k => observedFactors e τ k ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ
        Clock.held j ((embedding c)ᴴ *ᵥ ψ) :=
  Clock.observed _ _ _ (factor_observed (b := b) c p hp hp1 e τ) j ψ

end PMAction.RegisterSplit
