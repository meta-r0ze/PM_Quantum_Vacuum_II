import PMAction.ChiralRegisterCurrent
import PMAction.RegisterSplit

/-!
# Capacity-aware coexistence of a chiral charge and a reference register

The second Boolean bank has explicit payload × record labels. A supplied
record permutation, including an existing finite native reference lookup,
retains the payload. Chiral-charge evolution and record routing commute at
the readout for every ambient amplitude. They are not asserted equal on
unobserved sectors. The register count includes the whole product label.

This is a finite allocation witness. It does not prepare the reference, select
its source, supply an infinite fresh-record orbit, or price routing/maintenance.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RegisterReference
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker
variable (c : Fin 3) {X n r : Type*} [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

abbrev Config := RegisterSplit.Config (X := X) (b := n × r) c
abbrev Modes := (X × ConcreteFermion.Sites) × (n × r)

def route (e : Equiv.Perm r) : Matrix (Config (X := X) (n := n) (r := r) c) (Config (X := X) (n := n) (r := r) c) ℂ :=
  (update (Equiv.refl (X × RegisterVacuum.Labels c)) (Equiv.prodCongr (Equiv.refl n) e)).permMatrix ℂ

def routeReadout (e : Equiv.Perm r) : Matrix (Modes (X := X) (n := n) (r := r)) (Modes (X := X) (n := n) (r := r)) ℂ :=
  (1 : Matrix (X × ConcreteFermion.Sites) (X × ConcreteFermion.Sites) ℂ) ⊗ₖ
    ((1 : Matrix n n ℂ) ⊗ₖ e.permMatrix ℂ)

def charge (B : Matrix n n ℂ) : Matrix (Config (X := X) (n := n) (r := r) c) (Config (X := X) (n := n) (r := r) c) ℂ :=
  RegisterInteraction.interaction ((1 : Matrix X X ℂ) ⊗ₖ RegisterVacuum.nativeProjector c)
    (B ⊗ₖ (1 : Matrix r r ℂ))

def chargeReadout (B : Matrix n n ℂ) : Matrix (Modes (X := X) (n := n) (r := r)) (Modes (X := X) (n := n) (r := r)) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ WallChiralCurrent.projector) ⊗ₖ (B ⊗ₖ (1 : Matrix r r ℂ))

omit [DecidableEq X] [DecidableEq n] [DecidableEq r] in
theorem register_count : Fintype.card ((X × RegisterVacuum.Labels c) ⊕ (n × r)) =
    16 * Fintype.card X + Fintype.card n * Fintype.card r := by
  simp [RegisterVacuum.Labels, CarrierVacuumSector.Labels, CarrierEvents.carrier_card, Nat.mul_comm]

theorem route_observed (e : Equiv.Perm r) :
    Obs (RegisterSplit.embedding (X := X) (b := n × r) c) (route c e) (routeReadout (X := X) e) := by
  have hfirst := IndependentRegisters.tensor_observed (Equiv.refl (X × RegisterVacuum.Labels c))
    (Equiv.prodCongr (Equiv.refl n) e)
  simp only [permMatrix_refl, IndependentRegisters.tensor_permutation] at hfirst
  apply NativeObservation.compose hfirst
  exact NativeObservation.tensor
    (NativeObservation.one : Obs (NativeSplit.emb c) 1 1)
    (show Obs (1 : Matrix (n × r) (n × r) ℂ)
      ((1 : Matrix n n ℂ) ⊗ₖ e.permMatrix ℂ) ((1 : Matrix n n ℂ) ⊗ₖ e.permMatrix ℂ)
      from ⟨by simp, by simp⟩)

theorem charge_observed (B : Matrix n n ℂ) (hB : B.IsHermitian) :
    Obs (RegisterSplit.embedding (X := X) (b := n × r) c) (charge c B) (chargeReadout (X := X) B) := by
  have hA : ((1 : Matrix X X ℂ) ⊗ₖ RegisterVacuum.nativeProjector c).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, conjTranspose_one, (RegisterVacuum.projector_hermitian c).eq]
  have hR : (B ⊗ₖ (1 : Matrix r r ℂ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, hB.eq, conjTranspose_one]
  apply NativeObservation.compose (RegisterInteraction.observed _ _ hA hR)
  exact NativeObservation.tensor
    (NativeObservation.kron 1 (RegisterVacuum.native_projector_observed c))
    (show Obs (1 : Matrix (n × r) (n × r) ℂ) (B ⊗ₖ (1 : Matrix r r ℂ))
      (B ⊗ₖ (1 : Matrix r r ℂ)) from ⟨by simp, by simp⟩)

theorem charge_unitary (B : Matrix n n ℂ) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • charge (X := X) (r := r) c B) ∈ unitary _ :=
  RegisterInteraction.evolution_unitary _ _ t

theorem route_unitary (e : Equiv.Perm r) : route (X := X) (n := n) c e ∈ unitary _ := by
  constructor <;> simp [route, star_eq_conjTranspose, ← permMatrix_mul]

theorem readout_commutes (B : Matrix n n ℂ) (e : Equiv.Perm r) :
    chargeReadout (X := X) B * routeReadout (X := X) e = routeReadout (X := X) e * chargeReadout (X := X) B := by
  simp [chargeReadout, routeReadout, ← mul_kronecker_mul]

/-- The current and reference route have order-independent readout, also for
unencoded inputs and arbitrary complex evolution parameters. -/
theorem evolution_route_readout (B : Matrix n n ℂ) (hB : B.IsHermitian)
    (e : Equiv.Perm r) (z : ℂ) (ψ : Config (n := n) c → ℂ) :
    (RegisterSplit.embedding (X := X) c)ᴴ *ᵥ
      (NormedSpace.exp (z • charge c B) *ᵥ (route c e *ᵥ ψ)) =
    (RegisterSplit.embedding (X := X) c)ᴴ *ᵥ
      (route c e *ᵥ (NormedSpace.exp (z • charge c B) *ᵥ ψ)) := by
  have hc : Commute (z • chargeReadout (X := X) B) (routeReadout (X := X) e) := by
    change (z • chargeReadout (X := X) B) * routeReadout (X := X) e = routeReadout (X := X) e * (z • chargeReadout (X := X) B)
    rw [Matrix.smul_mul, Matrix.mul_smul, readout_commutes]
  have he := hc.exp_left
  have hq := NativeObservation.exp (charge_observed (X := X) (r := r) c B hB) z
  have hr := route_observed (X := X) (n := n) c e
  rw [NativeObservation.readout hq, NativeObservation.readout hr,
    NativeObservation.readout hr, NativeObservation.readout hq,
    mulVec_mulVec, he.eq, ← mulVec_mulVec]

end PMAction.RegisterReference
