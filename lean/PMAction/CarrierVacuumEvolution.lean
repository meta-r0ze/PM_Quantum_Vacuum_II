import PMAction.CarrierVacuumSector
import PMAction.RectangularEvolution
import PMAction.IsometricDynamics

/-! The complete odd representation has eight coordinates, with exact full
Hamiltonian evolution and response. This is a carrier realization of the supplied
vacuum dynamics, not a proof that persistence selects amplitudes or this sector. -/
noncomputable section
namespace PMAction.CarrierVacuumEvolution
open Matrix CarrierVacuumSector
open scoped Matrix.Norms.Operator

lemma restricted_intertwining (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    hamiltonian c p k δ * embedding c = embedding c * ConcreteFermion.hamiltonian k δ := by
  rw [identification c p hp hp1, Matrix.mul_assoc, isometry, Matrix.mul_one]

/-- The full real-time evolution follows, not only its infinitesimal generator. -/
theorem evolution (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ) :
    NormedSpace.exp (z • hamiltonian c p k δ) * embedding c =
      embedding c * NormedSpace.exp (z • ConcreteFermion.hamiltonian k δ) :=
  RectangularEvolution.scaled _ _ _ (restricted_intertwining c p hp hp1 k δ) z

/-- The intrinsic odd restriction has conservative real-time evolution on the
whole ambient space, with identity evolution on its even complement. -/
theorem unitary (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ t : ℝ) :
    NormedSpace.exp (((t : ℂ)*Complex.I) • hamiltonian c p k δ) ∈
      unitary (Matrix (Labels c) (Labels c) ℂ) := by
  rw [← LinkEvolution.transport_eq_exp (hermitian c p hp hp1 k δ) t]
  exact HermitianTransport.transport_unitary _ _

/-- Response of the constructed full native-sector evolution agrees exactly. -/
theorem response (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (z : ℂ) (x : ConcreteFermion.Sites → ℂ) :
    CommonResponse.nsq (embedding c *ᵥ x -
      NormedSpace.exp (z • hamiltonian c p k δ) *ᵥ (embedding c *ᵥ x)) =
    CommonResponse.nsq (x - NormedSpace.exp (z • ConcreteFermion.hamiltonian k δ) *ᵥ x) := by
  rw [mulVec_mulVec, evolution c p hp hp1, ← mulVec_mulVec, ← Matrix.mulVec_sub]
  exact IsometricDynamics.population (embedding c) (isometry c) _

def oddSpace (c : Fin 3) := LinearMap.ker (parity c + 1).mulVecLin

lemma mem_oddSpace (c : Fin 3) (ψ : Labels c → ℂ) :
    ψ ∈ oddSpace c ↔ parity c *ᵥ ψ = -ψ := by
  change (parity c + 1) *ᵥ ψ = 0 ↔ _
  rw [add_mulVec, one_mulVec, add_eq_zero_iff_eq_neg]

/-- A canonical inverse uses coordinate readouts, not an arbitrarily chosen basis. -/
def coordinatesEquiv (c : Fin 3) : oddSpace c ≃ₗ[ℂ] (ConcreteFermion.Sites → ℂ) where
  toFun ψ := (embedding c)ᴴ *ᵥ ψ.1
  invFun x := ⟨embedding c *ᵥ x, (mem_oddSpace c _).mpr
    ((range_iff_odd c _).mp ⟨x,rfl⟩)⟩
  left_inv ψ := by
    apply Subtype.ext
    change embedding c *ᵥ ((embedding c)ᴴ *ᵥ ψ.1) = ψ.1
    obtain ⟨x,hx⟩ := (range_iff_odd c ψ.1).mpr ((mem_oddSpace c _).mp ψ.2)
    rw [← hx, mulVec_mulVec (M := (embedding c)ᴴ), isometry, one_mulVec]
  right_inv x := by
    change (embedding c)ᴴ *ᵥ (embedding c *ᵥ x)=x
    rw [mulVec_mulVec, isometry, one_mulVec]
  map_add' ψ φ := Matrix.mulVec_add _ _ _
  map_smul' a ψ := Matrix.mulVec_smul _ _ _

theorem odd_finrank (c : Fin 3) : Module.finrank ℂ (oddSpace c)=8 := by
  rw [(coordinatesEquiv c).finrank_eq]
  simp [ConcreteFermion.Sites]

/-- The even complement is inert by our extension convention, not ruled out
as nonpersistent. Selecting the physical odd sector is still an obligation. -/
theorem even_inert (c : Fin 3) (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ)
    (ψ : Labels c → ℂ) (h : parity c *ᵥ ψ=ψ) : hamiltonian c p k δ *ᵥ ψ=0 := by
  have he : oddProjector c *ᵥ ψ=0 := by
    simp [oddProjector, smul_mulVec, sub_mulVec, h]
  rw [hamiltonian, ← mulVec_mulVec, he, mulVec_zero]

end PMAction.CarrierVacuumEvolution
