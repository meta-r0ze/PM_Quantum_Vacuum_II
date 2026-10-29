import PMAction.ConcreteFermion
import PMAction.ChargedCurrent

/-!
# The charged chiral projector on the actual domain-wall zero kernel

The existing (1-Gamma)/2 projector selects the second, negative-Gamma wall
when restricted to the concrete zero-momentum kernel. It is not the full
zero-mode projector: its range also contains gapped states. Calling this
wall physical left chirality, attaching the weak gauge representation and
extending the identification away from the zero kernel remain inputs.
-/
noncomputable section
namespace PMAction.WallChiralCurrent
open Matrix ConcreteFermion

/-- Dirac gamma matrices reconstructed from the actual Hamiltonian matrices,
with signature (+---) and the displayed orientation convention. -/
def diracGamma : Fin 4 → Spin := ![beta, beta * alpha 0, beta * alpha 1, beta * alpha 2]

/-- The oriented product fixes the chirality operator in this representation. -/
def gammaFive : Spin := Complex.I •
  (diracGamma 0 * diracGamma 1 * diracGamma 2 * diracGamma 3)

theorem gammaFive_eq : gammaFive = gamma := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gammaFive, diracGamma, beta, alpha, gamma, mul_apply, Fin.sum_univ_four]

/-- Same concrete chirality operator on each wall. -/
def chirality : Matrix Sites Sites ℂ := fromBlocks gamma 0 0 gamma

/-- The full wall chirality is the same Dirac-product operator on each wall. -/
theorem chirality_from_dirac : chirality = fromBlocks gammaFive 0 0 gammaFive := by
  rw [gammaFive_eq]
  rfl

def projector : Matrix Sites Sites ℂ := (1/2 : ℂ) • (1-chirality)

/-- The second summand; wall names are kept separate from physical left/right labels. -/
def secondWall (v : Sites → ℂ) : Sites → ℂ := Sum.elim (fun _ => 0) (fun a => v (.inr a))

theorem chirality_square : chirality * chirality = 1 := by
  simp [chirality, fromBlocks_multiply, gamma_square, ← fromBlocks_one]

theorem projector_idempotent : projector * projector = projector :=
  ChargedCurrent.projector_idempotent chirality chirality_square

/-- On every actual zero mode the projector is exactly second-wall restriction. -/
theorem kernel_projector (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) :
    projector *ᵥ v = secondWall v := by
  have hc := (kernel_coordinates v).mp hv
  ext c
  rcases c with a | a <;> fin_cases a <;>
    simp [projector, chirality, secondWall, gamma, mulVec, dotProduct, Fin.sum_univ_four, hc.1, hc.2.1,
      hc.2.2.1, hc.2.2.2] <;> ring

theorem projected_zero_mode (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) :
    hamiltonian 0 0 *ᵥ (projector *ᵥ v) = 0 := by
  rw [kernel_projector v hv, kernel_coordinates]
  have hc := (kernel_coordinates v).mp hv
  simpa [secondWall] using hc.2.2

/-- The selected zero modes have no amplitude on the positive-Gamma first wall. -/
theorem selected_iff (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) :
    projector *ᵥ v = v ↔ ∀ a, v (.inl a) = 0 := by
  rw [kernel_projector v hv]
  constructor
  · intro h a
    exact (congrFun h (.inl a)).symm
  · intro h
    ext c
    rcases c with a | a <;> simp [secondWall, h]

/-- The charged-current coefficient specializes to the actual kernel projector. -/
theorem vertex_on_kernel (g : ℂ) (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) :
    ((g / (2 * Real.sqrt 2)) • (1-chirality)) *ᵥ v =
      (g / Real.sqrt 2) • secondWall v := by
  rw [← ChargedCurrent.vertex_coefficient chirality g, smul_mulVec]
  exact congrArg ((g / Real.sqrt 2) • ·) (kernel_projector v hv)

/-- Without the kernel restriction the chiral projector also retains a gapped state. -/
theorem projector_not_vacuum_projector :
    ∃ v : Sites → ℂ, projector *ᵥ v = v ∧ hamiltonian 0 0 *ᵥ v ≠ 0 := by
  let v : Sites → ℂ := Sum.elim ![0,0,1,0] (fun _ => 0)
  refine ⟨v, ?_, ?_⟩
  · ext c
    rcases c with a | a <;> fin_cases a <;>
      norm_num [v, projector, chirality, gamma, sub_mulVec, smul_mulVec,
        fromBlocks_mulVec, mulVec, dotProduct, Fin.sum_univ_four]
  · intro h
    have hc := (kernel_coordinates v).mp h
    norm_num [v] at hc

/-- The plain exchange of wall labels is not a symmetry of the present
chiral hopping Hamiltonian. An E8 sector-swap automorphism alone cannot supply it. -/
theorem plain_wall_exchange_fails :
    (fromBlocks 0 1 1 0 : Matrix Sites Sites ℂ) * hamiltonian 0 0 ≠
      hamiltonian 0 0 * (fromBlocks 0 1 1 0 : Matrix Sites Sites ℂ) := by
  intro h
  have hh := congrFun (congrFun h (.inl 0)) (.inl 2)
  norm_num [hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
    DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
    DomainWallSpectrum.minus, fromBlocks_multiply, beta, gamma, mul_apply, vecMul, dotProduct,
    Fin.sum_univ_four] at hh

end PMAction.WallChiralCurrent
