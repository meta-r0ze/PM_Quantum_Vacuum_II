import PMAction.ControllerHamiltonian
import PMAction.ReferenceMaintenance

/-!
# Constructed action-response model

This is the finite Hermitian dynamics/readout theorem, not selection of a
microscopic PM update. A Hermitian generator yields a unitary group, a unitary
comparison with exact coherent repair, and a controlled quadratic response.
The amplitude interpretation and physical preparation/primitive cost map remain
inputs. Paper-specific representations, workloads and constants stay downstream.
-/
noncomputable section
namespace PMAction.Main
open Matrix HermitianTransport CoherentComparisonRepair CommonResponse
variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}

/-- One constructed dynamics and readout, with every mathematical hypothesis
visible. The small-step restriction controls the remainder, not unitarity. -/
theorem hermitian_action_response (h : H.IsHermitian) (φ : n → ℂ) (hφ : nsq φ = 1)
    (t : ℝ) (ht : |t| ≤ radius h) :
    let U := transport h t
    U ∈ unitary (Matrix n n ℂ) ∧
      compare U ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ) ∧
      compare Uᴴ *ᵥ (compare U *ᵥ Sum.elim φ (fun _ => 0)) = Sum.elim φ (fun _ => 0) ∧
      stateFlag U φ = (1 - (star φ ⬝ᵥ (U *ᵥ φ)).re) / 2 ∧
      |nsq (φ - U *ᵥ φ) - t^2 * nsq (H *ᵥ φ)| ≤ coefficient h φ * t^4 := by
  dsimp only
  have hu := transport_unitary h t
  exact ⟨hu, compare_unitary _ hu, prepared_uncompute _ hu φ,
    state_flag_formula _ hu φ hφ, controlled_response h φ ht⟩

/-- A concrete satisfiability witness: a zero generator on one complex carrier
and its unit basis amplitude satisfy the construction's hypotheses. This is
not a claim that this witness is the physical vacuum. -/
theorem hypotheses_satisfiable : ∃ (H : Matrix (Fin 1) (Fin 1) ℂ) (φ : Fin 1 → ℂ),
    H.IsHermitian ∧ nsq φ = 1 := by
  refine ⟨0, fun _ => 1, ?_, ?_⟩
  · exact Matrix.isHermitian_zero
  · norm_num [nsq, dotProduct]

end PMAction.Main
