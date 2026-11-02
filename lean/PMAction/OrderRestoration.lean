import PMAction.OrderComparison
import PMAction.ReferenceSampling

/-!
# Exact restoration fixes the endpoint comparison response

If an update U must be undone on every input, its exact linear restorer R
satisfies RU=I and, for unitary U, is uniquely U†. On the actual transported
state, the endpoint repair flag equals the original comparison flag. This
does not identify the endpoint flag with the sum of primitive-event costs.
An executable schedule and its prices must still be supplied.

A complete orthonormal ensemble has the same mean flag before and after an
arbitrary unitary preparation. This supports pricing successive specified
events without pretending the compound endpoint is one primitive event.
Restoration requirements, preparation and physical prices remain inputs.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.OrderRestoration
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem restorer_unique (U R : Matrix n n ℂ) (hU : U ∈ unitary _) (hR : R*U=1) : R=Uᴴ := by
  have hr : U*Uᴴ=1 := hU.2
  calc
    R = R*(U*Uᴴ) := by rw [hr, mul_one]
    _ = Uᴴ := by rw [← Matrix.mul_assoc, hR, one_mul]

theorem restored_state (U R : Matrix n n ℂ) (hR : R*U=1) (ψ : n → ℂ) :
    R *ᵥ (U *ᵥ ψ) = ψ := by rw [mulVec_mulVec, hR, one_mulVec]

/-- Endpoint response is determined by the restoration task, regardless of
which implementation is used for its operator. -/
theorem repair_response (U R : Matrix n n ℂ) (hR : R*U=1) (ψ : n → ℂ) :
    CommonResponse.stateFlag R (U*ᵥ ψ) = CommonResponse.stateFlag U ψ := by
  unfold CommonResponse.stateFlag
  rw [restored_state U R hR ψ]
  have he : U*ᵥ ψ-ψ = -(ψ-U*ᵥ ψ) := by abel
  rw [he, LinkExpansion.nsq_eq, LinkExpansion.nsq_eq]
  simp only [Pi.neg_apply, Complex.normSq_neg]

theorem order_repair_response (A B R : Matrix n n ℂ) (hA : A ∈ unitary _)
    (hB : B ∈ unitary _) (hR : R*OrderComparison.compareLoop A B=1) (ψ : n → ℂ) :
    CommonResponse.stateFlag R (OrderComparison.compareLoop A B *ᵥ ψ) =
      OrderComparison.flag A B ψ := by
  rw [repair_response _ R hR ψ, OrderComparison.flag_eq_stateFlag A B hA hB ψ]

theorem adjoint_repairs (U : Matrix n n ℂ) (hU : U ∈ unitary _) : Uᴴ*U=1 := hU.1

theorem no_null_repair (U : Matrix n n ℂ) (hU : U ≠ 1) : (1:Matrix n n ℂ)*U ≠ 1 := by
  simpa using hU

/-- This is the existing readout on a supplied complete orthonormal ensemble. -/
theorem uniform_preparation_invariant {N : ℕ} (F P : Matrix (Fin N) (Fin N) ℂ)
    (hF : F ∈ unitary _) (hP : P ∈ unitary _) :
    ReferenceSampling.refFlag F P = ReferenceSampling.refFlag (1:Matrix (Fin N) (Fin N) ℂ) P := by
  have hl : Fᴴ*F=1 := hF.1
  have hr : F*Fᴴ=1 := hF.2
  rw [ReferenceSampling.ref_flag F hl P hP,
    ReferenceSampling.ref_flag 1 (by simp) P hP]
  have he : trace (Fᴴ*(1-P)*F) = trace (1-P) := by
    rw [Matrix.trace_mul_cycle, hr, one_mul]
  simp only [he, conjTranspose_one, one_mul, mul_one]

end PMAction.OrderRestoration
