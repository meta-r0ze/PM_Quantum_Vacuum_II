import PMArch.NetCost
import Mathlib.Tactic

/-! Weighted finite-event accounting. The event law is supplied; linearity
neither requires independence nor selects that law. Uniform sampling recovers Paper I. -/
noncomputable section
namespace PMAction.EventAccounting
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def eventMass (mass : Ω → ℝ) (E : Finset Ω) : ℝ := ∑ ω ∈ E, mass ω

def cost (toll : ℝ) (mass : Ω → ℝ) {n : ℕ} (E : Fin n → Finset Ω) : ℝ :=
  ∑ ω, mass ω*(toll*∑ i, if ω ∈ E i then (1 : ℝ) else 0)

/-- One common primitive toll, with each event counted exactly once. -/
theorem weighted_linear (toll : ℝ) (mass : Ω → ℝ) {n : ℕ} (E : Fin n → Finset Ω) :
    cost toll mass E=toll*∑ i, eventMass mass (E i) := by
  calc
    cost toll mass E = ∑ i, toll*∑ ω, if ω ∈ E i then mass ω else 0 := by
      unfold cost
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro ω _
      split_ifs <;> simp_all <;> ring
    _ = ∑ i, toll*eventMass mass (E i) := by
      apply sum_congr rfl
      intro i _
      congr 1
      rw [← sum_filter]
      simp [eventMass]
    _ = toll*∑ i, eventMass mass (E i) := (mul_sum _ _ _).symm

/-- The old uniform counting theorem is a special case of the same event accounting. -/
theorem uniform_recovers_netCost (toll : ℝ) {n : ℕ} (E : Fin n → Finset Ω) :
    cost toll (fun _ => 1/(Fintype.card Ω : ℝ)) E=PMArch.NetCost.expectedCost toll E := by
  unfold cost PMArch.NetCost.expectedCost
  rw [sum_div]
  apply sum_congr rfl
  intro ω _
  ring

def binaryMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

theorem binary_normalized (p : ℝ) : (∑ b, binaryMass p b)=1 := by
  simp [binaryMass, Fintype.sum_bool]

theorem binary_nonnegative {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∀ b, 0 ≤ binaryMass p b := by
  intro b; cases b <;> simp [binaryMass] <;> linarith

/-- An explicit binary event, not a cost defined directly as a curvature score. -/
theorem binary_flag_cost (toll p : ℝ) :
    cost toll (binaryMass p) (fun _ : Fin 1 => ({true} : Finset Bool))=toll*p := by
  rw [weighted_linear]
  simp [eventMass, binaryMass]

end PMAction.EventAccounting
