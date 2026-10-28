import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-! Finite Gibbs survival model. The exponential law is a stated model input;
its ordering, normalization and finite-temperature limitations are proved. -/
noncomputable section
namespace PMAction
open Finset

def weight (β action : ℝ) : ℝ := Real.exp (-β * action)

theorem weight_pos (β action : ℝ) : 0 < weight β action := Real.exp_pos _

theorem weight_add (β a b : ℝ) : weight β (a+b) = weight β a * weight β b := by
  simp only [weight, ← Real.exp_add]
  congr 1
  ring

theorem survival_ratio (β a b : ℝ) : weight β b / weight β a = weight β (b-a) := by
  rw [weight, weight, ← Real.exp_sub, weight]
  congr 1
  ring

theorem weight_order {β a b : ℝ} (hβ : 0 < β) :
    weight β b ≤ weight β a ↔ a ≤ b := by
  simp only [weight, Real.exp_le_exp]
  constructor <;> intro h <;> nlinarith

/-- A finite action penalty suppresses a history but does not eliminate it. -/
theorem finite_penalty_survives (β a δ : ℝ) :
    0 < weight β (a+δ) / weight β a := div_pos (weight_pos _ _) (weight_pos _ _)

def partition {ι : Type*} [Fintype ι] (β : ℝ) (S : ι → ℝ) : ℝ := ∑ i, weight β (S i)

def probability {ι : Type*} [Fintype ι] (β : ℝ) (S : ι → ℝ) (i : ι) : ℝ :=
  weight β (S i) / partition β S

theorem partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (S : ι → ℝ) :
    0 < partition β S := by
  exact sum_pos (fun _ _ => weight_pos _ _) univ_nonempty

theorem probabilities_sum_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (S : ι → ℝ) : ∑ i, probability β S i = 1 := by
  simp only [probability, ← sum_div]
  exact div_self (ne_of_gt (partition_pos β S))

theorem probability_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (S : ι → ℝ) (i : ι) : 0 < probability β S i :=
  div_pos (weight_pos _ _) (partition_pos _ _)

/-- Stationarity by itself does not select a minimum. -/
theorem stationary_not_minimal :
    let p : Polynomial ℝ := -Polynomial.X^2
    p.derivative.eval 0 = 0 ∧ p.eval 1 < p.eval 0 := by
  norm_num

/-- A dissipation budget constrains a product without determining each factor. -/
theorem complexity_speed_bound {ξ K f C : ℝ} (hξ : 0 < ξ) (hK : 0 < K)
    (hbudget : ξ * K * f ≤ C) : f ≤ C / (ξ*K) := by
  apply (le_div_iff₀ (mul_pos hξ hK)).mpr
  nlinarith

/-- A positive dissipation density cannot be identified with an unrestricted
Lorentzian quadratic form by algebra alone. -/
theorem lorentzian_cost_not_nonnegative :
    ¬ ∀ t x : ℝ, 0 ≤ -t^2+x^2 := by
  intro h
  have := h 1 0
  norm_num at this

end PMAction
