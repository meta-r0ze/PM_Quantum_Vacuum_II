import PMArch.NetCost
import PMArch.Impedance

/-!
# Economy and positive prices from Paper I's survival law

Paper III's remaining selections (single ownership, fewest insertions) use **Economy with a
positive price per event**. Both parts follow from Paper I.

* `survival_strictAnti`, `most_persistent_iff_cheapest`: Paper I prices persistence as survival
  `P = exp(−β · cost)` with hazard `β > 0` (`NetCost.survival_factorizes`). Then the option that
  persists best is exactly the cheapest one. Economy is the persistence postulate, read through
  the survival law, and not a separate rule.
* `event_price_pos`: the cost of an event is its expected number of transitions times the toll
  `c₀` (`NetCost.expected_count_linear`). Closure sets `c₀ = 1`. So any event that occurs with
  positive probability has a strictly positive price.
* `toll_pos`: Paper I's derived Toll is itself positive.

Still an input: the hazard `β` is positive. This is what "cost" means: cost lowers survival.
-/

noncomputable section
namespace PMAction.PersistenceSelection

/-- Survival falls strictly with cost. -/
theorem survival_strictAnti (β : ℝ) (hβ : 0 < β) : StrictAnti (fun c : ℝ => Real.exp (-β * c)) :=
  fun a b hab => Real.exp_lt_exp.mpr (by nlinarith)

/-- **Economy from survival.** Among options with costs `C`, the one that persists best is
exactly the cheapest. -/
theorem most_persistent_iff_cheapest {ι : Type*} (β : ℝ) (hβ : 0 < β) (C : ι → ℝ) (i : ι) :
    (∀ j, Real.exp (-β * C j) ≤ Real.exp (-β * C i)) ↔ ∀ j, C i ≤ C j := by
  refine forall_congr' fun j => ?_
  exact (survival_strictAnti β hβ).le_iff_ge

/-- **Every occurring event has a positive price.** With the transition toll `c₀ = 1` (Closure),
an event of positive probability `p` costs `c₀ · p > 0`. -/
theorem event_price_pos (c₀ p : ℝ) (hc : c₀ = 1) (hp : 0 < p) : 0 < c₀ * p := by
  rw [hc, one_mul]; exact hp

/-- Paper I's derived Toll is positive. -/
theorem toll_pos : 0 < PMArch.tollTerm PMArch.baseline := by
  norm_num [PMArch.tollTerm, PMArch.baseline, PMArch.Parameters.eulerCharacteristic,
    PMArch.Parameters.resolution, PMArch.Parameters.embeddingDimension,
    PMArch.Parameters.nodeCapacity]

end PMAction.PersistenceSelection
