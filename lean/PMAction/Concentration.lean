import PMAction.Survival

/-! Equal-time finite Gibbs histories concentrate only in a limit. Degenerate
minima retain equal shares. The exponential law is still an input. -/
noncomputable section
namespace PMAction.Concentration
open Filter Finset
open scoped Topology

theorem penalty_vanishes {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun β : ℝ => weight β δ) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hδ)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun β => by dsimp [weight]; congr 1; ring)

variable {X : Type*} [Fintype X] [DecidableEq X]

def minima (S : X → ℝ) (g : X) : Finset X := univ.filter (fun i => S i = S g)

omit [DecidableEq X] in
theorem minima_nonempty (S : X → ℝ) (g : X) : (minima S g).Nonempty :=
  ⟨g, by simp [minima]⟩

omit [Fintype X] [DecidableEq X] in
theorem relative_limit (S : X → ℝ) (g : X) (hmin : ∀ i, S g ≤ S i) (i : X) :
    Tendsto (fun β : ℝ => weight β (S i - S g)) atTop
      (𝓝 (if S i = S g then 1 else 0)) := by
  by_cases hi : S i = S g
  · simpa [hi, weight] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))
  · simpa [hi] using penalty_vanishes (lt_of_le_of_ne (hmin i) (Ne.symm hi) |> sub_pos.mpr)

omit [DecidableEq X] in
theorem probability_shift (β : ℝ) (S : X → ℝ) (g i : X) :
    probability β S i = probability β (fun j => S j - S g) i := by
  have hf : ∀ j, weight β (S j) = weight β (S g) * weight β (S j - S g) := by
    intro j
    rw [← weight_add]
    congr 1; ring
  change weight β (S i) / (∑ j, weight β (S j)) = _
  rw [hf i, show (∑ j, weight β (S j)) =
    weight β (S g) * (∑ j, weight β (S j - S g)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hf j)]
  exact mul_div_mul_left _ _ (ne_of_gt (weight_pos β (S g)))

omit [DecidableEq X] in
/-- The complete finite-ensemble zero-temperature limit, including ties. -/
theorem probability_limit (S : X → ℝ) (g : X) (hmin : ∀ i, S g ≤ S i) (i : X) :
    Tendsto (fun β : ℝ => probability β S i) atTop
      (𝓝 (if S i = S g then 1 / (minima S g).card else 0)) := by
  have hsum : Tendsto (fun β : ℝ => ∑ j, weight β (S j - S g)) atTop
      (𝓝 ((minima S g).card : ℝ)) := by
    convert tendsto_finsetSum univ (fun j _ => relative_limit S g hmin j) using 1
    simp [minima, Finset.sum_boole]
  have hn : ((minima S g).card : ℝ) ≠ 0 := by
    exact_mod_cast (minima_nonempty S g).card_pos.ne'
  have h := (relative_limit S g hmin i).div hsum hn
  have heq : (fun β : ℝ => probability β S i) =
      (fun β : ℝ => weight β (S i - S g) / ∑ j, weight β (S j - S g)) := by
    funext β; exact probability_shift β S g i
  rw [heq]
  convert h using 1
  split_ifs <;> simp

end PMAction.Concentration
