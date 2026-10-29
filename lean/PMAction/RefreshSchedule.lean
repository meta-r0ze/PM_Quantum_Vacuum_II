import Mathlib.Tactic

/-!
# The refresh rule from Conservation and Economy

`GaugeLedgers` used the rule "one refresh per distinct required resource". This module derives it.

A refresh schedule for one phase is a list of resource refreshes. It is admissible under
Conservation when every required resource appears in it (nothing required is dropped).
Its cost is the sum of the weights of its entries, repeats included.

* `admissible_cost_ge`: every admissible schedule costs at least `Σ_{r ∈ R} w r` (nonnegative
  weights).
* `minimal_attained`: the schedule listing each required resource once is admissible and attains
  that cost.
* `minimal_is_ledger`: so the minimal admissible cost, the Economy choice, is exactly the ledger
  `Σ_{r ∈ R} w r`. With positive weights, a schedule with a repeat, or with an unrequired
  resource, costs strictly more (`strict_if_extra`).

For the gauge sectors this makes `GaugeLedgers.ledger` the Economy-minimal Conservation-admissible
refresh cost. The remaining premise is the requirement table itself.
-/

noncomputable section
namespace PMAction.RefreshSchedule

variable {R : Type*} [DecidableEq R]

def cost (w : R → ℝ) (L : List R) : ℝ := (L.map w).sum

def admissible (req : Finset R) (L : List R) : Prop := ∀ r ∈ req, r ∈ L

theorem cost_ge_toFinset (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (L : List R) :
    ∑ r ∈ L.toFinset, w r ≤ cost w L := by
  induction L with
  | nil => simp [cost]
  | cons a L ih =>
    simp only [cost, List.map_cons, List.sum_cons, List.toFinset_cons] at ih ⊢
    by_cases ha : a ∈ L.toFinset
    · rw [Finset.insert_eq_of_mem ha]; linarith [hw a]
    · rw [Finset.sum_insert ha]; linarith

theorem admissible_cost_ge (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (req : Finset R) (L : List R)
    (hL : admissible req L) : ∑ r ∈ req, w r ≤ cost w L := by
  have hsub : req ⊆ L.toFinset := fun r hr => List.mem_toFinset.mpr (hL r hr)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hw r)).trans
    (cost_ge_toFinset w hw L)

theorem minimal_attained (w : R → ℝ) (req : Finset R) :
    admissible req req.toList ∧ cost w req.toList = ∑ r ∈ req, w r := by
  refine ⟨fun r hr => Finset.mem_toList.mpr hr, ?_⟩
  unfold cost
  rw [← List.sum_toFinset _ req.nodup_toList, Finset.toList_toFinset]

theorem minimal_is_ledger (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (req : Finset R) :
    IsLeast {c | ∃ L, admissible req L ∧ cost w L = c} (∑ r ∈ req, w r) := by
  refine ⟨⟨req.toList, (minimal_attained w req).1, (minimal_attained w req).2⟩, ?_⟩
  rintro c ⟨L, hL, rfl⟩
  exact admissible_cost_ge w hw req L hL

/-- An admissible schedule with a repeat or an unrequired entry costs strictly more. -/
theorem strict_if_extra (w : R → ℝ) (hw : ∀ r, 0 < w r) (req : Finset R) (L : List R)
    (hL : admissible req L) (hx : ¬ (L.Nodup ∧ L.toFinset = req)) :
    ∑ r ∈ req, w r < cost w L := by
  have hw0 : ∀ r, 0 ≤ w r := fun r => (hw r).le
  have hsub : req ⊆ L.toFinset := fun r hr => List.mem_toFinset.mpr (hL r hr)
  by_cases hnd : L.Nodup
  · have hne : L.toFinset ≠ req := fun h => hx ⟨hnd, h⟩
    have hss : req ⊂ L.toFinset := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne h.symm⟩
    obtain ⟨x, hxL, hxr⟩ := Finset.exists_of_ssubset hss
    have h1 : ∑ r ∈ req, w r < ∑ r ∈ L.toFinset, w r :=
      Finset.sum_lt_sum_of_subset hsub hxL hxr (hw x) (fun r _ _ => hw0 r)
    have h2 : ∑ r ∈ L.toFinset, w r = cost w L := by
      unfold cost; rw [List.sum_toFinset _ hnd]
    linarith
  · have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hw0 r)
    suffices ∑ r ∈ L.toFinset, w r < cost w L by linarith
    clear hL hx hsub h1
    induction L with
    | nil => exact absurd List.nodup_nil hnd
    | cons a L ih =>
      simp only [cost, List.map_cons, List.sum_cons, List.toFinset_cons] at ih ⊢
      by_cases ha : a ∈ L
      · rw [Finset.insert_eq_of_mem (List.mem_toFinset.mpr ha)]
        have hc := cost_ge_toFinset w hw0 L
        unfold cost at hc
        linarith [hw a]
      · rw [Finset.sum_insert (fun h => ha (List.mem_toFinset.mp h))]
        have : ¬ L.Nodup := fun h => hnd (List.nodup_cons.mpr ⟨ha, h⟩)
        linarith [ih this]

end PMAction.RefreshSchedule
