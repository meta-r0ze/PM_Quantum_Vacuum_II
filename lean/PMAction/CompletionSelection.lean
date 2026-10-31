import PMAction.IsometricDynamics
import PMAction.PersistenceSelection

/-!
# Persistence selects the identity completion on invisible modes

`LocalIsometricDynamics` completes a local readout update `U` on all labels by the identity on the
unobserved complement `P = 1 − E Eᴴ`. Any operator `W` placed on that complement,
`E U Eᴴ + P W P`, gives the same readout at every tick (`readout_same`), so readout alone does not
select the completion.

Persistence does. Price the completion's action on invisible modes at a positive rate per unit of
squared displacement, `toll · ‖P W P − P‖²` (the same positive change price that selects stationary
backgrounds, `PersistentBackground`). Under Paper I's survival law:

* `most_persistent_completion`: the completion that persists best is exactly one with `P W P = P`;
* `selected_is_identity`: every such completion equals `LocalIsometricDynamics`'s
  (`IsometricDynamics.extend`).

So the even (invisible) modes evolve by the identity, as a persistence consequence, not a
construction choice. Still inputs: the displacement price of invisible modes, `β > 0`, a positive
toll. This does not identify the directional-exponential completion with this one.
-/

noncomputable section
namespace PMAction.CompletionSelection
open Matrix

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The projector onto the invisible complement. -/
abbrev P (E : Matrix a b ℂ) : Matrix a a ℂ := IsometricDynamics.complement E

omit [Fintype a] [DecidableEq b] in
lemma P_eq (E : Matrix a b ℂ) : P E = 1 - E * Eᴴ := rfl

lemma P_idem (E : Matrix a b ℂ) (hE : Eᴴ * E = 1) : P E * P E = P E := by
  rw [P_eq, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul,
    show E * Eᴴ * (E * Eᴴ) = E * (Eᴴ * E) * Eᴴ by simp only [Matrix.mul_assoc], hE]
  rw [Matrix.mul_one]
  abel

/-- A completion with operator `W` on the invisible complement. -/
def extendW (E : Matrix a b ℂ) (U : Matrix b b ℂ) (W : Matrix a a ℂ) : Matrix a a ℂ :=
  E * U * Eᴴ + P E * W * P E

/-- **Every such completion has the same readout.** -/
theorem readout_same (E : Matrix a b ℂ) (hE : Eᴴ * E = 1) (U : Matrix b b ℂ) (W : Matrix a a ℂ) :
    Eᴴ * extendW E U W = U * Eᴴ := by
  have h0 : Eᴴ * P E = 0 := IsometricDynamics.complement_right E hE
  rw [extendW, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE, Matrix.one_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, add_zero]

/-- Price of the completion's action on invisible modes. -/
def invisibleCost (E : Matrix a b ℂ) (toll : ℝ) (W : Matrix a a ℂ) : ℝ :=
  toll * ∑ i, ∑ j, ‖(P E * W * P E - P E) i j‖ ^ 2

omit [DecidableEq b] in
lemma invisibleCost_nonneg (E : Matrix a b ℂ) (toll : ℝ) (ht : 0 < toll) (W : Matrix a a ℂ) :
    0 ≤ invisibleCost E toll W := by
  unfold invisibleCost; positivity

/-- **The most persistent completion fixes the invisible modes.** -/
theorem most_persistent_completion (E : Matrix a b ℂ) (hE : Eᴴ * E = 1) (toll β : ℝ)
    (ht : 0 < toll) (hβ : 0 < β) (W : Matrix a a ℂ) :
    (∀ W' : Matrix a a ℂ, Real.exp (-β * invisibleCost E toll W') ≤
        Real.exp (-β * invisibleCost E toll W)) ↔ P E * W * P E = P E := by
  rw [PersistenceSelection.most_persistent_iff_cheapest β hβ (invisibleCost E toll) W]
  constructor
  · intro h
    have h1 : invisibleCost E toll 1 = 0 := by
      simp [invisibleCost, P_idem E hE]
    have hle := h 1
    rw [h1] at hle
    have hz : invisibleCost E toll W = 0 := le_antisymm hle (invisibleCost_nonneg E toll ht W)
    unfold invisibleCost at hz
    have hs : ∑ i, ∑ j, ‖(P E * W * P E - P E) i j‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left ht.ne'
    have hent : ∀ i j, (P E * W * P E - P E) i j = 0 := by
      intro i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        fun j _ => sq_nonneg ‖(P E * W * P E - P E) i j‖)).mp hs i (Finset.mem_univ _)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        sq_nonneg ‖(P E * W * P E - P E) i j‖)).mp hi j (Finset.mem_univ _)
      simpa using hj
    exact sub_eq_zero.mp (Matrix.ext hent)
  · intro h W'
    have h0 : invisibleCost E toll W = 0 := by simp [invisibleCost, h]
    rw [h0]
    exact invisibleCost_nonneg E toll ht W'

omit [DecidableEq b] in
/-- **The selected completion is the identity completion.** -/
theorem selected_is_identity (E : Matrix a b ℂ) (U : Matrix b b ℂ) (W : Matrix a a ℂ)
    (h : P E * W * P E = P E) : extendW E U W = IsometricDynamics.extend E U := by
  rw [extendW, h, IsometricDynamics.extend]

end PMAction.CompletionSelection
