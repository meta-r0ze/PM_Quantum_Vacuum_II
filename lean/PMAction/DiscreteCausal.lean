import PMAction.PropagationBounds

/-!
# The causal structure the substrate update actually has

We do not postulate a Lorentzian manifold. The substrate's own update is a finite
matrix supported on the three-direction stencil `Reach e` (`SplitUpdate.update_supported`,
at most 27 sites per tick, `reachable_card_le`). This module builds the **causal
order** that stencil induces on spacetime `ℕ × X`, proves it is a genuine preorder
with finite light speed, and shows that a vanishing *local clock speed* is **not** a
horizon — because the causal reach is fixed by the axis permutations `e`, independent
of the load/clock readout.

* `ReachN` — reachability in `n` ticks (`ReachN 0` = equal, `ReachN (n+1)` = one more
  `Reach`).
* `Causal` — `(t,x) ≼ (t',y)` iff `t ≤ t'` and `y` is reachable from `x` in `t'−t` ticks.
* `causal_refl`, `causal_trans` — a preorder; `causal_one_tick` — one tick is exactly
  `Reach` (at most one stencil step per tick).
* `CausallyTrapped` — a set nothing causally escapes (substrate analogue of a trapped
  region, a graph property, not a null surface).
* `zero_clock_not_horizon` — a moving capacity point (`c_loc = 0`) is not trapped.

This is what E8's finite update supplies; the continuum metric and a Lorentzian
comparison are not assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
namespace PMAction.DiscreteCausal
open PMAction.SplitUpdate

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Reachability in `n` ticks. -/
def ReachN (e : Fin 3 → Equiv.Perm X) : ℕ → X → X → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, ReachN e n x z ∧ Reach e z y

theorem reachN_succ (e : Fin 3 → Equiv.Perm X) (n : ℕ) (x y : X) :
    ReachN e (n + 1) x y ↔ ∃ z, ReachN e n x z ∧ Reach e z y :=
  Iff.rfl

theorem reachN_one (e : Fin 3 → Equiv.Perm X) (x y : X) :
    ReachN e 1 x y ↔ Reach e x y := by
  simp [ReachN]

/-- `m + n` reachability factors through an intermediate site. -/
theorem reachN_add (e : Fin 3 → Equiv.Perm X) (m n : ℕ) :
    ∀ x z, ReachN e (m + n) x z ↔ ∃ y, ReachN e m x y ∧ ReachN e n y z := by
  induction n with
  | zero =>
    intro x z
    constructor
    · intro h; exact ⟨z, by simpa [ReachN] using h, by simp [ReachN]⟩
    · rintro ⟨y, h, rfl⟩; simpa [ReachN] using h
  | succ n ih =>
    intro x z
    have hnat : m + (n + 1) = (m + n) + 1 := by omega
    rw [hnat, reachN_succ]
    constructor
    · rintro ⟨w, hw, hstep⟩
      obtain ⟨y, hxy, hyw⟩ := (ih x w).mp hw
      exact ⟨y, hxy, ⟨w, hyw, hstep⟩⟩
    · rintro ⟨y, hxy, hyn⟩
      obtain ⟨w, hyw, hstep⟩ := hyn
      exact ⟨w, (ih x w).mpr ⟨y, hxy, hyw⟩, hstep⟩

/-- The causal preorder on spacetime. -/
def Causal (e : Fin 3 → Equiv.Perm X) (p q : ℕ × X) : Prop :=
  p.1 ≤ q.1 ∧ ReachN e (q.1 - p.1) p.2 q.2

theorem causal_refl (e : Fin 3 → Equiv.Perm X) (p : ℕ × X) : Causal e p p := by
  refine ⟨le_refl _, ?_⟩
  simp [ReachN]

theorem causal_trans (e : Fin 3 → Equiv.Perm X) {p q r : ℕ × X}
    (hpq : Causal e p q) (hqr : Causal e q r) : Causal e p r := by
  obtain ⟨h1, h2⟩ := hpq
  obtain ⟨h3, h4⟩ := hqr
  refine ⟨le_trans h1 h3, ?_⟩
  have hadd : (r.1 - p.1) = (q.1 - p.1) + (r.1 - q.1) := by omega
  rw [hadd]
  exact (reachN_add e (q.1 - p.1) (r.1 - q.1) p.2 r.2).mpr ⟨q.2, h2, h4⟩

/-- **Finite light speed.** One tick of causal advance is exactly one substrate
stencil step `Reach` (at most 27 sites). -/
theorem causal_one_tick (e : Fin 3 → Equiv.Perm X) (t : ℕ) (x y : X) :
    Causal e (t, x) (t + 1, y) ↔ Reach e x y := by
  unfold Causal
  constructor
  · rintro ⟨-, h⟩
    have hsub : (t + 1) - t = 1 := by omega
    rw [hsub] at h
    exact (reachN_one e x y).mp h
  · intro h
    refine ⟨Nat.le_succ t, ?_⟩
    have hsub : (t + 1) - t = 1 := by omega
    rw [hsub]
    exact (reachN_one e x y).mpr h

/-- A region nothing causally escapes (a graph property, not a null surface). -/
def CausallyTrapped (e : Fin 3 → Equiv.Perm X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ n y, ReachN e n x y → y ∈ S

/-- **A zero local clock speed is not a horizon.** If the point's first link actually
moves (`e 0 x ≠ x`), its singleton is not causally trapped — independent of the load,
because `Causal` carries no clock/load argument. -/
theorem zero_clock_not_horizon (e : Fin 3 → Equiv.Perm X) (x : X)
    (hmove : e 0 x ≠ x) : ¬ CausallyTrapped e {x} := by
  intro h
  have hnear : Near (e 0) x (e 0 x) := Or.inr (Or.inl rfl)
  have hreach : Reach e x (e 0 x) :=
    ⟨e 0 x, ⟨e 0 x, hnear, Or.inl rfl⟩, Or.inl rfl⟩
  have hrn : ReachN e 1 x (e 0 x) := ⟨x, rfl, hreach⟩
  have hmem : e 0 x ∈ ({x} : Set X) := h x (by simp) 1 (e 0 x) hrn
  simp at hmem
  exact hmove hmem

end PMAction.DiscreteCausal
