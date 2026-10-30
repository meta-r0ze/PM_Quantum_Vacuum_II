import PMAction.NativeReferenceBackground

/-!
# The native vacuum reference walk has the parity exchange

This checks parity of the explicitly constructed reference subtask
(`NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`),
not a selection of physical parity for the complete vacuum, flavour links or a mass phase.
The reference update is
a carrier-label permutation in which the live stream moves one way along the neighbour permutation
`e`, the record stream the other way, and the root at the coupling site `o` exchanges them.

* `walk_parity`: swapping the two streams and reversing the neighbour permutation (`e ↦ e⁻¹`)
  intertwines the update: `advance o e⁻¹ ∘ swap = swap ∘ advance o e`. This is the native walk's form
  of `WallExchange`'s `P` (exchange plus parity, `k ↦ −k`).
* `exchange_involution`: the exchange squares to the identity.
* `stationary_exchanged`: an exchanged stationary configuration is stationary for the reversed walk.
* `background_fixed`: the stationary backgrounds (one common reference on both streams,
  `NativeReferenceBackground.streams_fixed_iff`) are fixed by the swap.
* `backgrounds_agree`: on a connected orbit, the stationary backgrounds of the walk and of its
  exchanged, reversed form coincide.
-/

noncomputable section
namespace PMAction.ReferenceWalkParity
open PMAction NativeReferenceBackground

variable {X : Type*} [Fintype X] [DecidableEq X] {A : Type*}

/-- Exchange the two streams. -/
def swapS (s : X → A × A) : X → A × A := fun x => ((s x).2, (s x).1)

omit [Fintype X] in
/-- **The walk commutes with the stream exchange plus spatial reversal.** -/
theorem walk_parity (o : X) (e : Equiv.Perm X) (s : X → A × A) :
    advance o e⁻¹ (swapS s) = swapS (advance o e s) := by
  funext x
  by_cases hx : x = o <;> simp [advance, swapS, hx]

omit [Fintype X] [DecidableEq X] in
theorem exchange_involution (s : X → A × A) : swapS (swapS s) = s := by
  funext x; simp [swapS]

omit [Fintype X] in
theorem stationary_exchanged (o : X) (e : Equiv.Perm X) (s : X → A × A)
    (hs : advance o e s = s) : advance o e⁻¹ (swapS s) = swapS s := by
  rw [walk_parity, hs]

omit [Fintype X] [DecidableEq X] in
theorem background_fixed (r : A) : swapS (fun _ : X => (r, r)) = fun _ => (r, r) := by
  funext x; simp [swapS]

/-- On a connected orbit the stationary backgrounds of the walk and of its exchanged, reversed form
coincide: both are the common-reference configurations. -/
theorem backgrounds_agree (o : X) (e : Equiv.Perm X) (hc : Connected o e) (hc' : Connected o e⁻¹)
    (s : X → A × A) : advance o e s = s ↔ advance o e⁻¹ (swapS s) = swapS s := by
  rw [streams_fixed_iff o e hc, streams_fixed_iff o e⁻¹ hc']
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, background_fixed r⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [← exchange_involution s, hr, background_fixed]

end PMAction.ReferenceWalkParity
