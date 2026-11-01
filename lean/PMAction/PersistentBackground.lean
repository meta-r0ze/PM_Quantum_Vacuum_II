import PMAction.NativeReferenceBackground
import PMAction.PersistenceSelection

/-!
# The initial background from persistence

`REVIEW-AND-NEXT` item 3 asks for the initial background of the reference protocol. Under
Paper I's survival law (`PersistenceSelection`), the most persistent configuration is the one of
least excess price. Economy selects exactly the stationary fields
(`NativeReferenceBackground.minimum_iff_fixed`). On a connected protocol those are exactly the
uniform backgrounds, in which every live and record cell holds the same reference value
(`stationary_iff`).

* `persistent_background`: the configuration that persists best is exactly a uniform background.
  This identifies the unrestricted excess-price minimizers. The clean initial supply in
  `RecordSupply.clean_supply` and `lattice_forever` still needs an accessible preparation or
  initial-state contract; minimization is not the dynamics preparing it.

Inputs include the positive excess-change price, β > 0, the admissible configuration family
and an accessible stationary witness. The original unrestricted theorem compares all
configurations; it does not prepare a stationary background from an arbitrary conserved
sector. `persistent_in_family` retains the family and the common clock baseline explicitly.
The reference value is not selected here.
-/

noncomputable section
namespace PMAction.PersistentBackground
open NativeReferenceBackground NativeCarrierState

variable {X : Type*} [Fintype X] [DecidableEq X] {A : Type*} [DecidableEq A]

/-- **The most persistent background is uniform.** -/
theorem persistent_background (o : X) (e : Equiv.Perm X) (hc : Connected o e) (toll β : ℝ)
    (ht : 0 < toll) (hβ : 0 < β) (a : A) (s : Config X A) :
    (∀ t : Config X A, Real.exp (-β * price o e toll t) ≤ Real.exp (-β * price o e toll s)) ↔
      ∃ r : Fin 2 → A, ∀ x i,
        s (x, ActualRootRepair.label (.inl i)) = r i ∧
        s (x, ActualRootRepair.label (.inr i)) = r i := by
  rw [PersistenceSelection.most_persistent_iff_cheapest β hβ (price o e toll) s,
    minimum_iff_fixed o e toll ht a s, stationary_iff o e hc s]

/-- The physically usable family-restricted version. An admissible stationary
witness is required, rather than borrowing one from another conserved sector. -/
theorem persistent_in_family (o : X) (e : Equiv.Perm X) (hc : Connected o e)
    (toll β baseline : ℝ) (ht : 0 < toll) (hβ : 0 < β)
    (F : Set (Config X A)) (w : Config X A) (hw : w ∈ F)
    (hfixed : tick o e w = w) (s : Config X A) :
    (s ∈ F ∧ ∀ t ∈ F, Real.exp (-β * (baseline + price o e toll t)) ≤
      Real.exp (-β * (baseline + price o e toll s))) ↔
      s ∈ F ∧ ∃ r : Fin 2 → A, ∀ x i,
        s (x, ActualRootRepair.label (.inl i)) = r i ∧
        s (x, ActualRootRepair.label (.inr i)) = r i := by
  have h := PersistenceSelection.within_family_iff_cheapest β hβ (price o e toll) F baseline s
  have hm := minimum_in_family_iff o e toll baseline ht F w hw hfixed s
  have he : (s ∈ F ∧ ∀ t ∈ F, price o e toll s ≤ price o e toll t) ↔
      s ∈ F ∧ ∀ t ∈ F, baseline + price o e toll s ≤ baseline + price o e toll t := by
    simp only [add_le_add_iff_left]
  rw [h, he, hm, stationary_iff o e hc s]

end PMAction.PersistentBackground
