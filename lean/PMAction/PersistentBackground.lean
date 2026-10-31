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
  So the clean record supply that `RecordSupply.clean_supply` and `lattice_forever` take as an
  initial condition is the persistence-selected background, not a separate premise.

Still inputs: `β > 0` and a positive toll. Which reference value `r` the background holds is not
selected here.
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

end PMAction.PersistentBackground
