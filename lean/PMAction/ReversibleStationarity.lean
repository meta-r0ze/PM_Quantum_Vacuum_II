import PMAction.NativeReferenceBackground

/-!
# Reachability is distinct from selecting a stationary background

An injective update cannot reach one of its fixed points in finitely many
steps from a nonfixed state. A survival comparison among supplied states is
not a physical preparation procedure. This does not exclude local restoration
that exports disturbances, open preparation, or asymptotic limits.
-/

noncomputable section
namespace PMAction.ReversibleStationarity

theorem iterate_fixed_iff {a : Type*} (f : a → a) (hf : Function.Injective f)
    (s : a) (n : ℕ) : f (f^[n] s) = f^[n] s ↔ f s = s := by
  rw [← Function.iterate_succ_apply' f n s, Function.iterate_succ_apply f n s]
  exact (hf.iterate n).eq_iff

theorem fixed_unreachable {a : Type*} (f : a → a) (hf : Function.Injective f)
    (s : a) (hs : f s ≠ s) (n : ℕ) : f (f^[n] s) ≠ f^[n] s := by
  exact fun h => hs ((iterate_fixed_iff f hf s n).mp h)

open PMAction.NativeCarrierState PMAction.NativeReferenceBackground in
/-- The native occupied seed cannot be turned into a globally fixed reference
background merely by iterating this same closed reversible routing. -/
theorem native_seed_not_prepared {X : Type*} [Fintype X] [DecidableEq X]
    (o : X) (e : Equiv.Perm X) (n : ℕ) :
    let s := oneHot (o, ActualRootRepair.label (.inl 0))
    tick o e ((tick o e)^[n] s) ≠ (tick o e)^[n] s :=
  fixed_unreachable (tick o e) (tick o e).injective _ (single_carrier_not_fixed o e) n

end PMAction.ReversibleStationarity
