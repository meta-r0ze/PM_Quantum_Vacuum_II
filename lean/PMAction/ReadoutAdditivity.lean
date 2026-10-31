import PMAction.SummedReference
import PMAction.RecordTransport

/-!
# Why the reference read is summed

`SummedReference` and `ChainCouplings` use the summed read (every reference state read at each
refresh), and `ChainCouplings.mean_read_strong_factor` shows the mean read misses the strong ratio
by `3/2`. Here the summed read follows from two facts.

* `exact_refresh_needs_records`: by `RecordTransport.history_packet_bound`, a conservative linear
  refresh that exactly restores `r` independent reference states keeps at least `r` records. Each
  record is one read of one state. So a refresh reading one sampled state (one record) is not
  exact when `r ≥ 2` (`sampled_not_exact`).
* `additive_read`: a read cost that adds over disjoint sets of states, and charges each single
  state its event flag, is the sum of the flags over the states read. Read over all states, this
  is `SummedReference.sumFlag` (`full_read_is_sum`).
* `mean_not_additive`: the mean read is not additive. Two states with the same nonzero flag give
  the mean `f` together but `2f` separately.

So the summed read is the cost of an exact refresh under additive event pricing. That pricing is
Paper II's event law, `CommonResponse.responseCost`, linear in the flag. Still a premise: that a
refresh restores every reference state exactly each cycle.
-/

noncomputable section
namespace PMAction.ReadoutAdditivity
open Matrix CommonResponse ReferenceSampling SummedReference

/-- **Exact refresh of `r` states needs `r` records.** -/
theorem exact_refresh_needs_records {n : Type*} [Fintype n] [Nonempty n] (r R : ℕ)
    (P : ((Fin r → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ] ((Fin r → n → ℂ) × (Fin R → n → ℂ)))
    (hP : Function.Injective P) (hreset : ∀ inputs, (P (inputs, 0)).1 = 0) : r ≤ R :=
  RecordTransport.history_packet_bound r R P hP hreset

/-- **A one-record (sampled) read cannot refresh two or more states exactly.** -/
theorem sampled_not_exact {n : Type*} [Fintype n] [Nonempty n] (r : ℕ) (hr : 2 ≤ r)
    (P : ((Fin r → n → ℂ) × (Fin 1 → n → ℂ)) →ₗ[ℂ] ((Fin r → n → ℂ) × (Fin 1 → n → ℂ)))
    (hP : Function.Injective P) : ¬ ∀ inputs, (P (inputs, 0)).1 = 0 := by
  intro h
  have := exact_refresh_needs_records r 1 P hP h
  omega

/-- **Additive event pricing is the sum of single-state flags.** -/
theorem additive_read {ι : Type*} [DecidableEq ι] (C : Finset ι → ℝ) (f : ι → ℝ)
    (hempty : C ∅ = 0) (hsingle : ∀ i, C {i} = f i)
    (hadd : ∀ s t : Finset ι, Disjoint s t → C (s ∪ t) = C s + C t) (s : Finset ι) :
    C s = ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simpa using hempty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.insert_eq, hadd {a} s (Finset.disjoint_singleton_left.mpr ha),
      hsingle, ih]

/-- Reading every reference state with additive pricing gives `SummedReference.sumFlag`. -/
theorem full_read_is_sum {N r : ℕ} (E : Matrix (Fin N) (Fin r) ℂ) (Pm : Matrix (Fin N) (Fin N) ℂ)
    (C : Finset (Fin r) → ℝ) (hempty : C ∅ = 0)
    (hsingle : ∀ k, C {k} = stateFlag Pm (fun i => E i k))
    (hadd : ∀ s t : Finset (Fin r), Disjoint s t → C (s ∪ t) = C s + C t) :
    C Finset.univ = sumFlag E Pm := by
  rw [additive_read C _ hempty hsingle hadd, sumFlag]

/-- The mean read over a set of states. -/
def meanRead {ι : Type*} (f : ι → ℝ) (s : Finset ι) : ℝ := (∑ i ∈ s, f i) / s.card

/-- **The mean read is not additive.** -/
theorem mean_not_additive {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hf : f a = f b) (h0 : f a ≠ 0) :
    meanRead f ({a} ∪ {b}) ≠ meanRead f {a} + meanRead f {b} := by
  have hd : Disjoint ({a} : Finset ι) {b} := Finset.disjoint_singleton.mpr hab
  simp only [meanRead, Finset.sum_union hd, Finset.card_union_of_disjoint hd,
    Finset.sum_singleton, Finset.card_singleton, hf]
  intro h
  apply h0
  rw [hf]
  norm_num at h
  linarith

end PMAction.ReadoutAdditivity
