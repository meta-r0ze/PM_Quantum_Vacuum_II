import PMAction.SubstrateReflection
import PMAction.CarrierResponse
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# A closed reference cycle on actual carriers and a supplied 43-phase clock

Reference information is encoded in the correlation between a carrier and the
existing phase label. A root excursion is undone before the clock closes; no
fresh clean record is required on each cycle. A mask specifies the excursion.
All masks give reversible closed cycles, so persistence alone selects no mask.

The reflection is the existing E8-induced carrier event. Its phase-controlled
implementation, the clock register and its advance are model inputs; no coherent
mixer or primitive clock price is derived here.
-/
noncomputable section
namespace PMAction.CarrierReferenceCycle
open Matrix Finset CarrierEvents

abbrev State (c : Fin 3) := Carrier c × Fin 43

def rebase (c : Fin 3) (mask : Fin 43 → Bool) : Equiv.Perm (State c) where
  toFun s := (if mask s.2 then reflect c s.1 else s.1, s.2)
  invFun s := (if mask s.2 then reflect c s.1 else s.1, s.2)
  left_inv s := by cases hm : mask s.2 <;> simp [hm, reflection_involutive c s.1]
  right_inv s := by cases hm : mask s.2 <;> simp [hm, reflection_involutive c s.1]

@[simp] theorem rebase_twice (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) :
    rebase c mask (rebase c mask s) = s := (rebase c mask).left_inv s

def clock (c : Fin 3) : Equiv.Perm (State c) :=
  Equiv.prodCongr (Equiv.refl _) (finRotate 43)

def tick (c : Fin 3) (mask : Fin 43 → Bool) : Equiv.Perm (State c) :=
  (rebase c mask).trans ((clock c).trans (rebase c mask))

def reference (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) : Carrier c :=
  (rebase c mask s).1

theorem reference_encoded (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    reference c mask (rebase c mask (r,t)) = r :=
  congrArg Prod.fst (rebase_twice c mask (r,t))

theorem state_card (c : Fin 3) : Fintype.card (State c) = 344 := by
  simp [State, Fintype.card_prod, carrier_card]

theorem encoded_step (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    tick c mask (rebase c mask (r,t)) = rebase c mask (r,finRotate 43 t) := by
  change rebase c mask (clock c (rebase c mask (rebase c mask (r,t)))) = _
  rw [rebase_twice]
  rfl

theorem reference_preserved (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) :
    reference c mask (tick c mask s) = reference c mask s := by
  change (rebase c mask (rebase c mask (clock c (rebase c mask s)))).1 = _
  rw [rebase_twice]
  rfl

theorem phase_advances (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) :
    (tick c mask s).2 = finRotate 43 s.2 := rfl

/-- Executable gate form: advance the clock and perform at most one carrier
root event, exactly at a mask boundary. The two rebases defining the conjugacy
are algebraic coordinates, not two gates charged on every tick. -/
theorem tick_gate_form (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) :
    tick c mask s =
      (if mask (finRotate 43 s.2) ≠ mask s.2 then reflect c s.1 else s.1,
        finRotate 43 s.2) := by
  change (if mask (finRotate 43 s.2) then reflect c
      (if mask s.2 then reflect c s.1 else s.1) else
      (if mask s.2 then reflect c s.1 else s.1), finRotate 43 s.2) = _
  cases h0 : mask s.2 <;> cases h1 : mask (finRotate 43 s.2) <;>
    simp_all [reflection_involutive c s.1]

theorem iterate_encoded (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c)
    (t : Fin 43) (n : ℕ) :
    (tick c mask)^[n] (rebase c mask (r,t)) = rebase c mask (r,(finRotate 43)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, encoded_step, Function.iterate_succ_apply']

theorem clock_closes : ∀ t : Fin 43, (finRotate 43)^[43] t = t := by decide +kernel

theorem clock_visits : ∀ t : Fin 43, (finRotate 43)^[t.val] 0 = t := by decide +kernel

theorem trajectory_visits (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    (tick c mask)^[t.val] (rebase c mask (r,0)) = rebase c mask (r,t) := by
  rw [iterate_encoded, clock_visits]

/-- Closure holds on every state, not just a subset supplied with clean ancillas. -/
theorem cycle_closes (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) :
    (tick c mask)^[43] s = s := by
  obtain ⟨u, hu⟩ := (rebase c mask).surjective s
  rw [← hu, iterate_encoded, clock_closes]

theorem cycles_repeat (c : Fin 3) (mask : Fin 43 → Bool) (s : State c) (n : ℕ) :
    (tick c mask)^[43*n] s = s := by
  have hc : (tick c mask)^[43] = id := funext (cycle_closes c mask)
  rw [Function.iterate_mul, hc]
  simp

theorem tick_unitary (c : Fin 3) (mask : Fin 43 → Bool) :
    (tick c mask).permMatrix ℂ ∈ unitary (Matrix (State c) (State c) ℂ) :=
  CarrierResponse.perm_unitary _

/-- On encoded states, the carrier changes precisely at a mask boundary and
on an active root carrier. Clock motion is a different event. -/
theorem carrier_changed_iff (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    (tick c mask (rebase c mask (r,t))).1 ≠ (rebase c mask (r,t)).1 ↔
      mask (finRotate 43 t) ≠ mask t ∧ r ∈ active c := by
  rw [encoded_step]
  change (if mask (finRotate 43 t) then reflect c r else r) ≠
    (if mask t then reflect c r else r) ↔ _
  cases h0 : mask t <;> cases h1 : mask (finRotate 43 t) <;>
    simp_all [active, ne_comm]

/-- One explicit excursion: the carrier is reflected only during phase 1. -/
def excursionMask (t : Fin 43) : Bool := decide (t = 1)

theorem excursion_start (c : Fin 3) (r : Carrier c) :
    rebase c excursionMask (r,0) = (r,0) := by
  simp [rebase, excursionMask]

def boundaries (mask : Fin 43 → Bool) : Finset (Fin 43) :=
  univ.filter fun t => mask (finRotate 43 t) ≠ mask t

theorem excursion_boundaries : boundaries excursionMask = {0,1} := by decide +kernel

/-- A nonempty change set on a closed binary cycle cannot have just one edge:
the signed changes sum to zero. This does not require selecting an excursion mask. -/
theorem boundary_minimum (mask : Fin 43 → Bool) (hne : (boundaries mask).Nonempty) :
    2 ≤ (boundaries mask).card := by
  have hs : (∑ t : Fin 43, ((if mask (finRotate 43 t) then (1 : ℤ) else 0) -
      (if mask t then 1 else 0))) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate 43)
      (fun t : Fin 43 => if mask t then (1 : ℤ) else 0))
  have hnot : (boundaries mask).card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have had : mask (finRotate 43 a) ≠ mask a := by
      have hm : a ∈ boundaries mask := by rw [ha]; simp
      simpa [boundaries] using hm
    have hz : (∑ t : Fin 43, ((if mask (finRotate 43 t) then (1 : ℤ) else 0) -
        (if mask t then 1 else 0))) =
        (if mask (finRotate 43 a) then 1 else 0) - (if mask a then 1 else 0) := by
      apply Finset.sum_eq_single a
      · intro t _ hta
        have hn : t ∉ boundaries mask := by rw [ha]; simpa using hta
        have he : mask (finRotate 43 t) = mask t := by
          by_contra hbad
          exact hn (Finset.mem_filter.mpr ⟨mem_univ t, hbad⟩)
        rw [he, sub_self]
      · simp
    rw [hz] at hs
    cases h0 : mask a <;> cases h1 : mask (finRotate 43 a) <;> simp_all
  have hp := hne.card_pos
  omega

/-- The two carrier events are the actual outgoing and returning root actions. -/
def carrierEvents (c : Fin 3) (mask : Fin 43 → Bool) (t : Fin 43) : Finset (Carrier c) :=
  if t ∈ boundaries mask then active c else ∅

theorem event_member_iff (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    r ∈ carrierEvents c mask t ↔ t ∈ boundaries mask ∧ r ∈ active c := by
  by_cases ht : t ∈ boundaries mask <;> simp [carrierEvents, ht]

/-- A fixed reference does not sample the ensemble: it experiences either all
boundary events or none. -/
theorem pointwise_excursion_count (c : Fin 3) (r : Carrier c) :
    (∑ t : Fin 43, if r ∈ carrierEvents c excursionMask t then (1 : ℕ) else 0) =
      if r ∈ active c then 2 else 0 := by
  simp_rw [event_member_iff]
  by_cases hr : r ∈ active c
  · simp only [hr, and_true]
    rw [← Finset.sum_filter]
    have hs : univ.filter (fun t => t ∈ boundaries excursionMask) = {0,1} := by
      ext t
      simp [excursion_boundaries]
    rw [hs]
    norm_num
  · simp [hr]

theorem event_matches_update (c : Fin 3) (mask : Fin 43 → Bool) (r : Carrier c) (t : Fin 43) :
    r ∈ carrierEvents c mask t ↔
      (tick c mask (rebase c mask (r,t))).1 ≠ (rebase c mask (r,t)).1 := by
  rw [carrier_changed_iff]
  by_cases hb : t ∈ boundaries mask <;> simp_all [carrierEvents, boundaries]

/-- Uniform sampling is an explicit ensemble input. No independence of the
outgoing and returning events is needed; they have the same reference label. -/
theorem carrier_cost_for_mask (c : Fin 3) (mask : Fin 43 → Bool) (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (carrierEvents c mask) =
      toll * ((boundaries mask).card / 2) := by
  rw [PMArch.NetCost.expected_count_linear]
  have hp (t : Fin 43) : PMArch.NetCost.prob (carrierEvents c mask t) =
      if t ∈ boundaries mask then (1/2 : ℝ) else 0 := by
    by_cases ht : t ∈ boundaries mask <;>
      norm_num [carrierEvents, ht, PMArch.NetCost.prob, active_card, carrier_card]
  simp_rw [hp]
  rw [← Finset.sum_filter]
  have hs : univ.filter (fun t => t ∈ boundaries mask) = boundaries mask := by
    ext t
    simp
  rw [hs, Finset.sum_const]
  simp only [nsmul_eq_mul]
  ring

theorem carrier_cycle_cost (c : Fin 3) (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (carrierEvents c excursionMask) = toll := by
  rw [carrier_cost_for_mask, excursion_boundaries]
  norm_num

theorem idle_cycle_cost (c : Fin 3) (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (carrierEvents c (fun _ => false)) = 0 := by
  rw [carrier_cost_for_mask]
  have hb : boundaries (fun _ => false) = ∅ := by simp [boundaries]
  rw [hb]
  simp

/-- Economy within the stated family of non-idle root excursions. Requiring
an excursion is an operational input; idle cycles also persist at zero root cost. -/
theorem minimum_nonidle_carrier_cost (c : Fin 3) (toll : ℝ) (ht : 0 ≤ toll) :
    IsLeast {cost | ∃ mask : Fin 43 → Bool, (boundaries mask).Nonempty ∧
      PMArch.NetCost.expectedCost toll (carrierEvents c mask) = cost} toll := by
  constructor
  · refine ⟨excursionMask, ?_, carrier_cycle_cost c toll⟩
    rw [excursion_boundaries]
    simp
  · rintro cost ⟨mask, hmask, rfl⟩
    rw [carrier_cost_for_mask]
    have hb : (2 : ℝ) ≤ (boundaries mask).card := by exact_mod_cast boundary_minimum mask hmask
    have hf : (1 : ℝ) ≤ (boundaries mask).card / 2 := by linarith
    simpa using mul_le_mul_of_nonneg_left hf ht

theorem minimum_cost_iff_two_boundaries (c : Fin 3) (mask : Fin 43 → Bool)
    (toll : ℝ) (ht : 0 < toll) :
    PMArch.NetCost.expectedCost toll (carrierEvents c mask) = toll ↔
      (boundaries mask).card = 2 := by
  rw [carrier_cost_for_mask]
  constructor
  · intro h
    have hh : toll * ((boundaries mask).card / 2 : ℝ) = toll * 1 := by simpa using h
    have hf := mul_left_cancel₀ (ne_of_gt ht) hh
    have hc : ((boundaries mask).card : ℝ) = 2 := by linarith
    exact_mod_cast hc
  · intro h
    norm_num [h]

/-- A supplied root disturbance cannot be repaired by doing nothing on all
carriers: the actual reflection has a nonempty active set. -/
theorem reflection_nontrivial (c : Fin 3) : ¬ ∀ r : Carrier c, reflect c r = r := by
  intro h
  have he : active c = ∅ := by ext r; simp [active, h r]
  have hc := active_card c
  rw [he] at hc
  norm_num at hc

/-- Among positive-length words using this single root generator, two events
are necessary and sufficient to close on every carrier. This is not a minimum
for an arbitrary interference-controller or an unspecified gate library. -/
theorem minimum_closed_root_word (c : Fin 3) :
    IsLeast {n : ℕ | 0 < n ∧ ∀ r : Carrier c, (reflect c)^[n] r = r} 2 := by
  constructor
  · refine ⟨by decide, ?_⟩
    intro r
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      reflection_involutive c r
  · intro n hn
    by_contra h
    have hn1 : n = 1 := by have hp := hn.1; omega
    subst n
    exact reflection_nontrivial c (by simpa only [Function.iterate_one] using hn.2)

/-- Clock advance is not free in this ledger. Its price is supplied separately;
every phase advances, even when the carrier itself is stationary. -/
theorem clock_cycle_cost (c : Fin 3) (clockToll : ℝ) :
    PMArch.NetCost.expectedCost clockToll (fun _ : Fin 43 => (univ : Finset (Carrier c))) =
      43 * clockToll := by
  rw [PMArch.NetCost.expected_count_linear]
  have hn : Fintype.card (Carrier c) ≠ 0 := by rw [carrier_card]; decide
  simp [PMArch.NetCost.prob, hn]
  ring

end PMAction.CarrierReferenceCycle
