import PMAction.RefreshSchedule

/-!
# Reversible reference maintenance with a retained record

A job has a Boolean discrepancy relative to its reference and a Boolean record.
Its event swaps discrepancy and record. A clean record therefore permits exact
restoration without erasure. This is a finite reversible *task model*, not an
identification of a swap with one E8 event or of a bit with a carrier amplitude.

Every universally restoring schedule must visit every required job. Listing
each required job once is executable and achieves the minimum additive cost.
The record stores the old discrepancy; it is not a renewable clean resource.
The final no-reset theorem makes that boundary explicit.
-/

namespace PMAction.ReferenceMaintenance
open PMAction
variable {R : Type*} [DecidableEq R]

abbrev State (R : Type*) := R → Bool × Bool

def event (r : R) (s : State R) : State R :=
  fun j => if j = r then ((s j).2, (s j).1) else s j

theorem event_involutive (r : R) : Function.Involutive (event r) := by
  intro s
  funext j
  by_cases h : j = r <;> simp [event, h]

theorem event_commute (r q : R) (s : State R) :
    event r (event q s) = event q (event r s) := by
  funext j
  by_cases hr : j = r <;> by_cases hq : j = q <;> simp_all [event]

def run : List R → State R → State R
  | [], s => s
  | r :: L, s => event r (run L s)

theorem run_injective (L : List R) : Function.Injective (run L) := by
  induction L with
  | nil => exact Function.injective_id
  | cons r L ih => exact (event_involutive r).injective.comp ih

theorem untouched (L : List R) (s : State R) (r : R) (h : r ∉ L) :
    run L s r = s r := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.mem_cons, not_or] at h
    simpa [run, event, h.1] using ih h.2

theorem run_nodup (L : List R) (hL : L.Nodup) (s : State R) (r : R) :
    run L s r = if r ∈ L then ((s r).2, (s r).1) else s r := by
  induction L with
  | nil => simp [run]
  | cons a L ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hL
    by_cases h : r = a
    · subst r
      simp [run, event, ih hn, ha]
    · simp [run, event, h, ih hn]

def prepare (d : R → Bool) : State R := fun r => (d r, false)

/-- Restoration is required for every initial discrepancy, with a clean record. -/
def Restores (req : Finset R) (L : List R) : Prop :=
  ∀ d : R → Bool, ∀ r ∈ req, (run L (prepare d) r).1 = false

theorem restoring_visits {req : Finset R} {L : List R} (h : Restores req L) :
    RefreshSchedule.admissible req L := by
  intro r hr
  by_contra hn
  have hh := h (fun _ => true) r hr
  rw [untouched L _ r hn] at hh
  simp [prepare] at hh

theorem restores_iff_visits (req : Finset R) (L : List R) (hL : L.Nodup) :
    Restores req L ↔ RefreshSchedule.admissible req L := by
  refine ⟨restoring_visits, ?_⟩
  intro h d r hr
  simp [run_nodup L hL, h r hr, prepare]

/-- The minimal schedule restores the live bits and retains their old values. -/
theorem canonical_record (req : Finset R) (d : R → Bool) (r : R) (hr : r ∈ req) :
    run req.toList (prepare d) r = (false, d r) := by
  simp [run_nodup _ req.nodup_toList, Finset.mem_toList.mpr hr, prepare]

theorem canonical_restores (req : Finset R) : Restores req req.toList := by
  intro d r hr
  rw [canonical_record req d r hr]

/-- A stored reference bit is unchanged by execution. -/
abbrev Frame (R : Type*) := Bool × State R

def execute (L : List R) (s : Frame R) : Frame R := (s.1, run L s.2)

theorem reference_preserved (L : List R) (s : Frame R) : (execute L s).1 = s.1 := rfl

theorem execute_injective (L : List R) : Function.Injective (execute L) := by
  intro s t h
  have h1 := congrArg (fun x : Frame R => x.1) h
  have h2 := congrArg (fun x : Frame R => x.2) h
  exact Prod.ext h1 (run_injective L h2)

/-- The live value is specified relative to the stored reference. -/
def live (s : Frame R) (r : R) : Bool := if (s.2 r).1 then !s.1 else s.1

theorem live_restored (req : Finset R) (reference : Bool) (d : R → Bool)
    (r : R) (hr : r ∈ req) :
    live (execute req.toList (reference, prepare d)) r = reference := by
  simp [live, execute, canonical_record req d r hr]

/-- Reusing the same occupied records undoes the repair, rather than providing
free repeated maintenance. A fresh-record supply or a further task is necessary. -/
theorem canonical_twice (req : Finset R) (s : State R) :
    run req.toList (run req.toList s) = s := by
  funext r
  simp only [run_nodup _ req.nodup_toList]
  split <;> simp_all

/-- All restoring schedules, not just duplicate-free ones, obey the work bound. -/
theorem minimum_executable_cost (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (req : Finset R) :
    IsLeast {c | ∃ L, Restores req L ∧ RefreshSchedule.cost w L = c}
      (∑ r ∈ req, w r) := by
  refine ⟨⟨req.toList, canonical_restores req, (RefreshSchedule.minimal_attained w req).2⟩, ?_⟩
  rintro c ⟨L, hL, rfl⟩
  exact RefreshSchedule.admissible_cost_ge w hw req L (restoring_visits hL)

/-- The record cannot also be reset while preserving the erased distinction. -/
theorem no_record_free_reset (F : (Bool × Bool) → (Bool × Bool))
    (hinj : Function.Injective F)
    (hreset : ∀ b, F (b, false) = (false, false)) : False := by
  have h := hinj ((hreset true).trans (hreset false).symm)
  have := congrArg Prod.fst h
  cases this

omit [DecidableEq R] in
/-- A closed finite reversible state space cannot send every state to a fixed
live reference, even when arbitrary record states are allowed as inputs. -/
theorem no_closed_universal_reset [Finite R] (r : R) (F : State R → State R)
    (hinj : Function.Injective F) (hreset : ∀ s, (F s r).1 = false) : False := by
  have hsurj := (Finite.injective_iff_surjective).mp hinj
  obtain ⟨s, hs⟩ := hsurj (fun _ => (true, false))
  have hh := hreset s
  rw [hs] at hh
  cases hh

end PMAction.ReferenceMaintenance
