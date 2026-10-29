import PMAction.WalkReferenceProtocol

/-!
# Finite closed reference flow without per-tick clean-record assumptions

On a ring of N sites, prepare N forward reference packets and supply an
arbitrary initial live stream. The same closed, unitary transport/coupling
update restores the coupling site's live packet for the first N trials.
At trial N+1 its first old live packet returns. Every amplitude remains
inside the finite state; no record is refreshed between trials.

The incoming reference preparation and on-site pulse/phase admissibility
remain inputs. This is not an unlimited reservoir or a physical tick selector.
-/
noncomputable section
namespace PMAction.WalkReferenceCycle
open Matrix ConcreteFermion WalkReferenceCoupling
variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev State (X : Type*) := X → Doublet × Doublet

def advance (o : X) (e : Equiv.Perm X) (s : State X) : State X := fun x =>
  if x = o then ((s (e x)).2, (s (e⁻¹ x)).1)
  else ((s (e⁻¹ x)).1, (s (e x)).2)

def amplitude (s : State X) : X × Fin 4 → ℂ :=
  WalkReferenceProtocol.field (fun x => (s x).1) (fun x => (s x).2)

/-- The packet dynamics is exactly the actual spatial-spinor unitary. -/
theorem intertwining (o : X) (e : Equiv.Perm X) (s : State X) :
    WalkReferenceProtocol.update o e *ᵥ amplitude s = amplitude (advance o e s) := by
  ext p
  rcases p with ⟨x,a⟩
  rw [amplitude, WalkReferenceProtocol.update_action]
  by_cases hx : x = o <;> simp [amplitude, advance, WalkReferenceProtocol.field, hx]

theorem iterations (o : X) (e : Equiv.Perm X) (t : ℕ) (s : State X) :
    (fun ψ => WalkReferenceProtocol.update o e *ᵥ ψ)^[t] (amplitude s) =
      amplitude ((advance o e)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, intertwining, Function.iterate_succ_apply']

omit [Fintype X] in
/-- A record follows its predecessor until its path encounters the coupling site. -/
lemma record_path (o : X) (e : Equiv.Perm X) (t : ℕ) (s : State X) (x : X)
    (havoid : ∀ j < t, e^[j] x ≠ o) :
    (((advance o e)^[t] s) x).2 = (s (e^[t] x)).2 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hx : x ≠ o := by simpa using havoid 0 (by omega)
    have hs : ∀ j < t, e^[j] (e x) ≠ o := by
      intro j hj
      simpa only [Function.iterate_succ_apply] using havoid (j+1) (by omega)
    rw [Function.iterate_succ_apply']
    simp only [advance, hx, ite_false]
    rw [ih (e x) hs, Function.iterate_succ_apply]

omit [Fintype X] in
/-- Each sampled live output uses the next incoming record packet. -/
lemma arrival (o : X) (e : Equiv.Perm X) (t : ℕ) (s : State X) :
    (((advance o e)^[t+1] s) o).1 = (((advance o e)^[t] s) (e o)).2 := by
  rw [Function.iterate_succ_apply']
  simp [advance]

omit [Fintype X] in
/-- With no incoming discrepancy, the closed reference state needs no renewal. -/
theorem reference_fixed (o : X) (e : Equiv.Perm X) (reference : Doublet) :
    advance o e (fun _ => (reference, reference)) = fun _ => (reference, reference) := by
  funext x
  simp [advance]

end PMAction.WalkReferenceCycle

namespace PMAction.WalkReferenceCycle
open WalkReferenceCoupling

lemma rotate_zero (R j : ℕ) (hj : j < R+1) :
    (finRotate (R+1))^[j] 0 = (⟨j,hj⟩ : Fin (R+1)) := by
  have h := congrFun (finCycle_eq_finRotate_iterate (k := (⟨j,hj⟩ : Fin (R+1)))) 0
  simpa only [finCycle_apply, zero_add] using h.symm

lemma avoids_return (R : ℕ) :
    ∀ j < R, (finRotate (R+1))^[j] (finRotate (R+1) 0) ≠ (0 : Fin (R+1)) := by
  intro j hj
  rw [← Function.iterate_succ_apply, rotate_zero R (j+1) (by omega)]
  intro h
  have hh := congrArg Fin.val h
  simp at hh

/-- N initially prepared record packets suffice for N actual closed update trials. -/
theorem ring_restores (R t : ℕ) (ht0 : 0 < t) (ht : t ≤ R+1)
    (s : State (Fin (R+1))) (reference : Doublet) (hr : ∀ x, (s x).2 = reference) :
    (((advance 0 (finRotate (R+1)))^[t] s) 0).1 = reference := by
  cases t with
  | zero => omega
  | succ t =>
    rw [arrival]
    rw [record_path 0 (finRotate (R+1)) t s (finRotate (R+1) 0)]
    · exact hr _
    · intro j hj
      exact avoids_return R j (by omega)

/-- After exhausting the N reference packets, the first old live packet returns. -/
theorem first_return (R : ℕ) (s : State (Fin (R+1))) :
    (((advance 0 (finRotate (R+1)))^[R+2] s) 0).1 =
      (s ((finRotate (R+1))⁻¹ 0)).1 := by
  rw [arrival]
  rw [Function.iterate_succ_apply]
  rw [record_path 0 (finRotate (R+1)) R
    (advance 0 (finRotate (R+1)) s) (finRotate (R+1) 0) (avoids_return R)]
  have hclose : (finRotate (R+1))^[R] (finRotate (R+1) 0) = (0 : Fin (R+1)) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', rotate_zero R R (by omega)]
    exact finRotate_last
  rw [hclose]
  simp [advance]

/-- No silent renewal occurs when a non-reference live packet has been retained. -/
theorem finite_horizon (R : ℕ) (s : State (Fin (R+1))) (reference : Doublet)
    (h : (s ((finRotate (R+1))⁻¹ 0)).1 ≠ reference) :
    (((advance 0 (finRotate (R+1)))^[R+2] s) 0).1 ≠ reference := by
  rw [first_return]
  exact h

end PMAction.WalkReferenceCycle
