import PMAction.WalkReferenceCycle

/-!
# Open renewal has an explicit source and a retained outgoing record

The same two-stream update extends reversibly to the integer line. A prepared
reference at every positive incoming site restores the coupling output for
every finite time, with no wraparound. This requires an unbounded source:
for nonzero reference population the incoming population through N trials is
N times that population. An indefinitely replenished source is not derived
from finite-memory closed persistence, nor is this infinite background claimed
to be a normalized one-particle state.
-/
noncomputable section
namespace PMAction.OpenReferenceFlow
variable {X V : Type*} [DecidableEq X]

abbrev State (X V : Type*) := X → V × V

def streamShift (e : Equiv.Perm X) (s : State X V) : State X V :=
  fun x => ((s (e⁻¹ x)).1, (s (e x)).2)

def exchangeAt (o : X) (s : State X V) : State X V :=
  fun x => if x = o then ((s x).2, (s x).1) else s x

omit [DecidableEq X] in
lemma shift_inverse (e : Equiv.Perm X) (s : State X V) : streamShift e⁻¹ (streamShift e s) = s := by
  funext x
  simp [streamShift]

lemma exchange_involutive (o : X) : Function.Involutive (exchangeAt (V := V) o) := by
  intro s
  funext x
  by_cases h : x = o <;> simp [exchangeAt, h]

def shiftEquiv (e : Equiv.Perm X) : State X V ≃ State X V where
  toFun := streamShift e
  invFun := streamShift e⁻¹
  left_inv := shift_inverse e
  right_inv s := by simpa using shift_inverse e⁻¹ s

def evolution (o : X) (e : Equiv.Perm X) : State X V ≃ State X V :=
  (shiftEquiv e).trans (Function.Involutive.toPerm (exchangeAt o) (exchange_involutive o))

lemma evolution_apply (o : X) (e : Equiv.Perm X) (s : State X V) (x : X) :
    evolution o e s x = if x = o then ((s (e x)).2, (s (e⁻¹ x)).1)
      else ((s (e⁻¹ x)).1, (s (e x)).2) := rfl

/-- This is the same stencil as the finite spinor protocol, not a replacement rule. -/
lemma agrees_with_walk (o : X) (e : Equiv.Perm X)
    (s : State X WalkReferenceCoupling.Doublet) :
    evolution o e s = WalkReferenceCycle.advance o e s := rfl

lemma record_path (o : X) (e : Equiv.Perm X) (t : ℕ) (s : State X V) (x : X)
    (havoid : ∀ j < t, e^[j] x ≠ o) :
    (((evolution o e)^[t] s) x).2 = (s (e^[t] x)).2 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hx : x ≠ o := by simpa using havoid 0 (by omega)
    have hs : ∀ j < t, e^[j] (e x) ≠ o := by
      intro j hj
      simpa only [Function.iterate_succ_apply] using havoid (j+1) (by omega)
    rw [Function.iterate_succ_apply', evolution_apply]
    simp only [hx, ite_false]
    rw [ih (e x) hs, Function.iterate_succ_apply]

lemma arrival (o : X) (e : Equiv.Perm X) (t : ℕ) (s : State X V) :
    (((evolution o e)^[t+1] s) o).1 = (((evolution o e)^[t] s) (e o)).2 := by
  rw [Function.iterate_succ_apply', evolution_apply]
  simp

def line : Equiv.Perm ℤ where
  toFun x := x+1
  invFun x := x-1
  left_inv x := by dsimp; omega
  right_inv x := by dsimp; omega

lemma line_iterate (t : ℕ) (x : ℤ) : line^[t] x = x + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    change (x + (t : ℤ)) + 1 = x + ((t+1 : ℕ) : ℤ)
    omega

/-- Indefinite operation is possible under an explicit infinite incoming-source contract. -/
theorem open_restores (s : State ℤ V) (reference : V)
    (hsource : ∀ j : ℕ, (s ((j : ℤ)+1)).2 = reference) (t : ℕ) :
    (((evolution 0 line)^[t+1] s) 0).1 = reference := by
  rw [arrival]
  rw [record_path 0 line t s (line 0)]
  · rw [line_iterate]
    simpa [line, add_comm] using hsource t
  · intro j _
    rw [line_iterate]
    change (0+1) + (j : ℤ) ≠ 0
    omega

section Population
variable {n : Type*} [Fintype n]

def incomingPopulation (s : State ℤ (n → ℂ)) (N : ℕ) : ℝ :=
  ∑ j : Fin N, CommonResponse.nsq ((s ((j.val : ℤ)+1)).2)

/-- Incoming references carry population; they are not a free reset operation. -/
theorem source_population (s : State ℤ (n → ℂ)) (reference : n → ℂ)
    (hsource : ∀ j : ℕ, (s ((j : ℤ)+1)).2 = reference) (N : ℕ) :
    incomingPopulation s N = N * CommonResponse.nsq reference := by
  simp [incomingPopulation, hsource]

theorem source_unbounded (s : State ℤ (n → ℂ)) (reference : n → ℂ)
    (hsource : ∀ j : ℕ, (s ((j : ℤ)+1)).2 = reference)
    (hpop : 0 < CommonResponse.nsq reference) (C : ℝ) :
    ∃ N, C < incomingPopulation s N := by
  obtain ⟨N,hN⟩ := exists_nat_gt (C / CommonResponse.nsq reference)
  refine ⟨N, ?_⟩
  rw [source_population s reference hsource]
  exact (div_lt_iff₀ hpop).mp hN

end Population
end PMAction.OpenReferenceFlow
