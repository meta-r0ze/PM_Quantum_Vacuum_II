import PMAction.SplitUpdate
import Mathlib.Logic.Equiv.Fin.Rotate

noncomputable section
namespace PMAction.SplitUpdate
open Matrix ConcreteFermion

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [Fintype X] [DecidableEq X]

def choice (e : Equiv.Perm X) (c : Fin 3) (x : X) : X := ![x,e x,e.symm x] c

omit [Fintype X] [DecidableEq X] in
lemma near_iff_choice (e : Equiv.Perm X) (x y : X) :
    Near e x y ↔ ∃ c : Fin 3, y=choice e c x := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨c,rfl⟩
    fin_cases c <;> simp [choice, Near]

def endpoint (e : Fin 3 → Equiv.Perm X) (x : X) (c : Fin 3 → Fin 3) : X :=
  choice (e 2) (c 2) (choice (e 1) (c 1) (choice (e 0) (c 0) x))

omit [Fintype X] [DecidableEq X] in
lemma reach_iff_endpoint (e : Fin 3 → Equiv.Perm X) (x y : X) :
    Reach e x y ↔ ∃ c : Fin 3 → Fin 3, y=endpoint e x c := by
  constructor
  · rintro ⟨v,⟨u,hu,hv⟩,hy⟩
    obtain ⟨a,ha⟩ := (near_iff_choice (e 0) x u).mp hu
    obtain ⟨b,hb⟩ := (near_iff_choice (e 1) u v).mp hv
    obtain ⟨c,hc⟩ := (near_iff_choice (e 2) v y).mp hy
    exact ⟨![a,b,c], by simpa [endpoint, ha, hb] using hc⟩
  · rintro ⟨c,rfl⟩
    exact ⟨_, ⟨_, (near_iff_choice _ _ _).mpr ⟨c 0,rfl⟩,
      (near_iff_choice _ _ _).mpr ⟨c 1,rfl⟩⟩, (near_iff_choice _ _ _).mpr ⟨c 2,rfl⟩⟩

/-- A lattice-size-independent bound, allowing coincident/wrapped neighbors. -/
theorem reachable_card_le (e : Fin 3 → Equiv.Perm X) (x : X) :
    (Finset.univ.filter (Reach e x)).card ≤ 27 := by
  have hi : Finset.univ.filter (Reach e x) = Finset.univ.image (endpoint e x) := by
    ext y
    simp [reach_iff_endpoint, eq_comm]
  rw [hi]
  calc
    _ ≤ (Finset.univ : Finset (Fin 3 → Fin 3)).card := Finset.card_image_le
    _ = 27 := by norm_num

/-- Three literal coordinate shifts on a finite periodic cubic lattice. -/
def axisShift (N : ℕ) (j : Fin 3) : Equiv.Perm (Fin 3 → Fin N) :=
  Equiv.piCongrRight (fun i => if i=j then finRotate N else Equiv.refl (Fin N))

lemma axisShift_own (N : ℕ) (j : Fin 3) (x : Fin 3 → Fin N) :
    axisShift N j x j = finRotate N (x j) := by simp [axisShift]

lemma axisShift_other (N : ℕ) (j i : Fin 3) (x : Fin 3 → Fin N) (h : i ≠ j) :
    axisShift N j x i = x i := by simp [axisShift, h]

/-- A concrete cubic-lattice update with eight internal components. -/
def cubicUpdate (N : ℕ) (Q : Matrix Sites Sites ℂ) (τ : ℝ) := update (axisShift N) Q τ

theorem cubicUpdate_unitary (N : ℕ) (Q : Matrix Sites Sites ℂ) (τ : ℝ)
    (hq : Q ∈ unitary (Matrix Sites Sites ℂ)) :
    cubicUpdate N Q τ ∈ unitary (Matrix ((Fin 3 → Fin N) × Sites) ((Fin 3 → Fin N) × Sites) ℂ) :=
  update_unitary _ _ _ hq

end PMAction.SplitUpdate
