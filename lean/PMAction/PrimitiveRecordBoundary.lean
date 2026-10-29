import PMAction.WalkReferenceCoupling
import PMAction.BranchGateBoundary
import PMAction.CarrierEvents

/-!
# Why the preparation still needs a primitive implementation and price

In a fixed carrier/register basis, finite words of permutations and diagonal
phases cannot prepare the required two-support coherent state from a basis
seed. The concrete beta preparation is outside that library. Thus pricing
it as one existing permutation/root event is not justified by the current
basis-label model. This does not exclude another coherent encoding, initially
coherent resources or a richer E8-derived operator model; those resources
and their preparation still need an implementation and tariff.
-/
noncomputable section
namespace PMAction.PrimitiveRecordBoundary
open Matrix BranchGateBoundary
variable {n : Type*} [Fintype n] [DecidableEq n]

def quarterState (a b : n) : n → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (Pi.single a 1 + Complex.I • Pi.single b 1)

lemma scale_ne_zero : ((1 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  positivity

/-- Any basis-preserving gate has at most one nonzero entry in an input column. -/
theorem cannot_prepare (A : Matrix n n ℂ) (hA : BasisPreserving A)
    (input a b : n) (hab : a ≠ b) : A *ᵥ Pi.single input 1 ≠ quarterState a b := by
  intro h
  obtain ⟨k,z,hk⟩ := hA input
  have haVal : A a input = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, quarterState, Pi.single_apply,
      hab, Ne.symm hab] using congrFun h a
  have hbVal : A b input = ((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, quarterState, Pi.single_apply,
      hab, Ne.symm hab] using congrFun h b
  have ha : a = k := by
    by_contra he
    have hz : A a input = 0 := by simpa [he] using hk a
    exact scale_ne_zero (haVal.symm.trans hz)
  have hb : b = k := by
    by_contra he
    have hz : A b input = 0 := by simpa [he] using hk b
    exact (mul_ne_zero scale_ne_zero Complex.I_ne_zero) (hbVal.symm.trans hz)
  exact hab (ha.trans hb.symm)

/-- This larger library contains every carrier permutation and every diagonal
phase assignment; the obstruction does not depend on a special clock phase. -/
inductive Gate (n : Type*) where
  | permutation (e : Equiv.Perm n)
  | phase (d : n → ℂ)

def action : Gate n → Matrix n n ℂ
  | .permutation e => e.permMatrix ℂ
  | .phase d => diagonal d

omit [Fintype n] in
lemma action_preserves (g : Gate n) : BasisPreserving (action g) := by
  cases g with
  | permutation e => exact permutation_preserves e
  | phase d => exact diagonal_preserves d

theorem word_cannot_prepare (gates : List (Gate n)) (input a b : n) (hab : a ≠ b) :
    (gates.map action).prod *ᵥ Pi.single input 1 ≠ quarterState a b := by
  apply cannot_prepare _ _ input a b hab
  apply word_preserves
  intro A hA
  obtain ⟨g,_,rfl⟩ := List.mem_map.mp hA
  exact action_preserves g

/-- This specializes to actual Paper I carriers, rather than only four arbitrary labels. -/
theorem actual_carrier_boundary (c : Fin 3) (gates : List (Gate (CarrierEvents.Carrier c)))
    (input a b : CarrierEvents.Carrier c) (hab : a ≠ b) :
    (gates.map action).prod *ᵥ Pi.single input 1 ≠ quarterState a b :=
  word_cannot_prepare gates input a b hab

lemma beta_target : WalkReferenceCoupling.preparation *ᵥ WalkReferenceCoupling.seed =
    quarterState (0 : Fin 4) 2 := by
  rw [WalkReferenceCoupling.prepares_forward]
  ext a
  fin_cases a <;>
    simp [quarterState, WalkReferenceCoupling.pack, WalkReferenceCoupling.raw,
      WalkReferenceCoupling.backward, WalkRecordTransport.encode, WalkReferenceCoupling.reference]

/-- There is no finite price for this preparation *within this gate library*,
because there is no implementing word; a richer physical implementation is needed. -/
theorem no_primitive_preparation (gates : List (Gate (Fin 4))) :
    (gates.map action).prod ≠ WalkReferenceCoupling.preparation := by
  intro h
  apply word_cannot_prepare gates 0 0 2 (by decide)
  rw [h]
  have hs : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℂ) = WalkReferenceCoupling.seed := by
    ext a
    fin_cases a <;> simp [WalkReferenceCoupling.seed]
  rw [hs]
  exact beta_target

end PMAction.PrimitiveRecordBoundary
