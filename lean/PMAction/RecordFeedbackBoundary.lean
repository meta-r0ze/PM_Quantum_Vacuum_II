import PMAction.FiniteRestorationBridge
import PMArch.Lattices

/-!
# A retained record does not automatically give an autonomous live residual

The norm-preserving E8 isometry below restricts on the A2 plane of simple
coordinates 0 and 2 to `(x,y) ↦ (x-y,x)`. Reading x as live displacement and
y as record, a clean record gives a two-tick live reset with the old value
retained. Yet the one-tick live map on clean inputs is the identity, and on
occupied records it depends on y. Its clean-input residual is therefore not
the autonomous residual required by `FiniteRestorationBridge`.

The orbit closes after six ticks. This example refutes inferring a per-tick
nilpotent live map from a one-time record-assisted reset. It does not satisfy
convergence to a permanently restored live state and does not refute the
finite convergence theorem. Nor does it price or select this update as the
physical vacuum dynamics.
-/
noncomputable section
namespace PMAction.RecordFeedbackBoundary
open Matrix PMArch.Lattices

abbrev State := Fin 8 → ℤ

/-- An integral isometry: minus the composition of simple-root reflections 0 and 2. -/
def e8Update (z : State) : State :=
  ![z 0 - z 2, -z 1, z 0 - z 3, -z 3, -z 4, -z 5, -z 6, -z 7]

theorem e8_norm_preserved (z : State) :
    pairing (e8Update z) (e8Update z) = pairing z z := by
  simp [e8Update, pairing, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- A closed, reversible six-tick update, with no fresh records. -/
theorem e8_cycle (z : State) : e8Update^[6] z = z := by
  ext i
  fin_cases i <;> simp [Function.iterate_succ_apply', e8Update]
  ring

theorem e8_injective : Function.Injective e8Update := by
  intro z w h
  have hh : e8Update^[6] z = e8Update^[6] w := by
    change e8Update^[5] (e8Update z) = e8Update^[5] (e8Update w)
    rw [h]
  simpa only [e8_cycle] using hh

def plane (x y : ℤ) : State := ![x,0,y,0,0,0,0,0]

theorem plane_action (x y : ℤ) : e8Update (plane x y) = plane (x-y) x := by
  ext i
  fin_cases i <;> simp [e8Update, plane]

theorem plane_norm (x y : ℤ) :
    pairing (plane x y) (plane x y) = 2 * (x^2-x*y+y^2) := by
  simp [plane, pairing, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- After two ticks the live coordinate is zero and the record retains x. -/
theorem e8_clean_two_ticks (x : ℤ) : e8Update (e8Update (plane x 0)) = plane 0 x := by
  simp [plane_action]

/-- The same linear map on real displacement/record variables. -/
def step : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1-p.2, p.1)
  map_add' p q := Prod.ext (by dsimp; ring) (by rfl)
  map_smul' c p := Prod.ext (by dsimp; ring) (by rfl)

theorem clean_two_ticks (x : ℝ) : step (step (x,0)) = (0,x) := by
  simp [step]

theorem clean_one_tick (x : ℝ) : (step (x,0)).1 = x := by simp [step]

/-- No map of the live coordinate alone represents this update on occupied records. -/
theorem no_autonomous_live_map :
    ¬ ∃ A : ℝ →ₗ[ℝ] ℝ, ∀ p, (step p).1 = A p.1 := by
  rintro ⟨A, h⟩
  have hh := h (0,1)
  norm_num [step] at hh

/-- Repeatedly applying the clean-input residual predicts identity, not the reset. -/
theorem clean_input_residual_not_nilpotent (N : ℕ) :
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)^N ≠ 0 := by
  intro h
  have hh := congrArg (fun A : ℝ →ₗ[ℝ] ℝ => A 1) h
  simp at hh

namespace NonlinearEncoding

/-- A genuinely convergent finite reduced map need not respect linear feature relations. -/
def collapse (i : Fin 3) : Fin 3 := if i = 2 then 1 else 0

def encode (i : Fin 3) : ℝ := i.val

theorem restores_in_two : ∀ i, collapse^[2] i = 0 := by decide +kernel

theorem reference_fixed : collapse 0 = 0 := by decide

theorem encoding_spans : Submodule.span ℝ (Set.range encode) = ⊤ := by
  apply top_unique
  intro x _
  have h1 : (1 : ℝ) ∈ Submodule.span ℝ (Set.range encode) :=
    Submodule.subset_span ⟨1, by norm_num [encode]⟩
  simpa using (Submodule.span ℝ (Set.range encode)).smul_mem x h1

/-- The states encoded by 1 and 2 have incompatible successors for any linear A. -/
theorem no_linear_encoding :
    ¬ ∃ A : ℝ →ₗ[ℝ] ℝ, ∀ i, encode (collapse i) = A (encode i) := by
  rintro ⟨A, h⟩
  have h1 := h 1
  have h2 := h 2
  norm_num [collapse, encode] at h1 h2
  have hm := A.map_smul (2 : ℝ) (1 : ℝ)
  norm_num [h1.symm, h2.symm] at hm

end NonlinearEncoding

end PMAction.RecordFeedbackBoundary
