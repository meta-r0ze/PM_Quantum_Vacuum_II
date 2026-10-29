import PMAction.CoherentRecordRestoration
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.OfFn

/-!
# Conservative transport of occupied coherent records

A finite cyclic mode shift realizes a FIFO record buffer. An input stream and
an initially prepared buffer are transported into the output stream and final
buffer without deleting any value. R initially zero record packets allow R
successive zero-discrepancy outputs; the next output is the first old input.

This supplies an explicit finite-duration record-flow implementation, not a
renewable clean reservoir. The ports are direct-sum coherent modes. Their E8
encoding, preparation, physical spatial embedding and primitive prices are
not selected here. External inputs and outgoing values are retained in the
stream contract, not identified with a closed vacuum evolution.
-/
noncomputable section
namespace PMAction.RecordTransport
open Matrix

section Modes
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One incoming/output port and R record ports, shifted cyclically. -/
def shift (R : ℕ) : Equiv.Perm (Fin (R + 1) × n) :=
  (finRotate (R + 1)).prodCongr (Equiv.refl n)

def tick (R : ℕ) (ψ : Fin (R + 1) × n → ℂ) : Fin (R + 1) × n → ℂ :=
  (shift R).permMatrix ℂ *ᵥ ψ

lemma tick_apply (R : ℕ) (ψ : Fin (R + 1) × n → ℂ) (i : Fin (R + 1)) (a : n) :
    tick R ψ (i,a) = ψ (finRotate (R + 1) i,a) := by
  rw [tick, Matrix.permMatrix_mulVec]
  rfl

theorem tick_unitary (R : ℕ) :
    (shift (n := n) R).permMatrix ℂ ∈ unitary (Matrix (Fin (R+1) × n) (Fin (R+1) × n) ℂ) :=
  CarrierResponse.perm_unitary _

theorem tick_norm (R : ℕ) (ψ : Fin (R + 1) × n → ℂ) :
    CommonResponse.nsq (tick R ψ) = CommonResponse.nsq ψ :=
  congrArg Complex.re (CommonResponse.unitary_nsq _ (tick_unitary R) ψ)

/-- The finite basis action uniquely fixes its complex-linear amplitude update. -/
theorem unique_linear_lift (R : ℕ)
    (U : Matrix (Fin (R+1) × n) (Fin (R+1) × n) ℂ)
    (h : ∀ j, U *ᵥ Pi.single j 1 = (shift R).permMatrix ℂ *ᵥ Pi.single j 1) :
    U = (shift R).permMatrix ℂ := by
  ext i j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (h j) i

/-- Exactly the oldest record is returned, and the input enters the final port. -/
theorem tick_fifo (R : ℕ) (input : n → ℂ) (records : Fin R → n → ℂ)
    (i : Fin (R+1)) (a : n) :
    tick R (fun p => (@Fin.cons R (fun _ => n → ℂ) input records p.1) p.2) (i,a) =
      (@Fin.snoc R (fun _ => n → ℂ) records input i) a := by
  rw [tick_apply, Fin.snoc_eq_cons_rotate]

/-- Every output port reads precisely one neighbouring port on the specified ring. -/
theorem tick_local (R : ℕ) (ψ φ : Fin (R+1) × n → ℂ) (i : Fin (R+1))
    (h : ∀ a, ψ (finRotate (R+1) i,a) = φ (finRotate (R+1) i,a)) :
    ∀ a, tick R ψ (i,a) = tick R φ (i,a) := by
  intro a
  simpa only [tick_apply] using h a

end Modes

section Streams
variable {V : Type*}

/-- Execute the FIFO; every outgoing packet is retained in the first result.
An empty buffer is a passthrough, not a reset. -/
def run : List V → List V → List V × List V
  | [], records => ([], records)
  | x :: xs, [] => let r := run xs []; (x :: r.1, r.2)
  | x :: xs, r :: rs => let s := run xs (rs ++ [x]); (r :: s.1, s.2)

lemma output_length (inputs records : List V) :
    (run inputs records).1.length = inputs.length := by
  induction inputs generalizing records with
  | nil => rfl
  | cons x xs ih => cases records <;> simp [run, ih]

lemma record_length (inputs records : List V) :
    (run inputs records).2.length = records.length := by
  induction inputs generalizing records with
  | nil => rfl
  | cons x xs ih => cases records <;> simp [run, ih]

/-- Stronger than a norm identity: the complete ordered stream is conserved. -/
theorem stream_conserved (inputs records : List V) :
    (run inputs records).1 ++ (run inputs records).2 = records ++ inputs := by
  induction inputs generalizing records with
  | nil => simp [run]
  | cons x xs ih =>
    cases records with
    | nil => simpa [run] using congrArg (List.cons x) (ih [])
    | cons r rs => simpa [run, List.append_assoc] using congrArg (List.cons r) (ih (rs ++ [x]))

lemma output_eq (inputs records : List V) :
    (run inputs records).1 = (records ++ inputs).take inputs.length := by
  calc
    _ = ((run inputs records).1 ++ (run inputs records).2).take
        (run inputs records).1.length := by simp
    _ = _ := by rw [stream_conserved, output_length]

lemma records_eq (inputs records : List V) :
    (run inputs records).2 = (records ++ inputs).drop inputs.length := by
  calc
    _ = ((run inputs records).1 ++ (run inputs records).2).drop
        (run inputs records).1.length := by simp
    _ = _ := by rw [stream_conserved, output_length]

/-- R prepared reference packets suffice for any input stream of at most R trials. -/
theorem clean_outputs (zero : V) (R : ℕ) (inputs : List V) (h : inputs.length ≤ R) :
    (run inputs (List.replicate R zero)).1 = List.replicate inputs.length zero := by
  rw [output_eq, List.take_append]
  simp [List.take_replicate, Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]

/-- Used packets remain in the buffer; no re-preparation occurs between trials. -/
theorem occupied_records (zero : V) (R : ℕ) (inputs : List V) (h : inputs.length ≤ R) :
    (run inputs (List.replicate R zero)).2 = List.replicate (R-inputs.length) zero ++ inputs := by
  rw [records_eq, List.drop_append]
  simp [List.drop_replicate, Nat.sub_eq_zero_of_le h]

/-- At capacity the entire input history is retained, in order. -/
theorem full_records (zero : V) (inputs : List V) :
    (run inputs (List.replicate inputs.length zero)).2 = inputs := by
  simpa using occupied_records zero inputs.length inputs le_rfl

/-- The first over-capacity output is the first old input, not a fresh reference. -/
theorem first_return (zero x : V) (xs : List V) :
    (run (x :: xs) (List.replicate xs.length zero)).1 =
      List.replicate xs.length zero ++ [x] := by
  rw [output_eq, List.take_append]
  simp [List.take_replicate]

/-- A finite buffer cannot provide indefinite universal restoration. -/
theorem no_unlimited_clean (zero x : V) (hx : x ≠ zero) (R : ℕ) :
    ¬ ∀ inputs : List V, (run inputs (List.replicate R zero)).1 =
      List.replicate inputs.length zero := by
  intro h
  have hh := h (x :: List.replicate R zero)
  have hr := first_return zero x (List.replicate R zero)
  simp only [List.length_replicate] at hr
  rw [hr] at hh
  have he := congrArg (fun L => L.drop R) hh
  exact hx (by simpa using he)

/-- Additive packet observables (including squared norm) balance across the boundary. -/
theorem observable_balance {A : Type*} [AddCommMonoid A] (f : V → A)
    (inputs records : List V) :
    ((run inputs records).1.map f).sum + ((run inputs records).2.map f).sum =
      (records.map f).sum + (inputs.map f).sum := by
  have h := congrArg (fun L => (L.map f).sum) (stream_conserved inputs records)
  simpa using h

end Streams

section Realization
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The stream interpreter's one-step outputs are exactly the unitary mode shift. -/
theorem single_step_realized (R : ℕ) (input : n → ℂ) (records : Fin R → n → ℂ) :
    List.ofFn (fun i a => tick R
      (fun p => (@Fin.cons R (fun _ => n → ℂ) input records p.1) p.2) (i,a)) =
      (run [input] (List.ofFn records)).1 ++ (run [input] (List.ofFn records)).2 := by
  rw [stream_conserved]
  have he : (fun i a => tick R
      (fun p => (@Fin.cons R (fun _ => n → ℂ) input records p.1) p.2) (i,a)) =
      @Fin.snoc R (fun _ => n → ℂ) records input := by
    funext i a
    exact tick_fifo R input records i a
  rw [he, List.ofFn_succ_last]
  simp

omit [DecidableEq n] in
/-- Total squared amplitude is balanced, including all incoming and outgoing packets. -/
theorem stream_norm_balance (inputs records : List (n → ℂ)) :
    ((run inputs records).1.map CommonResponse.nsq).sum +
        ((run inputs records).2.map CommonResponse.nsq).sum =
      (records.map CommonResponse.nsq).sum + (inputs.map CommonResponse.nsq).sum :=
  observable_balance CommonResponse.nsq inputs records

omit [DecidableEq n] in
/-- Any conservative linear protocol restoring N independent packets needs
at least N packet dimensions of retained memory, regardless of its circuit. -/
theorem history_memory_bound (N R : ℕ)
    (T : ((Fin N → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ]
      ((Fin N → n → ℂ) × (Fin R → n → ℂ)))
    (hT : Function.Injective T) (hreset : ∀ inputs, (T (inputs,0)).1 = 0) :
    N * Fintype.card n ≤ R * Fintype.card n := by
  simpa [Module.finrank_pi_fintype] using
    CoherentRecordRestoration.record_dimension_bound T hT hreset

omit [DecidableEq n] in
/-- Nonempty packets cannot be compressed into fewer clean record packets. -/
theorem history_packet_bound [Nonempty n] (N R : ℕ)
    (T : ((Fin N → n → ℂ) × (Fin R → n → ℂ)) →ₗ[ℂ]
      ((Fin N → n → ℂ) × (Fin R → n → ℂ)))
    (hT : Function.Injective T) (hreset : ∀ inputs, (T (inputs,0)).1 = 0) : N ≤ R :=
  Nat.le_of_mul_le_mul_right (history_memory_bound N R T hT hreset) Fintype.card_pos

end Realization
end PMAction.RecordTransport
