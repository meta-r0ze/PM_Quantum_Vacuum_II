import PMAction.BranchMixerSynthesis
import PMAction.CarrierResponse
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# A finite mode exchange has one exact linear-amplitude repair

The already constructed branch exchange swaps two copies of the carrier modes.
Its finite label permutation determines its matrix uniquely. With the record
modes prepared in a reference amplitude, it restores all live amplitudes and
retains the complete input in the record. No smooth extension of Boolean
feature values is selected or needed.

The records here are **coherent amplitude modes**, not independent tensor
subsystems or probabilities of Boolean configurations. Their physical encoding,
preparation, locality and price remain operational obligations. A second exchange
with an occupied record undoes the repair. This is not a renewable reservoir.
-/
noncomputable section
namespace PMAction.CoherentRecordRestoration
open Matrix BranchMixerSynthesis
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The repair is the existing finite branch-mode permutation. -/
theorem exchange_is_permutation : exchange (n := n) = Equiv.Perm.permMatrix ℂ (Equiv.sumComm n n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [exchange, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]

/-- In the linear-amplitude model, the basis-label action fixes the entire update. -/
theorem unique_linear_lift (U : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (h : ∀ j, U *ᵥ Pi.single j 1 = Pi.single ((Equiv.sumComm n n) j) 1) :
    U = exchange := by
  ext i j
  have hh := congrFun (h j) i
  rcases i with i | i <;> rcases j with j | j <;>
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, exchange, Pi.single_apply, Matrix.one_apply, eq_comm] using hh

theorem exchange_unitary : exchange (n := n) ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  rw [exchange_is_permutation]
  exact CarrierResponse.perm_unitary _

theorem exchange_action (live record : n → ℂ) :
    exchange *ᵥ Sum.elim live record = Sum.elim record live := by
  rw [exchange, fromBlocks_mulVec]
  simp

theorem norm_preserved (ψ : n ⊕ n → ℂ) :
    CommonResponse.nsq (exchange *ᵥ ψ) = CommonResponse.nsq ψ :=
  congrArg Complex.re (CommonResponse.unitary_nsq _ exchange_unitary ψ)

/-- Every amplitude is restored; every input distinction is retained coherently. -/
theorem prepared_repair (reference input : n → ℂ) :
    (∀ i, (exchange *ᵥ Sum.elim input reference) (.inl i) = reference i) ∧
      (∀ i, (exchange *ᵥ Sum.elim input reference) (.inr i) = input i) := by
  rw [exchange_action]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem repair_nonidle_iff (reference input : n → ℂ) :
    exchange *ᵥ Sum.elim input reference ≠ Sum.elim input reference ↔ input ≠ reference := by
  rw [exchange_action]
  constructor
  · intro h he
    exact h (by rw [he])
  · intro h he
    apply h
    funext i
    exact (congrFun he (.inl i)).symm

/-- The same occupied record cannot be silently reused as another clean reference. -/
theorem twice_undoes (ψ : n ⊕ n → ℂ) : exchange *ᵥ (exchange *ᵥ ψ) = ψ := by
  rw [mulVec_mulVec, (exchange_relations (n := n)).2, one_mulVec]

/-- Every square unitary reset with zero live-input block routes the input to a
unitary record encoding. Swap is its canonical representative, not a guessed loss map. -/
theorem unitary_reset_blocks (A B C : Matrix n n ℂ)
    (hU : fromBlocks 0 A B C ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    C = 0 ∧ A ∈ unitary (Matrix n n ℂ) ∧ B ∈ unitary (Matrix n n ℂ) := by
  have hl : (fromBlocks 0 A B C)ᴴ * fromBlocks 0 A B C = 1 := hU.1
  have hr : fromBlocks 0 A B C * (fromBlocks 0 A B C)ᴴ = 1 := hU.2
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero,
    zero_mul, mul_zero, zero_add, ← fromBlocks_one, fromBlocks_inj] at hl hr
  have hb : B * Bᴴ = 1 := mul_eq_one_comm.mp hl.1
  have ha : Aᴴ * A = 1 := mul_eq_one_comm.mp hr.1
  have hc : C = 0 := by
    calc
      C = (B * Bᴴ) * C := by rw [hb, one_mul]
      _ = B * (Bᴴ * C) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hl.2.1, mul_zero]
  refine ⟨hc, ?_, ?_⟩
  · exact ⟨ha, hr.1⟩
  · exact ⟨hl.1, hb⟩

/-- The resulting zero-live-block reset is swap followed by unitary encodings. -/
theorem unitary_reset_factorization (A B C : Matrix n n ℂ)
    (hU : fromBlocks 0 A B C ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    fromBlocks 0 A B C = fromBlocks A 0 0 B * exchange := by
  rw [(unitary_reset_blocks A B C hU).1]
  simp [exchange, fromBlocks_multiply]

section Memory
variable {𝕜 : Type*} [Field 𝕜] {V R : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup R] [Module 𝕜 R]

/-- The actual record channel of a linear total update on live and record displacements. -/
def recordMap (T : (V × R) →ₗ[𝕜] (V × R)) : V →ₗ[𝕜] R :=
  (LinearMap.snd 𝕜 V R).comp (T.comp (LinearMap.inl 𝕜 V R))

/-- Conservation forces the record to retain every restored displacement distinction. -/
theorem record_injective (T : (V × R) →ₗ[𝕜] (V × R)) (hT : Function.Injective T)
    (hreset : ∀ x, (T (x,0)).1 = 0) : Function.Injective (recordMap T) := by
  intro x y h
  have hr : (T (x,0)).2 = (T (y,0)).2 := h
  have he : T (x,0) = T (y,0) := Prod.ext ((hreset x).trans (hreset y).symm) hr
  exact congrArg Prod.fst (hT he)

/-- A finite-dimensional linear record cannot have fewer directions than the erased live task. -/
theorem record_dimension_bound [FiniteDimensional 𝕜 R]
    (T : (V × R) →ₗ[𝕜] (V × R)) (hT : Function.Injective T)
    (hreset : ∀ x, (T (x,0)).1 = 0) : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 R :=
  LinearMap.finrank_le_finrank_of_injective (record_injective T hT hreset)

end Memory
end PMAction.CoherentRecordRestoration
