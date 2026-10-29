import PMAction.BranchMixerSynthesis
import PMAction.BranchGateBoundary

/-!
# The precise operational contract and scheduled price of the pulse construction

Closure under the *continuous* involution rotation law is a sufficient extra
operational condition. It is stronger than unitary Conservation together with
available branch exchange/parity. `classical_not_rotation_closed` gives a
counterexample using all unitary single-support gates.

The displayed five-instruction program has a supplied scheduled price,
not a minimum E8 toll or a flag-conditioned event count. Its branch pulses
couple only the two branch entries of the same carrier index.
-/
noncomputable section
namespace PMAction.BranchPulseContract
open Matrix BranchMixerSynthesis ComparisonFactorization BranchGateBoundary
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "BM" => Matrix (n ⊕ n) (n ⊕ n) ℂ

/-- Internal rotations are admissible whenever their involution is admissible.
This is an operational closure premise, not the definition of persistence. -/
def RotationClosed (S : Submonoid BM) : Prop :=
  ∀ B ∈ S, B.IsHermitian → B * B = 1 → ∀ t : ℝ, LocalUnitary.rotation B t ∈ S

/-- The same rotation rule on branch X and Z suffices to implement comparison. -/
theorem comparison_mem (S : Submonoid BM) (hrot : RotationClosed S)
    (hx : exchange ∈ S) (hz : parity ∈ S) (U : M) (hu : ctrl U ∈ S) :
    CoherentComparisonRepair.compare U ∈ S := by
  have hX (t : ℝ) : xPulse t ∈ S := hrot _ hx exchange_relations.1 exchange_relations.2 t
  have hZ (t : ℝ) : zPulse t ∈ S := hrot _ hz parity_relations.1 parity_relations.2 t
  rw [← pulse_comparison]
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hZ _) (hX _)) hu) (hX _)) (hZ _)

/-- Equal branch weights in the first quadrant uniquely determine the pulse angle.
Balance is the specified comparison task, not a new consequence of survival. -/
theorem balanced_angle_iff (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ Real.pi / 2) :
    Real.sin t ^ 2 = 1/2 ↔ t = Real.pi / 4 := by
  have hp := Real.pi_pos
  have hsq : Real.sin (Real.pi / 4) ^ 2 = 1/2 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  constructor
  · intro h
    have hn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    have hn' : 0 ≤ Real.sin (Real.pi / 4) := by rw [Real.sin_pi_div_four]; positivity
    have he : Real.sin t = Real.sin (Real.pi / 4) := by nlinarith
    exact Real.strictMonoOn_sin.injOn ⟨by linarith, h1⟩ ⟨by linarith, by linarith⟩ he
  · rintro rfl
    exact hsq

/-- The pulse reads only the two branch amplitudes of the same carrier. -/
theorem exchange_pulse_pair (t : ℝ) (ψ : n ⊕ n → ℂ) (a : n) :
    (xPulse t *ᵥ ψ) (.inl a) =
      (Real.cos t : ℂ) * ψ (.inl a) + Complex.I * (Real.sin t : ℂ) * ψ (.inr a) ∧
    (xPulse t *ᵥ ψ) (.inr a) =
      Complex.I * (Real.sin t : ℂ) * ψ (.inl a) + (Real.cos t : ℂ) * ψ (.inr a) := by
  rw [xPulse_blocks, fromBlocks_mulVec]
  simp [Matrix.smul_mulVec]

/-- Squared modulus of the exchange pulse's cross-branch entry. -/
theorem transfer_weight (t : ℝ) (a : n) :
    Complex.normSq (xPulse t (.inr a) (.inl a)) = Real.sin t ^ 2 := by
  simp only [xPulse_blocks, fromBlocks_apply₂₁, Matrix.smul_apply, Matrix.one_apply,
    ite_true, smul_eq_mul, mul_one, Complex.normSq_mul, Complex.normSq_I,
    one_mul, Complex.normSq_ofReal]
  ring

inductive Instruction where
  | x (angle : ℝ)
  | z (angle : ℝ)
  | controlled

def program : List Instruction :=
  [.z (-Real.pi / 4), .x (-Real.pi / 4), .controlled,
    .x (Real.pi / 4), .z (Real.pi / 4)]

def decode (U : M) : Instruction → BM
  | .x t => xPulse t
  | .z t => zPulse t
  | .controlled => ctrl U

theorem program_correct (U : M) :
    (program.map (decode U)).prod = CoherentComparisonRepair.compare U := by
  simpa only [program, decode, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, Matrix.mul_assoc] using pulse_comparison U

/-- Each signed pulse is assigned its scheduled price; no activity discount is assumed. -/
def price (wX wZ wC : ℝ) : Instruction → ℝ
  | .x _ => wX
  | .z _ => wZ
  | .controlled => wC

theorem program_price (wX wZ wC : ℝ) :
    (program.map (price wX wZ wC)).sum = 2 * wX + 2 * wZ + wC := by
  simp only [program, price, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Quarter exchange creates two nonzero entries in one basis column. -/
theorem quarter_exchange_not_classical [Nonempty n] :
    ¬ BasisPreserving (xPulse (n := n) (-Real.pi / 4)) := by
  intro h
  let a : n := Classical.choice inferInstance
  obtain ⟨i, c, hi⟩ := h (.inl a)
  have hl : Sum.inl a = i := by
    by_contra he
    have hh := hi (.inl a)
    simp [xPulse_blocks, he, neg_div, Real.cos_pi_div_four] at hh
  have hr : Sum.inr a = i := by
    by_contra he
    have hh := hi (.inr a)
    simp [xPulse_blocks, he, neg_div, Real.sin_pi_div_four] at hh
  have hf : (Sum.inl a : n ⊕ n) = Sum.inr a := hl.trans hr.symm
  cases hf

/-- The monoid of single-support gates, before imposing unitarity. -/
def basisMonoid : Submonoid BM where
  carrier := BasisPreserving
  one_mem' := by
    change BasisPreserving (1 : BM)
    simpa using (diagonal_preserves (fun _ : n ⊕ n => (1 : ℂ)))
  mul_mem' := mul_preserves

/-- A conservative gate model admitting every unitary permutation/diagonal gate. -/
def classicalGates : Submonoid BM := unitary BM ⊓ basisMonoid

lemma exchange_classical : exchange (n := n) ∈ classicalGates := by
  constructor
  · constructor <;>
      simpa only [star_eq_conjTranspose, (exchange_relations (n := n)).1.eq] using
        (exchange_relations (n := n)).2
  · intro j
    rcases j with j | j
    · refine ⟨.inr j, 1, fun k => ?_⟩
      rcases k with k | k <;> simp [exchange, Matrix.one_apply, eq_comm]
    · refine ⟨.inl j, 1, fun k => ?_⟩
      rcases k with k | k <;> simp [exchange, Matrix.one_apply, eq_comm]

lemma parity_classical : parity (n := n) ∈ classicalGates := by
  constructor
  · constructor <;>
      simpa only [star_eq_conjTranspose, (parity_relations (n := n)).1.eq] using
        (parity_relations (n := n)).2
  · intro j
    rcases j with j | j
    · refine ⟨.inl j, 1, fun k => ?_⟩
      rcases k with k | k <;>
        (by_cases h : j = k <;> simp [parity, eq_comm, h])
    · refine ⟨.inr j, -1, fun k => ?_⟩
      rcases k with k | k <;>
        (by_cases h : j = k <;> simp [parity, eq_comm, h])

/-- Unitary Conservation and available X/Z do not imply continuous rotation closure. -/
theorem classical_not_rotation_closed [Nonempty n] :
    ¬ RotationClosed (classicalGates (n := n)) := by
  intro h
  have hp := h _ exchange_classical exchange_relations.1 exchange_relations.2 (-Real.pi / 4)
  exact quarter_exchange_not_classical hp.2

end PMAction.BranchPulseContract
