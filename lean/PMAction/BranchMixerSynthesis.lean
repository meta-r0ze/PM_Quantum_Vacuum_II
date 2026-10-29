import PMAction.ComparisonFactorization
import PMAction.RotationAlgebra

/-!
# A pulse implementation of the comparison using the existing involution rotation law

The same `LocalUnitary.rotation` used for the spatial split can be applied
mathematically to branch exchange X and branch parity Z. Quarter-angle X/Z
pulses provide an exact comparison circuit, with no separately postulated
Hadamard gate and no unrecorded global phase.

The additional operational condition is explicit: the rotation law must be
physically admissible on these branch involutions, at these signed angles.
Admissibility of the endpoint permutation alone does not imply this condition.
No microscopic pulse price, branch encoding or clock subdivision is selected.
-/
noncomputable section
namespace PMAction.BranchMixerSynthesis
open Matrix LocalUnitary RotationAlgebra ComparisonFactorization CoherentComparisonRepair
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "BM" => Matrix (n ⊕ n) (n ⊕ n) ℂ

def exchange : BM := fromBlocks 0 1 1 0
def parity : BM := fromBlocks 1 0 0 (-1)

theorem exchange_relations :
    (exchange (n := n)).IsHermitian ∧ exchange (n := n) * exchange = 1 := by
  constructor
  · simp [IsHermitian, exchange, fromBlocks_conjTranspose]
  · simp [exchange, fromBlocks_multiply, fromBlocks_one]

theorem parity_relations :
    (parity (n := n)).IsHermitian ∧ parity (n := n) * parity = 1 := by
  constructor
  · simp [IsHermitian, parity, fromBlocks_conjTranspose]
  · simp [parity, fromBlocks_multiply, fromBlocks_one]

/-- Quarter-angle exchange, not the discrete swap itself. -/
def xPulse (t : ℝ) : BM := rotation exchange t
/-- A relative branch phase, from the same rotation law. -/
def zPulse (t : ℝ) : BM := rotation parity t

theorem xPulse_unitary (t : ℝ) : xPulse (n := n) t ∈ unitary BM :=
  rotation_unitary _ _ exchange_relations.1 exchange_relations.2

theorem zPulse_unitary (t : ℝ) : zPulse (n := n) t ∈ unitary BM :=
  rotation_unitary _ _ parity_relations.1 parity_relations.2

/-- A normalized branch frame; the phase of each column is irrelevant to comparison. -/
def frame : BM := zPulse (-Real.pi / 4) * xPulse (-Real.pi / 4)

def balancedFrame (a b : ℂ) : BM :=
  fromBlocks (a • 1) (b • 1) (a • 1) ((-b) • 1)

/-- Balanced columns suffice; their phases need not be chosen as in Hadamard's matrix. -/
theorem balanced_comparison (a b : ℂ) (ha : a * star a = 1/2)
    (hb : b * star b = 1/2) (U : M) :
    balancedFrame a b * ctrl U * (balancedFrame a b)ᴴ = compare U := by
  simp only [balancedFrame, ctrl, fromBlocks_conjTranspose, fromBlocks_multiply,
    conjTranspose_smul, conjTranspose_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    mul_zero, add_zero, zero_add, star_neg, neg_mul, mul_neg, neg_neg,
    smul_smul, CoherentComparisonRepair.compare, plus, minus]
  have hsa : star a * a = 1/2 := by simpa only [mul_comm] using ha
  have hsb : star b * b = 1/2 := by simpa only [mul_comm] using hb
  simp only [neg_smul, hsa, hsb]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

lemma xPulse_blocks (t : ℝ) : xPulse (n := n) t =
    fromBlocks ((Real.cos t : ℂ) • 1) ((Complex.I * (Real.sin t : ℂ)) • 1)
      ((Complex.I * (Real.sin t : ℂ)) • 1) ((Real.cos t : ℂ) • 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [xPulse, rotation, exchange, Matrix.one_apply]

lemma zPulse_blocks (t : ℝ) : zPulse (n := n) t =
    fromBlocks (((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) • 1) 0 0
      (((Real.cos t : ℂ) - Complex.I * (Real.sin t : ℂ)) • 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    (by_cases h : i = j <;> simp [zPulse, rotation, parity, h, sub_eq_add_neg])

/-- The concrete X/Z pulse frame has exactly the required balanced columns. -/
theorem frame_blocks : frame (n := n) =
    balancedFrame ((1 - Complex.I)/2) (-(1 + Complex.I)/2) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [frame, zPulse_blocks, xPulse_blocks]
  simp only [neg_div, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
    fromBlocks_multiply, balancedFrame, smul_mul_smul_comm, one_mul,
    zero_mul, add_zero, zero_add]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> match_scalars <;> ring_nf <;> simp [hs] <;> norm_num <;> ring

/-- Exact conjugation implements the existing comparison, for every carrier operation. -/
theorem frame_comparison (U : M) : frame * ctrl U * (frame (n := n))ᴴ = compare U := by
  rw [frame_blocks]
  apply balanced_comparison <;> simp [star_sub, star_add, Complex.conj_I] <;> ring_nf <;> norm_num

/-- Five scheduled pulses/operations; no phase normalization is hidden. -/
theorem pulse_comparison (U : M) :
    zPulse (-Real.pi / 4) * xPulse (-Real.pi / 4) * ctrl U *
      xPulse (Real.pi / 4) * zPulse (Real.pi / 4) = compare U := by
  have hx : (xPulse (n := n) (-Real.pi / 4))ᴴ = xPulse (Real.pi / 4) := by
    simpa [xPulse, neg_div] using rotation_adjoint (exchange (n := n)) exchange_relations.1 (-Real.pi / 4)
  have hz : (zPulse (n := n) (-Real.pi / 4))ᴴ = zPulse (Real.pi / 4) := by
    simpa [zPulse, neg_div] using rotation_adjoint (parity (n := n)) parity_relations.1 (-Real.pi / 4)
  have h := frame_comparison U
  simpa only [frame, conjTranspose_mul, hx, hz, Matrix.mul_assoc] using h

end PMAction.BranchMixerSynthesis
