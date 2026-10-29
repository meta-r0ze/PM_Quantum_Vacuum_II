import PMAction.ControllerHamiltonian
import PMAction.RotationAlgebra

/-!
# Two-projector functional calculus for an involution

This is operator algebra for a supplied involution. It relates Euclidean
transfer and coherent phase evolution without choosing a spectral basis.
It does not identify the statistical transfer with an executed physical gate.
-/
noncomputable section
namespace PMAction.InvolutionSpectral
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def plus (P : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℂ) • (1+P)
def minus (P : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℂ) • (1-P)

omit [Fintype n] in
lemma sum (P : Matrix n n ℂ) : plus P + minus P = 1 := by
  unfold plus minus
  module

lemma products (P : Matrix n n ℂ) (hP : P*P=1) :
    plus P * plus P = plus P ∧ minus P * minus P = minus P ∧
      plus P * minus P = 0 ∧ minus P * plus P = 0 := by
  constructor
  · simp only [plus, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hP]
    module
  constructor
  · simp only [minus, smul_mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hP]
    module
  constructor <;>
    simp only [plus, minus, smul_mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add,
      one_mul, mul_one, hP] <;> module

/-- A unital two-eigenvalue calculus, proved from the actual involution relation. -/
def spectralMap (P : Matrix n n ℂ) (hP : P*P=1) : (ℂ × ℂ) →+* Matrix n n ℂ where
  toFun z := z.1 • plus P + z.2 • minus P
  map_one' := by simp [sum]
  map_zero' := by simp
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; module
  map_mul' z w := by
    have h := products P hP
    simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_smul_comm,
      h.1, h.2.1, h.2.2.1, h.2.2.2, smul_zero, add_zero, zero_add]

lemma spectralMap_continuous (P : Matrix n n ℂ) (hP : P*P=1) :
    Continuous (spectralMap P hP) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun z : ℂ × ℂ => z.1 * plus P i j + z.2 * minus P i j)
  fun_prop

open scoped Matrix.Norms.Operator in
/-- Exponentiation acts independently on the two spectral sectors. -/
theorem exp_sectors (P : Matrix n n ℂ) (hP : P*P=1) (a b : ℂ) :
    NormedSpace.exp (a • plus P + b • minus P) =
      Complex.exp a • plus P + Complex.exp b • minus P := by
  have he := NormedSpace.map_exp (spectralMap P hP) (spectralMap_continuous P hP) (a,b)
  have hf : (NormedSpace.exp (a,b)).1 = Complex.exp a := by
    simpa only [Complex.exp_eq_exp_ℂ] using!
      NormedSpace.map_exp (RingHom.fst ℂ ℂ) continuous_fst (a,b)
  have hg : (NormedSpace.exp (a,b)).2 = Complex.exp b := by
    simpa only [Complex.exp_eq_exp_ℂ] using!
      NormedSpace.map_exp (RingHom.snd ℂ ℂ) continuous_snd (a,b)
  change (NormedSpace.exp (a,b)).1 • plus P + (NormedSpace.exp (a,b)).2 • minus P =
    NormedSpace.exp (a • plus P + b • minus P) at he
  rw [hf,hg] at he
  exact he.symm

/-- Imaginary-time evolution is a phase times the existing involution rotation. -/
lemma phase_rotation (P : Matrix n n ℂ) (t : ℝ) :
    plus P + Complex.exp (-(2*t : ℝ) * Complex.I) • minus P =
      Complex.exp (-(t : ℝ) * Complex.I) • LocalUnitary.rotation P t := by
  have he : Complex.exp (-(2*t : ℝ) * Complex.I) =
      Complex.exp (-(t : ℝ) * Complex.I) * Complex.exp (-(t : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  simp only [plus, minus, LocalUnitary.rotation, smul_add, smul_smul]
  have hc : Complex.exp (-(t : ℝ) * Complex.I) * (Real.cos t : ℂ) =
      (1 + Complex.exp (-(t : ℝ) * Complex.I)^2)/2 := by
    rw [Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
    have ht := Complex.cos_sq_add_sin_sq (t : ℂ)
    ring_nf
    simp only [Complex.I_sq]
    linear_combination ht / 2
  have hs : Complex.exp (-(t : ℝ) * Complex.I) * (Complex.I * (Real.sin t : ℂ)) =
      (1 - Complex.exp (-(t : ℝ) * Complex.I)^2)/2 := by
    rw [Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
    have ht := Complex.cos_sq_add_sin_sq (t : ℂ)
    ring_nf
    simp only [Complex.I_sq]
    linear_combination ht / 2
  rw [hc, hs]
  module

end PMAction.InvolutionSpectral
