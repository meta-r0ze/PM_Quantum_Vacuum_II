import PMAction.OrthogonalRootPhase
import PMAction.RootPulseEvents

/-!
# The odd-sector complex phase from antipodal reconstruction

Antipodal inversion is an explicit root word. First we identify its reconstructed
phase on the odd sector. The preferred phaseI construction uses four individual
orthogonal root transfers at three positive quarter-times instead; it needs no
lazy kernel for the composite antipodal instruction. The common rate, admission
and time cost remain inputs. No even-complement action is identified with i.
-/
noncomputable section
namespace PMAction.OddCarrierPhase
open Matrix CarrierEvents CarrierParity
open scoped Matrix.Norms.Operator

lemma antipode_intertwining (c : Fin 3) :
    (antipode c).permMatrix ℂ * embedding c = -(embedding c) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← mulVec_mulVec,odd_image,neg_mulVec]

/-- The entire odd sector has one reconstructed phase; no relative basis phase is chosen. -/
theorem phase_sector (c : Fin 3) (p t : ℝ) :
    RootTransferPhase.phase (antipode c) p t * embedding c =
      Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I) • embedding c := by
  rw [RootTransferPhase.phase_formula _ (antipode_involutive c)]
  simp only [Matrix.smul_mul,InvolutionSpectral.plus,InvolutionSpectral.minus,
    Matrix.add_mul,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,antipode_intertwining]
  module

def phaseI (c : Fin 3) (p : ℝ) :=
  OrthogonalRootPhase.phase c p (3*RootTransferPhase.quarterTime p)

theorem phase_time_positive (p : ℝ) (hp : 0<p) (hp1 : p<1/2) :
    0 < 3*RootTransferPhase.quarterTime p :=
  mul_pos (by norm_num) (RootTransferPhase.quarterTime_positive p hp hp1)

lemma quarter_exp : Complex.exp (((-(Real.pi/2) : ℝ) : ℂ)*Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I]
  simp

theorem phaseI_sector (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) :
    phaseI c p * embedding c = Complex.I • embedding c := by
  rw [phaseI,OrthogonalRootPhase.phase_sector]
  have ha := RootPulseEvents.quarter_angle p hp hp1
  have ht : -(RootTransferPhase.gap p*(3*RootTransferPhase.quarterTime p) : ℝ)*Complex.I =
      (3 : ℂ) * (((-(Real.pi/2) : ℝ) : ℂ)*Complex.I) := by
    have hh : RootTransferPhase.gap p*(3*RootTransferPhase.quarterTime p)=3*(Real.pi/2) := by
      nlinarith [ha]
    rw [hh]
    push_cast
    ring
  rw [ht]
  have he := Complex.exp_nat_mul (((-(Real.pi/2) : ℝ) : ℂ)*Complex.I) 3
  norm_num only [Nat.cast_ofNat] at he
  rw [he,quarter_exp]
  have hi : (-Complex.I)^3 = Complex.I := by
    calc
      _ = -(Complex.I * Complex.I) * Complex.I := by ring
      _ = Complex.I := by rw [Complex.I_mul_I]; ring
  rw [hi]

/-- The previously imaginary alpha generator now has a specified native phase route. -/
def alpha1 (c : Fin 3) (p : ℝ) := phaseI c p * (CarrierWeyl.lookup c 4).permMatrix ℂ

theorem alpha1_intertwining (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) :
    alpha1 c p * embedding c = embedding c * ConcreteFermion.alpha 1 := by
  rw [alpha1,Matrix.mul_assoc,CarrierWeyl.intertwining,← Matrix.mul_assoc,
    phaseI_sector c p hp hp1,Matrix.smul_mul,← Matrix.mul_smul,CarrierWeyl.alpha1_eq]

end PMAction.OddCarrierPhase
