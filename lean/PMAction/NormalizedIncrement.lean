import PMAction.VacuumDifferential
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! A jointly analytic extension of the corrected split's divided time increment.
The extension is built from the actual seven factors, including the wall exponential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NormalizedIncrement
open Matrix ConcreteFermion VacuumTangent LocalUnitary
open scoped Matrix.Norms.L2Operator
abbrev Momentum := Fin 3 → ℝ
abbrev Joint := ℝ × Momentum
local notation "M" => Matrix Sites Sites ℂ

theorem analytic_dslope_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : AnalyticAt ℝ f 0) : AnalyticAt ℝ (dslope f 0) 0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

def sinQuot (t : ℝ) : ℝ := dslope Real.sin 0 t
def cosQuot (t : ℝ) : ℝ := dslope Real.cos 0 t

theorem sinQuot_zero : sinQuot 0=1 := by simp [sinQuot, dslope_same]
theorem cosQuot_zero : cosQuot 0=0 := by simp [cosQuot, dslope_same]

theorem sinQuot_mul (t : ℝ) : t*sinQuot t=Real.sin t := by
  simpa only [sinQuot, sub_zero, Real.sin_zero, smul_eq_mul] using sub_smul_dslope Real.sin 0 t

theorem cosQuot_mul (t : ℝ) : t*cosQuot t=Real.cos t-1 := by
  simpa only [cosQuot, sub_zero, Real.cos_zero, smul_eq_mul] using sub_smul_dslope Real.cos 0 t

theorem analytic_sinQuot : AnalyticAt ℝ sinQuot 0 := analytic_dslope_zero _ Real.analyticAt_sin
theorem analytic_cosQuot : AnalyticAt ℝ cosQuot 0 := analytic_dslope_zero _ Real.analyticAt_cos

theorem analytic_wall : AnalyticAt ℝ VacuumSplit.wallCoin 0 := by
  have hg : AnalyticAt ℝ (fun t : ℝ => t • ((-Complex.I) • VacuumSplit.wall)) 0 :=
    analyticAt_id.smul analyticAt_const
  have he := (NormedSpace.exp_analytic (𝕂 := ℝ)
    ((0 : ℝ) • ((-Complex.I) • VacuumSplit.wall))).comp
      (f := fun t : ℝ => t • ((-Complex.I) • VacuumSplit.wall)) (x := 0) hg
  simpa only [Function.comp_def, ← VacuumSplit.wallCoin_eq] using! he

def wallQuot (t : ℝ) : M := dslope VacuumSplit.wallCoin 0 t

theorem wallQuot_zero : wallQuot 0=(-Complex.I) • VacuumSplit.wall := by
  rw [wallQuot, dslope_same]
  have hd : HasDerivAt VacuumSplit.wallCoin ((-Complex.I) • VacuumSplit.wall) 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    exact VacuumSplit.wallCoin_deriv.tendsto_slope
  exact hd.deriv

theorem wallQuot_mul (t : ℝ) : t • wallQuot t=VacuumSplit.wallCoin t-1 := by
  simpa only [wallQuot, sub_zero, VacuumSplit.wallCoin_zero] using
    sub_smul_dslope VacuumSplit.wallCoin 0 t

theorem analytic_wallQuot : AnalyticAt ℝ wallQuot 0 := analytic_dslope_zero _ analytic_wall

/-- A primitive or product with an analytic divided time increment at the origin. -/
structure Germ where
  value : Joint → M
  quotient : Joint → M
  analytic_value : AnalyticAt ℝ value 0
  analytic_quotient : AnalyticAt ℝ quotient 0
  identity : ∀ z, z.1 • quotient z=value z-1

namespace Germ

def mul (p q : Germ) : Germ where
  value z := p.value z*q.value z
  quotient z := p.quotient z*q.value z+q.quotient z
  analytic_value := by simpa only [Pi.mul_def] using! p.analytic_value.mul q.analytic_value
  analytic_quotient := by
    simpa only [Pi.add_def, Pi.mul_def] using! (p.analytic_quotient.mul q.analytic_value).add q.analytic_quotient
  identity z := by
    rw [smul_add, ← smul_mul_assoc, p.identity, q.identity]
    noncomm_ring

theorem value_zero (p : Germ) (k : Momentum) : p.value (0,k)=1 := by
  have h := p.identity (0,k)
  simp only [zero_smul] at h
  exact sub_eq_zero.mp h.symm

theorem quotient_mul_zero (p q : Germ) (k : Momentum) :
    (p.mul q).quotient (0,k)=p.quotient (0,k)+q.quotient (0,k) := by
  change p.quotient (0,k)*q.value (0,k)+q.quotient (0,k)=_
  rw [value_zero, mul_one]

end Germ

def wallGerm : Germ where
  value z := VacuumSplit.wallCoin z.1
  quotient z := wallQuot z.1
  analytic_value := by simpa only [Function.comp_def] using! analytic_wall.comp (f := fun z : Joint => z.1) (x := 0) analyticAt_fst
  analytic_quotient := by simpa only [Function.comp_def] using! analytic_wallQuot.comp (f := fun z : Joint => z.1) (x := 0) analyticAt_fst
  identity z := wallQuot_mul z.1

theorem rotation_real (B : M) (t : ℝ) :
    rotation B t=(Real.cos t : ℝ) • (1 : M)+(Real.sin t : ℝ) • (Complex.I • B) := by
  simp only [rotation, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  congr 1
  exact mul_comm _ _

def rotationGerm (B : Joint → M) (hB : AnalyticAt ℝ B 0) : Germ where
  value z := rotation (B z) z.1
  quotient z := cosQuot z.1 • (1 : M)+sinQuot z.1 • (Complex.I • B z)
  analytic_value := by
    have hc : AnalyticAt ℝ (fun z : Joint => Real.cos z.1) 0 := Real.analyticAt_cos.comp analyticAt_fst
    have hs : AnalyticAt ℝ (fun z : Joint => Real.sin z.1) 0 := Real.analyticAt_sin.comp analyticAt_fst
    have h := (hc.smul (analyticAt_const (v := (1 : M)))).add
      (hs.smul ((analyticAt_const (v := Complex.I)).smul hB))
    simpa only [rotation_real, Pi.smul_def, Pi.add_def] using! h
  analytic_quotient := by
    have hc := analytic_cosQuot.comp (f := fun z : Joint => z.1) (x := 0) analyticAt_fst
    have hs := analytic_sinQuot.comp (f := fun z : Joint => z.1) (x := 0) analyticAt_fst
    have h := (hc.smul (analyticAt_const (v := (1 : M)))).add
      (hs.smul ((analyticAt_const (v := Complex.I)).smul hB))
    simpa only [Function.comp_def, Pi.smul_def, Pi.add_def] using! h
  identity z := by
    rw [smul_add, smul_smul, smul_smul, cosQuot_mul, sinQuot_mul, rotation_real]
    module

theorem analytic_direction (j : Fin 3) :
    AnalyticAt ℝ (fun z : Joint => WilsonSplit.directionSymbol j (z.2 j)) 0 := by
  let ev : Joint →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ Momentum)
  have he : AnalyticAt ℝ (fun z : Joint => z.2 j) 0 := ev.analyticAt 0
  have hc := Real.analyticAt_cos.comp he
  have hs := Real.analyticAt_sin.comp he
  simpa only [direction_eq, Pi.smul_def, Pi.sub_def] using!
    (hc.smul (analyticAt_const (v := VacuumSplit.beta8))).sub
      (hs.smul (analyticAt_const (v := alpha8 j)))

def reverseGerm : Germ := rotationGerm (fun _ => -VacuumSplit.beta8) analyticAt_const

def directionGerm (j : Fin 3) : Germ :=
  rotationGerm (fun z => WilsonSplit.directionSymbol j (z.2 j)) (analytic_direction j)

def splitGerm : Germ :=
  let b := (reverseGerm.mul reverseGerm).mul reverseGerm
  let w := wallGerm.mul b
  ((w.mul (directionGerm 0)).mul (directionGerm 1)).mul (directionGerm 2)

theorem split_value (t : ℝ) (k : Momentum) : splitGerm.value (t,k)=VacuumSplit.momentumUpdate k t := by
  change ((VacuumSplit.wallCoin t*((rotation (-VacuumSplit.beta8) t*
    rotation (-VacuumSplit.beta8) t)*rotation (-VacuumSplit.beta8) t))*_)*_*_ = _
  rw [VacuumErrorRate.reverse_eq _ VacuumSplit.beta8_hermitian]
  simp only [VacuumSplit.momentumUpdate, VacuumSplit.onsiteCoin, VacuumSplit.rotation,
    directionGerm, rotationGerm, pow_succ, pow_zero, one_mul]

def increment (z : Joint) : M := splitGerm.quotient z

theorem analytic_increment : AnalyticAt ℝ increment 0 := splitGerm.analytic_quotient

theorem increment_identity (t : ℝ) (k : Momentum) :
    t • increment (t,k)=VacuumSplit.momentumUpdate k t-1 := by
  rw [← split_value]
  exact splitGerm.identity (t,k)

theorem increment_of_ne (t : ℝ) (ht : t ≠ 0) (k : Momentum) :
    increment (t,k)=t⁻¹ • (VacuumSplit.momentumUpdate k t-1) := by
  rw [← increment_identity, inv_smul_smul₀ ht]

theorem increment_zero (k : Momentum) : increment (0,k)=VacuumIteration.generator k := by
  simp only [increment, splitGerm, Germ.quotient_mul_zero, wallGerm, reverseGerm,
    directionGerm, rotationGerm, cosQuot_zero, sinQuot_zero, wallQuot_zero,
    zero_smul, one_smul, zero_add, smul_neg, ← neg_smul]
  rw [VacuumIteration.generator, ← WilsonSplit.generator_identity, ← VacuumSplit.onsite_decomposition]
  simp only [Fin.sum_univ_three]
  module

end PMAction.NormalizedIncrement
