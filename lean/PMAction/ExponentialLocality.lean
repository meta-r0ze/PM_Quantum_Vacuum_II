import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! A nonzero second-hop coefficient prevents an exponential entry from
vanishing on a whole tick neighbourhood. No numerical residual is used. -/
noncomputable section
namespace PMAction.ExponentialLocality
open Matrix NormedSpace Filter Topology
open scoped Matrix.Norms.Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

def entry (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  ({ toFun := fun M => M i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Matrix n n ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- Any nonzero second derivative rules out a whole open interval of zero
matrix entries, even when the initial and first-derivative entries vanish. -/
theorem second_hop (A : Matrix n n ℂ) (i j : n) (h2 : (A*A) i j ≠ 0) :
    ∀ ε : ℝ, 0<ε → ∃ t : ℝ, |t|<ε ∧ exp (t • A) i j ≠ 0 := by
  let f : ℝ → ℂ := fun t => exp (t • A) i j
  let g : ℝ → ℂ := fun t => (exp (t • A) * A) i j
  have hd (t : ℝ) : HasDerivAt f (g t) t := by
    exact (entry i j).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const A t)
  have hdd : HasDerivAt g ((A*A) i j) 0 := by
    have hh : HasDerivAt g ((exp ((0 : ℝ) • A) * A * A) i j) 0 :=
      (entry i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_exp_smul_const A (0 : ℝ)).mul_const A)
    simpa only [zero_smul, exp_zero, Matrix.one_mul] using hh
  intro ε hε
  by_contra hn
  push Not at hn
  have hf (t : ℝ) (ht : |t|<ε) : f =ᶠ[𝓝 t] (fun _ => (0 : ℂ)) := by
    have hm : Set.Ioo (-ε) ε ∈ 𝓝 t := isOpen_Ioo.mem_nhds (abs_lt.mp ht)
    filter_upwards [hm] with s hs
    exact hn s (abs_lt.mpr hs)
  have hg (t : ℝ) (ht : |t|<ε) : g t=0 :=
    (hd t).unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq (hf t ht))
  have hge : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
    have hm : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds (by constructor <;> linarith)
    filter_upwards [hm] with s hs
    exact hg s (abs_lt.mpr hs)
  exact h2 (hdd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hge))

end PMAction.ExponentialLocality
