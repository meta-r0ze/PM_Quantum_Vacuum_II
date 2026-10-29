import PMAction.FiniteRestorationBridge
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Exact amplitude restoration implies a trace budget, without a linear microscopic update

An autonomous reduced update may be nonlinear. If it fixes zero, has derivative
`id-K` there, and its Nth iterate is zero on a neighborhood, the chain rule
forces `(id-K)^N = 0` and `trace K = dimension`.

For an arbitrary record-assisted protocol, the *net correction over the whole
protocol* has derivative identity whenever the final displacement is locally
zero. No autonomous per-tick residual or fresh-record reset is assumed for
that statement. It is not a microscopic work or per-tick capacity theorem.

A finite set of restored states does not supply the neighborhood hypothesis.
-/
noncomputable section
namespace PMAction.DifferentialRestoration
open Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The iterate derivative vanishes if every sufficiently small amplitude is exactly restored. -/
theorem iterate_derivative_zero (f : V → V) (A : V →L[ℝ] V)
    (hf : HasFDerivAt f A 0) (hfix : f 0 = 0) (N : ℕ)
    (hrestore : ∀ᶠ d in 𝓝 (0 : V), f^[N] d = 0) : A ^ N = 0 := by
  have hi := hf.iterate hfix N
  have hc : HasFDerivAt (fun _ : V => (0 : V)) 0 0 := hasFDerivAt_const (𝕜 := ℝ) (0 : V) (0 : V)
  exact hi.unique (hc.congr_of_eventuallyEq hrestore)

/-- Nonlinear autonomous amplitude dynamics yield the same finite-restoration gain trace. -/
theorem gain_trace [FiniteDimensional ℝ V] (f : V → V) (K : V →L[ℝ] V)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ V - K) 0)
    (hfix : f 0 = 0) (N : ℕ)
    (hrestore : ∀ᶠ d in 𝓝 (0 : V), f^[N] d = 0) :
    LinearMap.trace ℝ V K.toLinearMap = (Module.finrank ℝ V : ℝ) := by
  have hn := iterate_derivative_zero f _ hf hfix N hrestore
  let forget : (V →L[ℝ] V) →+* (V →ₗ[ℝ] V) := ContinuousLinearMap.toLinearMapRingHom
  have hp : ((LinearMap.id : V →ₗ[ℝ] V) - K.toLinearMap) ^ N = 0 := by
    have hh := congrArg forget hn
    change forget ((1 - K) ^ N) = forget 0 at hh
    have hh' : (forget (1 - K)) ^ N = 0 := by
      simpa only [map_pow, map_zero] using hh
    have he : forget (1 - K) = (LinearMap.id : V →ₗ[ℝ] V) - K.toLinearMap := by
      ext x
      rfl
    rw [he] at hh'
    exact hh'
  have ht := (LinearMap.isNilpotent_trace_of_isNilpotent
    (show IsNilpotent ((LinearMap.id : V →ₗ[ℝ] V) - K.toLinearMap) from ⟨N, hp⟩)).eq_zero
  rw [map_sub, LinearMap.trace_id] at ht
  linarith

/-- Exact record-assisted restoration fixes the derivative of the *total* correction.
`run` may include every internal record/clock update; those records are not discarded. -/
theorem net_correction_derivative {T : Type*} (prepare : V → T) (run : T → T)
    (observe : T → V)
    (hrestore : ∀ᶠ d in 𝓝 (0 : V), observe (run (prepare d)) = 0) :
    HasFDerivAt (fun d => d - observe (run (prepare d))) (ContinuousLinearMap.id ℝ V) 0 := by
  apply (hasFDerivAt_id (0 : V)).congr_of_eventuallyEq
  filter_upwards [hrestore] with d hd
  simp only [hd, sub_zero, id_eq]

/-- A linearized net gain for a complete restoring protocol has the dimension-valued trace. -/
theorem net_gain_trace [FiniteDimensional ℝ V] {T : Type*}
    (prepare : V → T) (run : T → T) (observe : T → V) (K : V →L[ℝ] V)
    (hrestore : ∀ᶠ d in 𝓝 (0 : V), observe (run (prepare d)) = 0)
    (hK : HasFDerivAt (fun d => d - observe (run (prepare d))) K 0) :
    LinearMap.trace ℝ V K.toLinearMap = (Module.finrank ℝ V : ℝ) := by
  have he := hK.unique (net_correction_derivative prepare run observe hrestore)
  rw [he]
  exact LinearMap.trace_id ℝ V

end PMAction.DifferentialRestoration
