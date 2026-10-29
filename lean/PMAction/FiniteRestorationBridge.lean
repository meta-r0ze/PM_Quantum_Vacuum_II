import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Instances.Discrete
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic

/-!
# From a finite restoring update to a linear displacement restorer

The missing bridge is an operational representation law, not just Finiteness.
If `encode (f s) = A (encode s)` and the encoded states span the displacement
space, uniform exact restoration to a state encoded by zero forces `A^N = 0`.
On a finite discrete state space convergence supplies such a uniform N.
The gain `K = id - A` then has trace equal to the displacement dimension.

`f` is the reduced restoring update. It is not asserted to be a closed
reversible substrate update. Records/environment must justify both this
reduced map and its autonomous representation law. No physical three-dimensional
encoding is selected by this theorem.
-/
noncomputable section
namespace PMAction.FiniteRestorationBridge
open Filter Topology
variable {S V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The same linear residual must represent every tick, including the memory effects. -/
theorem iterate_encoding (f : S → S) (encode : S → V) (A : V →ₗ[ℝ] V)
    (hstep : ∀ s, encode (f s) = A (encode s)) (N : ℕ) (s : S) :
    encode (f^[N] s) = (A ^ N) (encode s) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', hstep, ih, pow_succ']
    rfl

/-- Exact restoration on a spanning physical encoding implies nilpotence. -/
theorem nilpotent_from_encoding (f : S → S) (p : S) (encode : S → V)
    (A : V →ₗ[ℝ] V) (hstep : ∀ s, encode (f s) = A (encode s))
    (hspan : Submodule.span ℝ (Set.range encode) = ⊤) (hp : encode p = 0)
    (N : ℕ) (hrestore : ∀ s, f^[N] s = p) : A ^ N = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change (A ^ N) (encode s) = 0
  rw [← iterate_encoding f encode A hstep N s, hrestore s, hp]

/-- Discrete finite convergence is exact, uniformly over the initial state. -/
theorem finite_convergence_exact [Finite S] [TopologicalSpace S] [DiscreteTopology S]
    (f : S → S) (p : S)
    (hconv : ∀ s, Tendsto (fun N => f^[N] s) atTop (𝓝 p)) :
    ∃ N, ∀ n ≥ N, ∀ s, f^[n] s = p := by
  have he : ∀ s, ∀ᶠ n in atTop, f^[n] s = p := by
    intro s
    simpa only [nhds_discrete, tendsto_pure] using hconv s
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_all.mpr he)
  exact ⟨N, hN⟩

/-- The physical encoding law supplies the nilpotence premise of the trace identity. -/
theorem finite_restoration_gain_trace [FiniteDimensional ℝ V]
    (f : S → S) (p : S) (encode : S → V) (K : V →ₗ[ℝ] V)
    (hstep : ∀ s, encode (f s) = ((LinearMap.id : V →ₗ[ℝ] V) - K) (encode s))
    (hspan : Submodule.span ℝ (Set.range encode) = ⊤) (hp : encode p = 0)
    (N : ℕ) (hrestore : ∀ s, f^[N] s = p) :
    LinearMap.trace ℝ V K = (Module.finrank ℝ V : ℝ) := by
  have hn := nilpotent_from_encoding f p encode ((LinearMap.id : V →ₗ[ℝ] V) - K) hstep hspan hp N hrestore
  have ht := (LinearMap.isNilpotent_trace_of_isNilpotent
    (show IsNilpotent ((LinearMap.id : V →ₗ[ℝ] V) - K) from ⟨N, hn⟩)).eq_zero
  rw [map_sub, LinearMap.trace_id] at ht
  linarith

/-- Convergent finite dynamics plus a spanning linear encoding determine total gain. -/
theorem convergent_gain_trace [Finite S] [TopologicalSpace S] [DiscreteTopology S]
    [FiniteDimensional ℝ V] (f : S → S) (p : S) (encode : S → V) (K : V →ₗ[ℝ] V)
    (hstep : ∀ s, encode (f s) = ((LinearMap.id : V →ₗ[ℝ] V) - K) (encode s))
    (hspan : Submodule.span ℝ (Set.range encode) = ⊤) (hp : encode p = 0)
    (hconv : ∀ s, Tendsto (fun N => f^[N] s) atTop (𝓝 p)) :
    LinearMap.trace ℝ V K = (Module.finrank ℝ V : ℝ) := by
  obtain ⟨N, hN⟩ := finite_convergence_exact f p hconv
  exact finite_restoration_gain_trace f p encode K hstep hspan hp N (hN N le_rfl)

end PMAction.FiniteRestorationBridge
