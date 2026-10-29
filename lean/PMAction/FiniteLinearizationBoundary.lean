import PMAction.DifferentialRestoration
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A finite exact protocol does not determine the derivative of its amplitude extension

The finite states are three independent Boolean displacement coordinates. The
closed protocol swaps live state and record, so clean records give exact live
restoration and retain the input. Its displacement encoding spans R^3.

For every real a, the polynomial `a (x-x^3)` applied coordinatewise agrees
with the same reduced reset on all eight encoded states, but has derivative
a times identity at zero. Thus the linearized gain has trace 3(1-a), despite
identical finite restoration data. The finite-to-amplitude extension, and its
exactness on a neighborhood, must be supplied by the actual dynamics.
-/
noncomputable section
namespace PMAction.FiniteLinearizationBoundary
open Filter Topology
abbrev V := Fin 3 → ℝ
abbrev S := Fin 3 → Bool

def encode (s : S) : V := fun i => if s i then 1 else 0

def protocol : Equiv.Perm (S × S) := Equiv.prodComm S S

theorem clean_record_restores (s : S) : protocol (s, fun _ => false) = (fun _ => false, s) := rfl

theorem protocol_repeats (s : S × S) : protocol (protocol s) = s := by cases s; rfl

def extension (a : ℝ) (x : V) : V := a • (x - x * x * x)

/-- Every member of the family extends exactly the same finite reduced reset. -/
theorem extension_agrees (a : ℝ) (s : S) : extension a (encode s) = 0 := by
  ext i
  cases hs : s i <;> simp [extension, encode, hs]

/-- The encoded finite states span all three displacement coordinates. -/
theorem encoding_spans : Submodule.span ℝ (Set.range encode) = ⊤ := by
  apply top_unique
  intro x _
  have he (i : Fin 3) : (Pi.single i (1 : ℝ) : V) ∈ Submodule.span ℝ (Set.range encode) := by
    apply Submodule.subset_span
    refine ⟨fun j => decide (j = i), ?_⟩
    ext j
    by_cases h : j = i <;> simp [encode, h]
  have hx : x = ∑ i : Fin 3, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (he i))

/-- Smooth extensions of the finite protocol can have any scalar residual derivative. -/
theorem extension_derivative (a : ℝ) :
    HasFDerivAt (extension a) (a • ContinuousLinearMap.id ℝ V) 0 := by
  have h : HasFDerivAt (fun x : V => x) (ContinuousLinearMap.id ℝ V) 0 :=
    hasFDerivAt_id (0 : V)
  have hc := (h.mul h).mul h
  simpa [extension] using (h.sub hc).const_smul a

/-- Every member with 0 ≤ a ≤ 1 is locally stable, so mere persistence does not select a. -/
theorem extension_norm_le (a : ℝ) (ha : 0 ≤ a) (x : V) (hx : ‖x‖ ≤ 1) :
    ‖extension a x‖ ≤ a * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg ha (norm_nonneg x))).mpr
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using
      (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl i
  have hxi : |x i| ≤ 1 := hi.trans hx
  have hs : x i ^ 2 ≤ 1 := by nlinarith [abs_le.mp hxi]
  have hn : 0 ≤ 1 - x i ^ 2 := by linarith
  have he : extension a x i = a * x i * (1 - x i ^ 2) := by
    simp [extension]
    ring
  rw [Real.norm_eq_abs, he, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hn]
  calc
    a * |x i| * (1 - x i ^ 2) ≤ a * |x i| * 1 :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x i)]) (mul_nonneg ha (abs_nonneg _))
    _ ≤ a * ‖x‖ := by simpa using mul_le_mul_of_nonneg_left hi ha

theorem iterate_norm_le (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (x : V)
    (hx : ‖x‖ ≤ 1) (N : ℕ) : ‖(extension a)^[N] x‖ ≤ a ^ N * ‖x‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hc : ‖(extension a)^[N] x‖ ≤ 1 := by
      calc
        _ ≤ a ^ N * ‖x‖ := ih
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha1) (norm_nonneg x)
        _ ≤ 1 := by simpa using hx
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ a * ‖(extension a)^[N] x‖ := extension_norm_le a ha _ hc
      _ ≤ a * (a ^ N * ‖x‖) := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ (N + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- Both a=0 and a=1/2 are persistent local restoring dynamics, with different traces. -/
theorem extension_converges (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (x : V)
    (hx : ‖x‖ ≤ 1) : Tendsto (fun N => (extension a)^[N] x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (iterate_norm_le a ha ha1.le x hx)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1).mul_const ‖x‖

/-- The corresponding linearized restoring gain. -/
def gain (a : ℝ) : V →ₗ[ℝ] V := (1-a) • LinearMap.id

theorem gain_trace (a : ℝ) : LinearMap.trace ℝ V (gain a) = 3 * (1-a) := by
  simp [gain, LinearMap.trace_id]
  ring

/-- Identical finite reset data are compatible with distinct linearized gain traces. -/
theorem trace_not_fixed :
    (∀ s, extension 0 (encode s) = extension (1/2) (encode s)) ∧
      LinearMap.trace ℝ V (gain 0) = 3 ∧
      LinearMap.trace ℝ V (gain (1/2)) = 3/2 := by
  refine ⟨fun s => by rw [extension_agrees, extension_agrees], ?_, ?_⟩ <;>
    norm_num [gain_trace]

end PMAction.FiniteLinearizationBoundary
