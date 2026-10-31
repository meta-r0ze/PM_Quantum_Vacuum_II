import PMAction.ConnectionRegularity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Existence of matrix parallel transport from a continuous skew-Hermitian
coefficient. A compactly supported scalar cutoff makes the Picard field bounded;
conservation of T T† then proves the cutoff never changes the solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.TransportExistence
open Matrix Set Metric Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {N : ℕ}
local notation "M" => Matrix (Fin N) (Fin N) ℂ

def bump : ContDiffBump (0 : M) := ⟨2,3,by norm_num,by norm_num⟩
def cut (x : M) : M := bump x • x

lemma cut_smooth : ContDiff ℝ 1 (cut (N := N)) :=
  (bump.contDiff).smul contDiff_id

lemma cut_lipschitz : ∃ K, LipschitzWith K (cut (N := N)) := by
  have hc : HasCompactSupport (cut (N := N)) := bump.hasCompactSupport.smul_right
  exact cut_smooth.lipschitzWith_of_hasCompactSupport hc (by norm_num)

lemma cut_bound (x : M) : ‖cut x‖ ≤ 3 := by
  by_cases h : bump x = 0
  · simp [cut,h]
  · have hx : ‖x‖ < 3 := by
      have hm : x ∈ Function.support (bump (N := N)) := h
      rw [bump.support_eq] at hm
      simpa [bump,dist_eq_norm] using hm
    calc ‖cut x‖ = |bump x| * ‖x‖ := by simp [cut,norm_smul,Real.norm_eq_abs]
         _ ≤ 1 * 3 := mul_le_mul
           (by simpa only [abs_of_nonneg bump.nonneg] using (bump (N := N)).le_one (x := x))
           hx.le (norm_nonneg _) (by norm_num)
         _ = 3 := one_mul _

lemma one_bound : ‖(1 : M)‖ ≤ 1 := by
  cases subsingleton_or_nontrivial M with
  | inl h => simp [Subsingleton.elim (1 : M) 0]
  | inr h => simp

lemma cut_eq_of_unitary (x : M) (hx : x ∈ unitary M) : cut x = x := by
  have hn : ‖x‖ ≤ 1 := by
    have he : ‖x‖ = ‖(1 : M)‖ := by
      simpa only [mul_one] using (LinkConsistency.norm_umul (A := (1 : M)) hx)
    exact he.le.trans one_bound
  have hb : bump x = 1 := bump.one_of_mem_closedBall (by
    simpa [bump,dist_eq_norm] using hn.trans (by norm_num : (1:ℝ) ≤ 2))
  simp [cut,hb]

/-- A genuine solution on any prescribed finite time interval. The coefficient
need only be continuous, with no global bound and no time differentiability. -/
theorem exists_interval (B : ℝ → M) (hB : Continuous B)
    (hskew : ∀ t, star (B t) = -B t) (R : ℝ) (hR : 0 < R) :
    ∃ T : ℝ → M, T 0 = 1 ∧ ∀ t ∈ Ioo (-R) R,
      HasDerivAt T (T t * B t) t ∧ T t ∈ unitary M := by
  obtain ⟨m,hm⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hB.continuousOn
  let m' : ℝ≥0 := ⟨max m 0,le_max_right _ _⟩
  have hb (t : ℝ) (ht : t ∈ Icc (-R) R) : ‖B t‖ ≤ m' := (hm t ht).trans (le_max_left _ _)
  obtain ⟨K,hK⟩ := cut_lipschitz (N := N)
  let L : ℝ≥0 := 3*m'
  let a : ℝ≥0 := ⟨L*R+1,by positivity⟩
  have hp : IsPicardLindelof (fun (t : ℝ) (x : M) => cut x * B t)
      (tmin := -R) (tmax := R) (⟨0,by constructor <;> linarith⟩) 0 a 1 L (K*m') := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro x y
      calc dist (cut x * B t) (cut y * B t) = ‖(cut x-cut y)*B t‖ := by rw [dist_eq_norm,sub_mul]
           _ ≤ ‖cut x-cut y‖ * ‖B t‖ := norm_mul_le _ _
           _ ≤ (K*dist x y)*m' := mul_le_mul
             (by simpa only [dist_eq_norm] using hK.dist_le_mul x y) (hb t ht)
             (norm_nonneg _) (by positivity)
           _ = (↑(K*m'))*dist x y := by simp only [NNReal.coe_mul]; ring
    · intro x _
      exact (continuous_const.mul hB).continuousOn
    · intro t ht x _
      exact (norm_mul_le _ _).trans (mul_le_mul (cut_bound x) (hb t ht) (norm_nonneg _) (by norm_num))
    · change (L:ℝ)*max (R-0) (0- -R) ≤ (a:ℝ)-(1:ℝ≥0)
      simp only [sub_zero,sub_neg_eq_add,zero_add,max_self,NNReal.coe_one]
      change (L:ℝ)*R ≤ ((L:ℝ)*R+1)-1
      linarith
  obtain ⟨T,hT0,hTd⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (x := (1:M)) (by simpa only [mem_closedBall,dist_zero_right,NNReal.coe_one] using (one_bound : ‖(1:M)‖ ≤ 1))
  have hd (t : ℝ) (ht : t ∈ Ioo (-R) R) : HasDerivAt T (cut (T t)*B t) t :=
    (hTd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hw (t : ℝ) (ht : t ∈ Ioo (-R) R) : HasDerivAt (fun t => T t * star (T t)) 0 t := by
    have hh := (hd t ht).mul (hd t ht).star
    convert hh using 1
    simp only [cut,star_mul,star_smul,star_trivial,hskew,smul_mul_assoc,mul_smul_comm]
    rw [← smul_add]
    simp only [mul_neg,neg_mul,← mul_assoc,add_neg_cancel,smul_zero]
  have hu (t : ℝ) (ht : t ∈ Ioo (-R) R) : T t ∈ unitary M := by
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
      (fun s hs => (hw s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hw s hs).deriv) ht (show 0 ∈ Ioo (-R) R by constructor <;> linarith)
    simp only [hT0,star_one,mul_one] at hc
    exact Unitary.mem_iff.mpr ⟨mul_eq_one_comm.mp hc,hc⟩
  refine ⟨T,hT0,fun t ht => ⟨?_,hu t ht⟩⟩
  simpa only [cut_eq_of_unitary _ (hu t ht)] using hd t ht

/-- Unitary solutions with the same coefficient and initial identity agree. -/
lemma unique_interval {B : ℝ → M} (hskew : ∀ t, star (B t) = -B t)
    {R : ℝ} (hR : 0 < R) {T U : ℝ → M} (hT0 : T 0 = 1) (hU0 : U 0 = 1)
    (hT : ∀ t ∈ Ioo (-R) R, HasDerivAt T (T t*B t) t)
    (hU : ∀ t ∈ Ioo (-R) R, HasDerivAt U (U t*B t) t)
    (hunit : ∀ t ∈ Ioo (-R) R, U t ∈ unitary M) : EqOn T U (Ioo (-R) R) := by
  have hd (t : ℝ) (ht : t ∈ Ioo (-R) R) : HasDerivAt (fun t => T t*star (U t)) 0 t := by
    convert (hT t ht).mul (hU t ht).star using 1
    rw [star_mul,hskew]
    noncomm_ring
  intro t ht
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht (show 0 ∈ Ioo (-R) R by constructor <;> linarith)
  simp only [hT0,hU0,star_one,mul_one] at hc
  have hu := (Unitary.mem_iff.mp (hunit t ht)).1
  calc T t = T t*(star (U t)*U t) := by rw [hu,mul_one]
       _ = U t := by rw [← mul_assoc,hc,one_mul]

/-- Global parallel transport exists for every continuous skew-Hermitian matrix
coefficient. It starts at the identity and is unitary at every real time. -/
theorem exists_transport (B : ℝ → M) (hB : Continuous B)
    (hskew : ∀ t, star (B t) = -B t) :
    ∃ T : ℝ → M, T 0 = 1 ∧ (∀ t, HasDerivAt T (T t*B t) t) ∧ ∀ t, T t ∈ unitary M := by
  choose f hf0 hf using (fun R (hR : 0 < R) => exists_interval B hB hskew R hR)
  have agree (R S : ℝ) (hR : 0 < R) (hS : 0 < S) (t : ℝ)
      (htR : t ∈ Ioo (-R) R) (htS : t ∈ Ioo (-S) S) : f R hR t=f S hS t := by
    have hp : 0 < min R S := lt_min hR hS
    have subR : Ioo (-(min R S)) (min R S) ⊆ Ioo (-R) R :=
      Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
    have subS : Ioo (-(min R S)) (min R S) ⊆ Ioo (-S) S :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    apply unique_interval hskew hp (hf0 R hR) (hf0 S hS)
      (fun s hs => (hf R hR s (subR hs)).1)
      (fun s hs => (hf S hS s (subS hs)).1)
      (fun s hs => (hf S hS s (subS hs)).2)
    exact ⟨by
      rcases le_total R S with h | h
      · simpa only [min_eq_left h] using htR.1
      · simpa only [min_eq_right h] using htS.1,
      lt_min htR.2 htS.2⟩
  let T (t : ℝ) := f (|t|+1) (by positivity) t
  have mem (t : ℝ) : t ∈ Ioo (-(|t|+1)) (|t|+1) := by
    rw [mem_Ioo,← abs_lt]
    linarith
  refine ⟨T, hf0 _ _, fun t => ?_,fun t => (hf _ _ t (mem t)).2⟩
  have heq : T =ᶠ[𝓝 t] f (|t|+1) (by positivity) := by
    filter_upwards [Ioo_mem_nhds (mem t).1 (mem t).2] with s hs
    exact agree _ _ _ _ s (mem s) hs
  exact ((hf _ _ t (mem t)).1).congr_of_eventuallyEq heq

abbrev V := Fin 4 → ℝ

/-- One link family, constructed from the connection, solving every straight-edge
transport equation. No ODE-solution witness is an input. -/
theorem exists_connection_transport (A : V → V →L[ℝ] M) (hA : Continuous A)
    (hskew : ∀ y v, star (A y v) = -A y v) :
    ∃ T : V → V → ℝ → M, (∀ y v, T y v 0 = 1) ∧
      (∀ y v s, HasDerivAt (T y v) (T y v s*A (y+s • v) v) s) ∧
      ∀ y v s, T y v s ∈ unitary M := by
  have he (y v : V) := exists_transport (fun s : ℝ => A (y+s • v) v)
    (by fun_prop) (fun s => hskew (y+s • v) v)
  choose T h0 hd hu using he
  exact ⟨T,h0,hd,hu⟩

/-- Reversing an edge gives the adjoint link. This is derived from the transport
ODE and its uniqueness, rather than separately imposed on the connection links. -/
theorem connection_reciprocal {A : V → V →L[ℝ] M}
    (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → M) (h0 : ∀ y v, T y v 0=1)
    (hd : ∀ y v s, HasDerivAt (T y v) (T y v s*A (y+s • v) v) s)
    (hu : ∀ y v s, T y v s ∈ unitary M) (y v : V) (h : ℝ) :
    T (y+h • v) (-v) h=star (T y v h) := by
  let Q (s : ℝ) := star (T y v h)*T y v (h-s)
  have hQ0 : Q 0=1 := by
    simpa only [Q,sub_zero] using (Unitary.mem_iff.mp (hu y v h)).1
  have hQ (s : ℝ) : HasDerivAt Q (Q s*A ((y+h • v)+s • (-v)) (-v)) s := by
    have ht := (hd y v (h-s)).comp_const_sub h s
    have ht' := ht.const_mul (star (T y v h))
    have he : (y+h • v)+s • (-v)=y+(h-s) • v := by module
    convert ht' using 1
    simp only [Q,he,map_neg,mul_neg,mul_assoc]

  have hQu (s : ℝ) : Q s ∈ unitary M :=
    (unitary M).mul_mem (Unitary.star_mem (hu y v h)) (hu y v (h-s))
  have hR : 0 < |h|+1 := by positivity
  have he := unique_interval (fun s => hskew ((y+h • v)+s • (-v)) (-v)) hR
    (h0 (y+h • v) (-v)) hQ0 (fun s _ => hd (y+h • v) (-v) s)
    (fun s _ => hQ s) (fun s _ => hQu s)
    (show h ∈ Ioo (-(|h|+1)) (|h|+1) by rw [mem_Ioo,← abs_lt]; linarith)
  simpa only [Q,sub_self,h0,mul_one] using he

/-- Classical Yang–Mills site-action convergence for every supplied C² skew
connection, with transport existence and unitarity derived. This does not select
the connection or its link law from PM's microscopic update. -/
theorem exists_yang_mills_transport_c2 {A : V → V →L[ℝ] M} {S : Set V}
    (hSb : Bornology.IsBounded S) (hSm : MeasurableSet S)
    (hSf : MeasureTheory.volume (frontier S)=0) (hA : ContDiff ℝ 2 A)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    ∃ T : V → V → ℝ → M, (∀ y v, T y v 0=1) ∧
      (∀ y v s, HasDerivAt (T y v) (T y v s*A (y+s • v) v) s) ∧
      (∀ y v s, T y v s ∈ unitary M) ∧
      Tendsto (fun n => LatticeSiteAction.siteAction T β S n) atTop
        (𝓝 (∫ y in S, UniformGaugeAction.yangMillsDensity A (fderiv ℝ A) y β)) := by
  obtain ⟨T,h0,hd,hu⟩ := exists_connection_transport A hA.continuous hskew
  exact ⟨T,h0,hd,hu,ConnectionRegularity.d4_yang_mills_action_c2 hSb hSm hSf hA hskew T h0 hd β⟩

end PMAction.TransportExistence
