import PMAction.ClassicalYangMills

/-!
# Parallel-transport links are cubically consistent

`LinkConsistency.CubicConsistent` asks the links to be within `K h³` of the midpoint
exponentials of `A`. That is what it means for links to discretize `A`, and it holds whenever each
link is the parallel transport of `A` along its edge.

Parallel transport along `y → y + h v`: `T(0) = 1`, `T'(s) = T(s) B(s)` with `B(s) = A(y + s v) v`,
unitary for a `u(N)` connection. The midpoint link is `exp(h B_m)`, `B_m = B(h/2)`.

Proof: `W(s) = T(s) exp(−s B_m)` has `W' = T (B − B_m) exp(−s B_m)`. Since
`B(s) − B_m = (s − h/2) B' + O(h²)` and `∫₀ʰ (s − h/2) ds = 0`, subtracting the antiderivative of
the linear term leaves a derivative of size `O(h²)`, so `‖W(h) − 1‖ = O(h³)` by the mean value
inequality, and `T(h) − exp(h B_m) = (W(h) − 1) exp(h B_m)`.

* `transport_cubic`: the bound, with a constant depending only on bounds for `A`, `DA` near the
  edge and the Lipschitz constant of `DA`.
* `transport_consistent`: parallel-transport links are `CubicConsistent`.
* `pm_lattice_yang_mills_transport`: `ClassicalYangMills.pm_lattice_yang_mills` with the
  consistency hypothesis replaced by "the links are the parallel transports of `A`".
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ParallelTransport
open Matrix Set Filter Topology NormedSpace VaryingFields
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}
local notation "M" => Matrix (Fin N) (Fin N) ℂ

/-- **A unitary transport stays near the identity.** -/
theorem transport_near_one {T : ℝ → M} {B : ℝ → M} {MB : ℝ}
    (hT0 : T 0 = 1) (hTd : ∀ s, HasDerivAt T (T s * B s) s) (hTu : ∀ s, T s ∈ unitary M)
    (hB : ∀ t, 0 ≤ t → t ≤ 1 → ‖B t‖ ≤ MB) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖T s - 1‖ ≤ MB * s := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := T) (a := 0) (b := s)
    (fun t _ => (hTd t).hasDerivWithinAt)
    (fun t ht => by
      rw [LinkConsistency.norm_umul (hTu t)]
      exact hB t ht.1 (ht.2.le.trans hs1)) s ⟨hs0, le_rfl⟩
  rw [hT0, sub_zero] at h
  exact h

/-- **The exponential stays near the identity.** -/
theorem exp_near_one (Bm : M) {MB : ℝ} (hMB : 0 ≤ MB) (hB : ‖Bm‖ ≤ MB) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖exp (s • -Bm) - 1‖ ≤ s * (MB + MB ^ 2 / 2 + MB ^ 3 * Real.exp MB) := by
  set z : M := s • -Bm
  have hz : ‖z‖ ≤ s * MB := by
    simp only [z, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hB hs0
  have hz1 : ‖z‖ ≤ MB := hz.trans (by nlinarith)
  have h2 := exp_second z
  have e : exp z - 1 = (exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)) + z + (1 / 2 : ℝ) • z ^ 2 := by
    abel
  rw [e]
  have hz2 : ‖z ^ 2‖ ≤ ‖z‖ ^ 2 := norm_pow_le' z (by norm_num)
  have t1 : ‖exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)‖ ≤ s * (MB ^ 3 * Real.exp MB) := by
    refine h2.trans ?_
    have : ‖z‖ ^ 3 ≤ (s * MB) * MB ^ 2 := by
      calc ‖z‖ ^ 3 = ‖z‖ * ‖z‖ ^ 2 := by ring
        _ ≤ (s * MB) * MB ^ 2 := by gcongr
    calc ‖z‖ ^ 3 * Real.exp ‖z‖ ≤ ((s * MB) * MB ^ 2) * Real.exp MB := by gcongr
      _ = s * (MB ^ 3 * Real.exp MB) := by ring
  have t3 : ‖(1 / 2 : ℝ) • z ^ 2‖ ≤ s * (MB ^ 2 / 2) := by
    rw [norm_smul]
    have : ‖z‖ ^ 2 ≤ (s * MB) * MB := by
      calc ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := by ring
        _ ≤ (s * MB) * MB := by gcongr
    calc ‖(1 / 2 : ℝ)‖ * ‖z ^ 2‖ ≤ (1 / 2) * ((s * MB) * MB) := by
          rw [show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]; gcongr; exact hz2.trans this
      _ = s * (MB ^ 2 / 2) := by ring
  calc _ ≤ ‖exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2) + z‖ + ‖(1 / 2 : ℝ) • z ^ 2‖ := norm_add_le _ _
    _ ≤ ‖exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)‖ + ‖z‖ + ‖(1 / 2 : ℝ) • z ^ 2‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ s * (MB ^ 3 * Real.exp MB) + s * MB + s * (MB ^ 2 / 2) := by gcongr
    _ = _ := by ring

local notation "V4" => (Fin 4 → ℝ)

/-- The constant of the cubic bound. -/
def K (MA D L : ℝ) : ℝ :=
  (2 * MA) * (D + 8 * L) +
    (D + 8 * L) * ((2 * MA) + (2 * MA) ^ 2 / 2 + (2 * MA) ^ 3 * Real.exp (2 * MA)) + 8 * L

/-- **Taylor expansion of the transport generator about the midpoint.** -/
theorem generator_taylor {A : V4 → V4 →L[ℝ] M} {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] M)}
    (hA : ∀ y, HasFDerivAt A (DA y) y) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ z₁ z₂, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖) (y v : V4) (hv : ‖v‖ ≤ 2) (h : ℝ)
    (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ h) :
    ‖A (y + s • v) v - A (y + (h / 2) • v) v - (s - h / 2) • DA (y + (h / 2) • v) v v‖ ≤
      8 * L * h ^ 2 := by
  set x0 := y + (h / 2) • v
  have hv3 : ‖v‖ ^ 2 * ‖v‖ ≤ 8 := by
    have := norm_nonneg v
    nlinarith
  have hL : ∀ z, ‖DA z - DA x0‖ ≤ L * ‖z - x0‖ := fun z => hLip z x0
  rcases le_total (h / 2) s with hc | hc
  · have ht : 0 ≤ s - h / 2 := by linarith
    have e : y + s • v = x0 + (s - h / 2) • v := by simp only [x0, sub_smul]; abel
    have hb := taylor_apply (x := x0) (w := v) hA hL0 hL ht v
    rw [← e] at hb
    refine hb.trans ?_
    have : (s - h / 2) ^ 2 ≤ h ^ 2 := by nlinarith
    calc L * ‖v‖ ^ 2 * ‖v‖ * (s - h / 2) ^ 2 = L * (‖v‖ ^ 2 * ‖v‖) * (s - h / 2) ^ 2 := by ring
      _ ≤ L * 8 * h ^ 2 := by gcongr
      _ = 8 * L * h ^ 2 := by ring
  · have ht : 0 ≤ h / 2 - s := by linarith
    have e : y + s • v = x0 + (h / 2 - s) • -v := by
      simp only [x0, smul_neg, sub_smul]; abel
    have hb := taylor_apply (x := x0) (w := -v) hA hL0 hL ht v
    rw [← e, norm_neg] at hb
    have e2 : (h / 2 - s) • DA x0 (-v) v = (s - h / 2) • DA x0 v v := by
      rw [map_neg, _root_.neg_apply, smul_neg, ← neg_smul, neg_sub]
    rw [e2] at hb
    have hb' := hb
    refine hb'.trans ?_
    have : (h / 2 - s) ^ 2 ≤ h ^ 2 := by nlinarith
    calc L * ‖v‖ ^ 2 * ‖v‖ * (h / 2 - s) ^ 2 = L * (‖v‖ ^ 2 * ‖v‖) * (h / 2 - s) ^ 2 := by ring
      _ ≤ L * 8 * h ^ 2 := by gcongr
      _ = 8 * L * h ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- **Parallel transport is within `K h³` of the midpoint link.** -/
theorem transport_cubic {A : V4 → V4 →L[ℝ] M} {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] M)}
    (hA : ∀ y, HasFDerivAt A (DA y) y) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ z₁ z₂, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (y v : V4) (hv : ‖v‖ ≤ 2) {MA D : ℝ}
    (hMA : 0 ≤ MA) (hD : 0 ≤ D)
    (hAb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖A (y + t • v)‖ ≤ MA)
    (hDb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖DA (y + t • v) v v‖ ≤ D)
    (T : ℝ → M) (hT0 : T 0 = 1) (hTd : ∀ s, HasDerivAt T (T s * A (y + s • v) v) s)
    (hTu : ∀ s, T s ∈ unitary M) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    ‖T h - link A y v h‖ ≤ K MA D L * h ^ 3 := by
  set MB := 2 * MA
  set Δ := D + 8 * L
  set cE := MB + MB ^ 2 / 2 + MB ^ 3 * Real.exp MB
  have hMB : 0 ≤ MB := by positivity
  have hΔ : 0 ≤ Δ := by positivity
  have hcE : 0 ≤ cE := by positivity
  set B : ℝ → M := fun s => A (y + s • v) v
  set x0 := y + (h / 2) • v
  set Bm := A x0 v
  set Bc := DA x0 v v
  have hBb : ∀ t, 0 ≤ t → t ≤ 1 → ‖B t‖ ≤ MB := by
    intro t ht0 ht1
    calc ‖B t‖ ≤ ‖A (y + t • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ MA * 2 := mul_le_mul (hAb t ht0 ht1) hv (norm_nonneg _) hMA
      _ = MB := by ring
  have hBm : ‖Bm‖ ≤ MB := hBb (h / 2) (by positivity) (by linarith)
  have hBc : ‖Bc‖ ≤ D := hDb (h / 2) (by positivity) (by linarith)
  have htay : ∀ s, 0 ≤ s → s ≤ h → ‖B s - Bm - (s - h / 2) • Bc‖ ≤ 8 * L * h ^ 2 :=
    fun s hs0 hsh => generator_taylor hA hL0 hLip y v hv h s hs0 hsh
  have hdiff : ∀ s, 0 ≤ s → s ≤ h → ‖B s - Bm‖ ≤ Δ * h := by
    intro s hs0 hsh
    have habs : |s - h / 2| ≤ h := by rw [abs_le]; constructor <;> linarith
    have e : B s - Bm = (B s - Bm - (s - h / 2) • Bc) + (s - h / 2) • Bc := by abel
    rw [e]
    calc _ ≤ ‖B s - Bm - (s - h / 2) • Bc‖ + ‖(s - h / 2) • Bc‖ := norm_add_le _ _
      _ ≤ 8 * L * h ^ 2 + h * D := by
          gcongr
          · exact htay s hs0 hsh
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul habs hBc (norm_nonneg _) hh.le
      _ ≤ 8 * L * h + h * D := by gcongr; nlinarith
      _ = Δ * h := by ring
  -- the comparison function
  set E : ℝ → M := fun s => exp (s • -Bm)
  have hEu : ∀ s, E s ∈ unitary M := fun s => LinkConsistency.reverse_unitary hskew x0 v s
  have hEd : ∀ s, HasDerivAt E (E s * -Bm) s := fun s => hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Bm) s
  have hcomm : ∀ s, Commute Bm (E s) := fun s =>
    (((Commute.refl Bm).neg_right).smul_right s).exp_right
  set φ : ℝ → M := fun s => T s * E s - (s * s / 2 - s * h / 2) • Bc
  have hφd : ∀ s, HasDerivAt φ (T s * (B s - Bm) * E s - (s - h / 2) • Bc) s := by
    intro s
    have hW := (hTd s).mul (hEd s)
    have hq : HasDerivAt (fun s : ℝ => s * s / 2 - s * h / 2) (s - h / 2) s := by
      have h2 := (((hasDerivAt_id s).mul (hasDerivAt_id s)).div_const 2).sub
        (((hasDerivAt_id s).mul_const h).div_const 2)
      convert h2 using 1
      · funext x
        simp only [Pi.mul_apply, Pi.sub_apply, id]
      · simp only [id]
        ring
    have hP := hW.sub (hq.smul_const Bc)
    convert hP using 1
    have hc := (hcomm s).eq
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc, ← hc]
    abel
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) h,
      ‖T s * (B s - Bm) * E s - (s - h / 2) • Bc‖ ≤ K MA D L * h ^ 2 := by
    intro s hs
    have hs0 := hs.1
    have hsh := hs.2.le
    have hs1 : s ≤ 1 := hsh.trans h1
    have e : T s * (B s - Bm) * E s - (s - h / 2) • Bc =
        (T s - 1) * (B s - Bm) * E s + (B s - Bm) * (E s - 1) + (B s - Bm - (s - h / 2) • Bc) := by
      noncomm_ring
    rw [e]
    have hT1 := transport_near_one hT0 hTd hTu hBb s hs0 hs1
    have hE1 := exp_near_one Bm hMB hBm s hs0 hs1
    have t1 : ‖(T s - 1) * (B s - Bm) * E s‖ ≤ (MB * h) * (Δ * h) := by
      rw [LinkConsistency.norm_mulu (hEu s)]
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (hT1.trans (by gcongr)) (hdiff s hs0 hsh) (norm_nonneg _) (by positivity)
    have t2 : ‖(B s - Bm) * (E s - 1)‖ ≤ (Δ * h) * (h * cE) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (hdiff s hs0 hsh) (hE1.trans (by gcongr)) (norm_nonneg _) (by positivity)
    have t3 := htay s hs0 hsh
    calc _ ≤ ‖(T s - 1) * (B s - Bm) * E s + (B s - Bm) * (E s - 1)‖ +
          ‖B s - Bm - (s - h / 2) • Bc‖ := norm_add_le _ _
      _ ≤ ‖(T s - 1) * (B s - Bm) * E s‖ + ‖(B s - Bm) * (E s - 1)‖ +
          ‖B s - Bm - (s - h / 2) • Bc‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (MB * h) * (Δ * h) + (Δ * h) * (h * cE) + 8 * L * h ^ 2 := by gcongr
      _ = K MA D L * h ^ 2 := by simp only [K, MB, Δ, cE]; ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (a := 0) (b := h)
    (fun s _ => (hφd s).hasDerivWithinAt) hbound h ⟨hh.le, le_rfl⟩
  have hφ0 : φ 0 = 1 := by simp [φ, E, hT0]
  have hφh : φ h = T h * E h := by
    simp only [φ, show h * h / 2 - h * h / 2 = (0 : ℝ) by ring, zero_smul, sub_zero]
  rw [hφ0, hφh, sub_zero] at hmv
  -- back to the link
  have hlink : link A y v h = exp (h • Bm) := rfl
  have hinv : E h * exp (h • Bm) = 1 := by
    show exp (h • -Bm) * exp (h • Bm) = 1
    rw [← Matrix.exp_add_of_commute (h • -Bm) (h • Bm)
      (((Commute.refl Bm).neg_left.smul_left h).smul_right h)]
    simp [smul_neg]
  have e : T h - link A y v h = (T h * E h - 1) * exp (h • Bm) := by
    rw [hlink, Matrix.sub_mul, Matrix.mul_assoc, hinv, Matrix.mul_one, Matrix.one_mul]
  have hu : exp (h • Bm) ∈ unitary M := by
    rw [← hlink]; exact LinkConsistency.link_unitary hskew y v h
  rw [e, LinkConsistency.norm_mulu hu]
  calc ‖T h * E h - 1‖ ≤ K MA D L * h ^ 2 * h := hmv
    _ = K MA D L * h ^ 3 := by ring

/-- **Parallel-transport links are cubically consistent.** -/
theorem transport_consistent {A : V4 → V4 →L[ℝ] M} {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] M)}
    (hA : ∀ y, HasFDerivAt A (DA y) y) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ z₁ z₂, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (x : V4) {MA D : ℝ} (hMA : 0 ≤ MA) (hD : 0 ≤ D)
    (hAb : ∀ z, ‖z - x‖ ≤ 3 → ‖A z‖ ≤ MA)
    (hDb : ∀ z, ‖z - x‖ ≤ 3 → ∀ v : V4, ‖v‖ ≤ 2 → ‖DA z v v‖ ≤ D)
    (T : V4 → V4 → ℝ → M) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary M) :
    LinkConsistency.CubicConsistent T A x (K MA D L) := by
  intro y v h hh h1 hy hv
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖y + t • v - x‖ ≤ 3 := by
    intro t ht0 ht1
    have e : y + t • v - x = (y - x) + t • v := by abel
    rw [e]
    calc _ ≤ ‖y - x‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ 1 + 1 * 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          gcongr
      _ = 3 := by norm_num
  exact transport_cubic hA hL0 hLip hskew y v hv hMA hD
    (fun t ht0 ht1 => hAb _ (hseg t ht0 ht1)) (fun t ht0 ht1 => hDb _ (hseg t ht0 ht1) v hv)
    (T y v) (hT0 y v) (hTd y v) (hTu y v) h hh h1

/-- **The classical Yang–Mills limit for parallel-transport links.** PM's D₄ Wilson action built
from the parallel transports of a `C^{1,1}` `u(N)` connection converges, on any box, to the
Yang–Mills action. No consistency hypothesis remains. -/
theorem pm_lattice_yang_mills_transport {A : V4 → V4 →L[ℝ] M}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] M)} (I : BoxIntegral.Box (Fin 4))
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ z₁ z₂, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V4 → V4 → ℝ → M) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary M) (β : ℝ)
    (π : ℕ → BoxIntegral.TaggedPrepartition I)
    (hπ : Tendsto π atTop (BoxIntegral.IntegrationParams.Riemann.toFilteriUnion I ⊤))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun r => IntegratedGaugeAction.sample I
        (fun x => LinkConsistency.linkDensity T x β (h r)) (π r)) atTop
      (𝓝 (∫ x in I, UniformGaugeAction.yangMillsDensity A DA x β)) := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hK : IsCompact (Metric.cthickening 3 (BoxIntegral.Box.Icc I)) :=
    I.isCompact_Icc.cthickening
  obtain ⟨MA, hMA⟩ := hK.exists_bound_of_continuousOn hAc.continuousOn
  have hK2 : IsCompact (Metric.cthickening 3 (BoxIntegral.Box.Icc I) ×ˢ
      Metric.closedBall (0 : V4) 2) := hK.prod (isCompact_closedBall 0 2)
  have hDc : Continuous (fun p : V4 × V4 => DA p.1 p.2 p.2) := by fun_prop
  obtain ⟨MD, hMD⟩ := hK2.exists_bound_of_continuousOn hDc.continuousOn
  have hmem : ∀ x ∈ BoxIntegral.Box.Icc I, ∀ z, ‖z - x‖ ≤ 3 →
      z ∈ Metric.cthickening 3 (BoxIntegral.Box.Icc I) := fun x hx z hz =>
    Metric.mem_cthickening_of_dist_le z x 3 _ hx (by rw [dist_eq_norm]; exact hz)
  have hMA0 : 0 ≤ max MA 0 := le_max_right _ _
  have hMD0 : 0 ≤ max MD 0 := le_max_right _ _
  have hKpos : 0 ≤ K (max MA 0) (max MD 0) L := by unfold K; positivity
  refine ClassicalYangMills.pm_lattice_yang_mills I hA hDA hL0
    (fun x _ y => hLip y x) hskew T hTu hKpos (fun x hx => ?_) β π hπ h hh
  exact transport_consistent hA hL0 hLip hskew x hMA0 hMD0
    (fun z hz => (hMA z (hmem x hx z hz)).trans (le_max_left _ _))
    (fun z hz v hv => (hMD (z, v) ⟨hmem x hx z hz, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv⟩).trans (le_max_left _ _))
    T hT0 hTd hTu

end PMAction.ParallelTransport
