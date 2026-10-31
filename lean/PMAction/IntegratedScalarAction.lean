import PMAction.ScalarTransport
import PMAction.IntegratedGaugeAction

/-! Compact-region control and the integrated limit of the event-priced scalar action.
`ScalarTransport.scalar_limit` is pointwise. Here the per-root constants are explicit
(`ScalarTransport.covBound`) and continuous in the base point, so compactness gives one
constant on a region, and volume-weighted tagged sums converge to the integral of
`(3/4)·toll·m·Σ_μ ‖(∂_μ + A_μ)Φ‖²`. Classical, finite-region result: no potential, quantum
measure or physical clock is selected. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.IntegratedScalarAction
open Matrix Set Filter Topology MeasureTheory BoxIntegral VaryingFields ScalarTransport
  ReferenceSampling
open LinkConsistency (CubicConsistent rv_norm)
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- The continuum scalar density. -/
def scalarTarget (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (x : V) (toll : ℝ) (m : ℕ) : ℝ :=
  3 / 4 * (toll * m) * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2

/-- The per-root constant. -/
def rootBound (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (x : V) (L LΦ K : ℝ) (k : Fin 4 → Fin 3) : ℝ :=
  N * (covBound A DA Φ DΦ x L LΦ K (rv k) *
    (2 * ‖covD A Φ DΦ x (rv k)‖ + covBound A DA Φ DΦ x L LΦ K (rv k)))

/-- **Explicit pointwise bound.** -/
theorem scalar_bound {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hK : 0 ≤ K) (hc : CubicConsistent U A x K)
    (toll : ℝ) (m : ℕ) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    |scalarDensity U Φ x toll m h - scalarTarget A Φ DΦ x toll m| ≤
      (|toll * m| / 16 * ∑ k ∈ D4Gauge.roots, rootBound A DA Φ DΦ x L LΦ K k) * h := by
  have hroot : ∀ k : Fin 4 → Fin 3,
      |(∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
        ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2| ≤ rootBound A DA Φ DΦ x L LΦ K k * h := by
    intro k
    obtain ⟨hC, hb⟩ := covariant_expand_explicit hA hL0 hL hΦ hLΦ0 hLΦ (rv k)
      (fun h => U x (rv k) h) hK
      (fun h hh h1 => hc x (rv k) h hh h1 (by simp) ((rv_norm k).trans (by norm_num)))
    set C := covBound A DA Φ DΦ x L LΦ K (rv k)
    have hent : ∀ i, |‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2 / h ^ 2 -
        ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2| ≤ C * (2 * ‖covD A Φ DΦ x (rv k)‖ + C) * h := by
      intro i
      have hi : ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0 -
          h • covD A Φ DΦ x (rv k) i 0‖ ≤ C * h ^ 2 := by
        have := entry_le' ((U x (rv k) h * Φ (x + h • rv k) - Φ x) -
          h • covD A Φ DΦ x (rv k)) i 0
        simp only [Matrix.sub_apply, Matrix.smul_apply] at this
        exact this.trans (hb h hh h1)
      refine (quadratic_close hh h1 hC hi).trans ?_
      gcongr
      exact entry_le' _ i 0
    have e2 : (∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
        ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2 =
        ∑ i, (‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2 / h ^ 2 -
          ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    rw [e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hent i).trans ?_
    simp only [rootBound, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, C]
    apply le_of_eq
    ring
  have hmom : (∑ k ∈ D4Gauge.roots, ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) =
      12 * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2 := by
    simp only [covD_expand A Φ DΦ x (rv _)]
    rw [Finset.sum_comm]
    simp only [complex_moment, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  set T := toll * m
  have e : scalarDensity U Φ x toll m h - scalarTarget A Φ DΦ x toll m =
      (T / 16) * ∑ k ∈ D4Gauge.roots,
        ((∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
          ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) := by
    have hA1 : scalarDensity U Φ x toll m h = T / 16 * ∑ k ∈ D4Gauge.roots,
        (∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 := by
      rw [scalarDensity, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [T]; ring
    have hA2 : scalarTarget A Φ DΦ x toll m =
        T / 16 * ∑ k ∈ D4Gauge.roots, ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2 := by
      rw [scalarTarget, hmom]; ring
    rw [hA1, hA2, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [e, abs_mul, show |T / 16| = |T| / 16 by rw [abs_div]; norm_num]
  have hs : |∑ k ∈ D4Gauge.roots,
      ((∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
        ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2)| ≤
      (∑ k ∈ D4Gauge.roots, rootBound A DA Φ DΦ x L LΦ K k) * h := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hroot k)
  calc |T| / 16 * |_| ≤ |T| / 16 * ((∑ k ∈ D4Gauge.roots, rootBound A DA Φ DΦ x L LΦ K k) * h) := by
        gcongr
    _ = _ := by ring

theorem rootBound_continuous (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (hA : Continuous A) (hDA : Continuous DA) (hΦ : Continuous Φ)
    (hDΦ : Continuous DΦ) (L LΦ K : ℝ) (k : Fin 4 → Fin 3) :
    Continuous (fun x => rootBound A DA Φ DΦ x L LΦ K k) := by
  unfold rootBound covBound linkBound covD
  fun_prop

/-- **Uniform control on a compact region.** A common `C^{1,1}` bound for the connection and the
field, and a common cubic-consistency constant, are retained; compactness supplies one constant. -/
theorem scalar_uniform {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V} (hs : IsCompact s)
    {L K : ℝ} (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ s, ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hDΦ : Continuous DΦ) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ x ∈ s, ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hK : 0 ≤ K)
    (hc : ∀ x ∈ s, CubicConsistent U A x K) (toll : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |scalarDensity U Φ x toll m h - scalarTarget A Φ DΦ x toll m| ≤ C * h := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun x => (hΦ x).continuousAt
  have hcont : Continuous (fun x =>
      |toll * m| / 16 * ∑ k ∈ D4Gauge.roots, rootBound A DA Φ DΦ x L LΦ K k) :=
    continuous_const.mul (continuous_finsetSum _ fun k _ =>
      rootBound_continuous A DA Φ DΦ hAc hDA hΦc hDΦ L LΦ K k)
  obtain ⟨B, hB⟩ := hs.bddAbove_image hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx h hh h1 => ?_⟩
  have hb := scalar_bound hA hL0 (hL x hx) hΦ hLΦ0 (hLΦ x hx) U hK (hc x hx) toll m h hh h1
  exact hb.trans (mul_le_mul_of_nonneg_right
    ((hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)) hh.le)

theorem scalarTarget_continuous (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (hA : Continuous A) (hΦ : Continuous Φ) (hDΦ : Continuous DΦ)
    (toll : ℝ) (m : ℕ) : Continuous (fun x => scalarTarget A Φ DΦ x toll m) := by
  unfold scalarTarget covD
  fun_prop

/-- **The integrated scalar action.** The event-priced scalar density, accumulated with cell
volumes on refining tagged partitions of a box, converges to
`∫ (3/4)·toll·m·Σ_μ ‖(∂_μ + A_μ)Φ‖²` over the box. -/
theorem scalar_sampled_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} (I : Box (Fin 4))
    {L K : ℝ} (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ I.Icc, ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hDΦ : Continuous DΦ) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ x ∈ I.Icc, ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hK : 0 ≤ K)
    (hc : ∀ x ∈ I.Icc, CubicConsistent U A x K) (toll : ℝ) (m : ℕ)
    (π : ℕ → TaggedPrepartition I)
    (hπ : Tendsto π atTop (IntegrationParams.Riemann.toFilteriUnion I ⊤))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun r => IntegratedGaugeAction.sample I
        (fun x => scalarDensity U Φ x toll m (h r)) (π r)) atTop
      (𝓝 (∫ x in I, scalarTarget A Φ DΦ x toll m)) := by
  obtain ⟨C, hC, hb⟩ := scalar_uniform I.isCompact_Icc hA hDA hL0 hL hΦ hDΦ hLΦ0 hLΦ U hK hc toll m
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun x => (hΦ x).continuousAt
  have hsmall := hh.eventually (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
  have hε : Tendsto (fun r => C * h r) atTop (𝓝 0) := by
    simpa using (hh.mono_right nhdsWithin_le_nhds).const_mul C
  apply IntegratedGaugeAction.sampled_limit I _ _
    (scalarTarget_continuous A Φ DΦ hAc hΦc hDΦ toll m) π hπ _ hε
  filter_upwards [hsmall] with r hr
  exact fun x hx => hb x hx (h r) hr.1 hr.2.le

end PMAction.IntegratedScalarAction
