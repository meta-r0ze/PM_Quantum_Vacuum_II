import PMAction.UniformGaugeAction
import Mathlib.Analysis.BoxIntegral.Integrability

/-! Volume-weighted accumulation of the D₄ density on a finite box. Uniform
Taylor control and ordinary partition refinement give the Lebesgue action limit;
a pointwise limit alone would not suffice. No quantum measure or physical clock
is selected by this classical finite-region result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.IntegratedGaugeAction
open Set Filter Topology MeasureTheory BoxIntegral UniformGaugeAction VaryingFields
open scoped Matrix.Norms.L2Operator

/-- Positive quadrature weights accumulate error with total volume, not site count. -/
theorem weighted_error {ι : Type*} (s : Finset ι) (w f g : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (he : ∀ i ∈ s, |f i-g i| ≤ ε) :
    |(∑ i ∈ s, w i*f i)-(∑ i ∈ s, w i*g i)| ≤ ε*(∑ i ∈ s, w i) := by
  have hid : (∑ i ∈ s, w i*f i)-(∑ i ∈ s, w i*g i)=∑ i ∈ s, w i*(f i-g i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  calc
    _ ≤ ∑ i ∈ s, |w i*(f i-g i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i*ε := Finset.sum_le_sum fun i hi => by
      rw [abs_mul,abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (he i hi) (hw i hi)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A tagged finite-volume action, using actual cell volumes. -/
def sample (I : Box (Fin 4)) (f : V → ℝ) (π : TaggedPrepartition I) : ℝ :=
  ∑ J ∈ π.boxes, (volume : Measure V).real J * f (π.tag J)

lemma sample_eq_integralSum (I : Box (Fin 4)) (f : V → ℝ) (π : TaggedPrepartition I) :
    sample I f π=integralSum f (volume : Measure V).toBoxAdditive.toSMul π := by
  simp [sample,integralSum,BoxAdditiveMap.toSMul_apply,Measure.toBoxAdditive_apply,smul_eq_mul]

/-- Exact partition coverage fixes the total weight to the region's volume. -/
theorem sample_error (I : Box (Fin 4)) (π : TaggedPrepartition I) (hπ : π.IsPartition)
    (f g : V → ℝ) (ε : ℝ) (he : ∀ x ∈ I.Icc, |f x-g x| ≤ ε) :
    |sample I f π-sample I g π| ≤ ε*(volume : Measure V).real I := by
  have hw : (∑ J ∈ π.boxes, (volume : Measure V).real J)=(volume : Measure V).real I := by
    simpa only [Measure.toBoxAdditive_apply] using
      (volume : Measure V).toBoxAdditive.sum_partition_boxes (I := I) le_top hπ
  have h := weighted_error π.boxes (fun J => (volume : Measure V).real J)
    (fun J => f (π.tag J)) (fun J => g (π.tag J)) ε (fun _ _ => by positivity)
    (fun J _ => he _ (π.tag_mem_Icc J))
  simpa only [sample,hw] using h

/-- Stability of refined tagged actions. The sampled densities need not be
continuous or measurable between sample sites. Only the limiting density is
continuous; the quadrature limit is supplied by Mathlib's Riemann integral theorem. -/
theorem sampled_limit (I : Box (Fin 4)) (f : ℕ → V → ℝ) (g : V → ℝ) (hg : Continuous g)
    (π : ℕ → TaggedPrepartition I)
    (hπ : Tendsto π atTop (IntegrationParams.Riemann.toFilteriUnion I ⊤))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (he : ∀ᶠ r in atTop, ∀ x ∈ I.Icc, |f r x-g x| ≤ ε r) :
    Tendsto (fun r => sample I (f r) (π r)) atTop (𝓝 (∫ x in I, g x)) := by
  have hi := (hg.continuousOn.hasBoxIntegral (volume : Measure V) IntegrationParams.Riemann).tendsto.comp hπ
  have hq : Tendsto (fun r => sample I g (π r)) atTop (𝓝 (∫ x in I, g x)) := by
    simpa only [Function.comp_def,← sample_eq_integralSum] using hi
  have hp := hπ.eventually (IntegrationParams.eventually_isPartition IntegrationParams.Riemann I)
  have hb : ∀ᶠ r in atTop,
      ‖sample I (f r) (π r)-sample I g (π r)‖ ≤ ε r*(volume : Measure V).real I := by
    filter_upwards [hp,he] with r hr her
    rw [Real.norm_eq_abs]
    exact sample_error I (π r) hr (f r) g (ε r) her
  have hδ := squeeze_zero_norm' hb (by simpa using hε.mul_const ((volume : Measure V).real I))
  have hh := hq.add hδ
  convert hh using 1
  · funext r
    ring
  · simp

variable {N : ℕ}

theorem yang_mills_continuous (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ))
    (hA : Continuous A) (hDA : Continuous DA) (β : ℝ) :
    Continuous (fun x => yangMillsDensity A DA x β) := by
  unfold yangMillsDensity fieldStrength curvature
  fun_prop

/-- The actual midpoint D₄ density, accumulated with cell volumes on arbitrary
refining tagged partitions, converges to the classical Yang–Mills action on the
box. One common C¹,¹ bound over the region is retained explicitly. -/
theorem midpoint_sampled_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)}
    (I : Box (Fin 4)) (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x ∈ I.Icc, ∀ y, ‖y-x‖ ≤ 2 → ‖DA y-DA x‖ ≤ L*‖y-x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ)
    (π : ℕ → TaggedPrepartition I)
    (hπ : Tendsto π atTop (IntegrationParams.Riemann.toFilteriUnion I ⊤))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun r => sample I (fun x => d4Density A x β (h r)) (π r)) atTop
      (𝓝 (∫ x in I, yangMillsDensity A DA x β)) := by
  obtain ⟨C,hC,hb⟩ := yang_mills_uniform I.isCompact_Icc hA hDA hL0 hL hskew β
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hsmall := hh.eventually (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ)<1))
  have hε : Tendsto (fun r => C*h r) atTop (𝓝 0) := by
    simpa using (hh.mono_right nhdsWithin_le_nhds).const_mul C
  apply sampled_limit I _ _ (yang_mills_continuous A DA hAc hDA β) π hπ _ hε
  filter_upwards [hsmall] with r hr
  exact fun x hx => hb x hx (h r) hr.1 hr.2.le

end PMAction.IntegratedGaugeAction
