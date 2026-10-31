import PMAction.ReciprocalLinks

/-! The normalized reciprocal-link model. Product Haar is sampled on directed
inputs; the canonical orientation ignores one input in each reverse pair and sets
its physical link to the inverse of the other. The physical law is the pushforward
of the weighted input law. Gauge invariance and site-reflection positivity refer
to this same measure, with the original D₄ action evaluated on reciprocal links. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ReciprocalReflection
open Matrix MeasureTheory FiniteD4Reflection ReciprocalLinks
open D4ActionReflection (coordinates PlaneLinks UpperLinks)
open scoped ENNReal
variable {N : ℕ} {X : Finset Vertex}

abbrev Inputs (N : ℕ) (X : Finset Vertex) := ReciprocalLinks.Config N X
def reference (N : ℕ) (X : Finset Vertex) := Measure.pi fun _ : Edge X => UnitaryHaar.haar N
instance : IsProbabilityMeasure (reference N X) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi fun _ : Edge X => UnitaryHaar.haar N))
def cost (ω : Inputs N X) := action X (reciprocal ω)
def rawGibbs (N : ℕ) (X : Finset Vertex) (β : ℝ) := LatticeGibbs.gibbs (reference N X) β cost
def gibbs (N : ℕ) (X : Finset Vertex) (β : ℝ) := (rawGibbs N X β).map reciprocal

lemma cost_measurable : Measurable (cost (N := N) (X := X)) :=
  (action_measurable X).comp reciprocal_measurable

lemma raw_probability (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (rawGibbs N X β) := by
  apply LatticeGibbs.gibbs_isProbability _ hβ cost
  intro ω
  unfold cost
  rw [D4ActionReflection.action_eq]
  exact LatticeGibbs.action_bounds _ _ (D4ActionReflection.links_unitary X (reciprocal ω)) 1

lemma probability (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (gibbs N X β) := by
  have := raw_probability (N := N) (X := X) β hβ
  unfold gibbs
  infer_instance

lemma raw_gauge_preserving (g : Vertex → GeometricGauge.G N) (β : ℝ) :
    MeasurePreserving (GeometricGauge.act (X := X) g) (rawGibbs N X β) (rawGibbs N X β) := by
  apply GeometricGauge.gibbs_preserving_of_invariant (GeometricGauge.reference_preserving g)
    cost cost_measurable _ β
  intro ω
  simp only [cost,reciprocal_gauge,GeometricGauge.action_act]

/-- Local gauge invariance of the actual reciprocal-link probability law. -/
theorem gauge_preserving (g : Vertex → GeometricGauge.G N) (β : ℝ) :
    MeasurePreserving (GeometricGauge.act (X := X) g) (gibbs N X β) (gibbs N X β) := by
  refine ⟨GeometricGauge.act_measurable g,?_⟩
  unfold gibbs
  rw [Measure.map_map (GeometricGauge.act_measurable g) reciprocal_measurable]
  have he : (GeometricGauge.act g) ∘ reciprocal = reciprocal ∘ (GeometricGauge.act (X := X) g) :=
    funext fun ω => (reciprocal_gauge g ω).symm
  rw [he,← Measure.map_map reciprocal_measurable (GeometricGauge.act_measurable g),
    (raw_gauge_preserving g β).map_eq]

def half (hX : ∀ x ∈ X, reflect x ∈ X)
    (z : (PlaneLinks X → GeometricGauge.G N) × (UpperLinks X → GeometricGauge.G N)) : ℝ :=
  upperAction X (reciprocal ((coordinates hX).symm (z.1,(z.2,1))))

lemma half_measurable (hX : ∀ x ∈ X, reflect x ∈ X) : Measurable (half (N := N) hX) := by
  exact ((upperAction_measurable X).comp reciprocal_measurable).comp
    ((coordinates hX).symm.measurable.comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
lemma half_nonneg (hX : ∀ x ∈ X, reflect x ∈ X) (z) : 0 ≤ half (N := N) hX z :=
  upperAction_nonneg X _

lemma upper_eq_half (hX : ∀ x ∈ X, reflect x ∈ X) (ω : Inputs N X) :
    upperAction X (reciprocal ω)=half hX ((coordinates hX ω).1,(coordinates hX ω).2.1) := by
  let η := (coordinates hX).symm ((coordinates hX ω).1,((coordinates hX ω).2.1,1))
  have hs : coordinates hX η=((coordinates hX ω).1,((coordinates hX ω).2.1,1)) :=
    (coordinates hX).apply_symm_apply _
  apply upperAction_congr
  apply reciprocal_local
  apply FiniteReflection.agree_nonnegative (edgeReflection hX) (edgeReflection_involutive hX)
    height (height_reflect hX) (plane_fixed hX) ω η
  · change (coordinates hX ω).1=(coordinates hX η).1
    rw [hs]
  · change (coordinates hX ω).2.1=(coordinates hX η).2.1
    rw [hs]

lemma cost_split (hX : ∀ x ∈ X, reflect x ∈ X) (ω : Inputs N X) :
    cost ω=half hX ((coordinates hX ω).1,(coordinates hX ω).2.1)+
      half hX ((coordinates hX ω).1,(coordinates hX ω).2.2) := by
  unfold cost
  rw [action_split hX,upper_eq_half hX,← reciprocal_reflect hX,upper_eq_half hX]
  unfold coordinates
  rw [FiniteReflection.split_reflect]

/-- Reflection positivity of the weighted inputs for every upper input observable. -/
lemma raw_reflection_positive (hX : ∀ x ∈ X, reflect x ∈ X) (β : ℝ) (hβ : 0 ≤ β)
    (F : (PlaneLinks X → GeometricGauge.G N) × (UpperLinks X → GeometricGauge.G N) → ℂ)
    (hF : Measurable F) {B : ℝ} (hFb : ∀ z, ‖F z‖ ≤ B) :
    let z := ∫ ω, D4ActionReflection.observable hX F ω *
      starRingEnd ℂ (D4ActionReflection.observable hX F (fun e => ω (edgeReflection hX e)))
      ∂rawGibbs N X β
    z.im=0 ∧ 0 ≤ z.re := by
  have heq (ω : Inputs N X) : D4ActionReflection.observable hX F ω *
      starRingEnd ℂ (D4ActionReflection.observable hX F (fun e => ω (edgeReflection hX e))) *
      (Real.exp (-β*cost ω) : ℂ) =
      SiteReflection.integrand F (fun z => β*half hX z) (coordinates hX ω) := by
    rw [D4ActionReflection.observable_reflect,cost_split hX]
    simp only [D4ActionReflection.observable,SiteReflection.integrand,mul_add,neg_add,neg_mul]
  have hp : let z := ∫ ω, D4ActionReflection.observable hX F ω *
      starRingEnd ℂ (D4ActionReflection.observable hX F (fun e => ω (edgeReflection hX e))) *
      (Real.exp (-β*cost ω) : ℂ) ∂reference N X
      z.im=0 ∧ 0 ≤ z.re := by
    dsimp only
    simp_rw [heq]
    have hmp := shared_link_measure (UnitaryHaar.haar N) hX
    change MeasurePreserving (coordinates hX) (reference N X) _ at hmp
    rw [hmp.integral_comp']
    apply SiteReflection.reflection_positive _ _ F (fun z => β*half hX z) hF
      (measurable_const.mul (half_measurable hX)) hFb (M := 0)
    intro z
    simpa only [neg_zero] using mul_nonneg hβ (half_nonneg hX z)
  dsimp only
  rw [rawGibbs,D4ActionReflection.gibbs_integral _ β cost cost_measurable]
  constructor
  · simp only [Complex.smul_im,smul_eq_mul,hp.1,mul_zero]
  · simpa only [Complex.smul_re,smul_eq_mul] using mul_nonneg ENNReal.toReal_nonneg hp.2

/-- Upper observables depend only on nonnegative-height geometric edges. -/
def UpperObservable (F : Inputs N X → ℂ) : Prop :=
  ∀ ω η, (∀ e, 0 ≤ height e → ω e=η e) → F ω=F η

/-- Site-reflection positivity on the physical reciprocal-link measure itself. -/
theorem reflection_positive (hX : ∀ x ∈ X, reflect x ∈ X) (β : ℝ) (hβ : 0 ≤ β)
    (F : Inputs N X → ℂ) (hF : Measurable F) (hUpper : UpperObservable F)
    {B : ℝ} (hFb : ∀ ω, ‖F ω‖ ≤ B) :
    let z := ∫ ω, F ω * starRingEnd ℂ (F (fun e => ω (edgeReflection hX e))) ∂gibbs N X β
    z.im=0 ∧ 0 ≤ z.re := by
  let FF (z : (PlaneLinks X → GeometricGauge.G N) × (UpperLinks X → GeometricGauge.G N)) :=
    F (reciprocal ((coordinates hX).symm (z.1,(z.2,1))))
  have hFF : Measurable FF := (hF.comp reciprocal_measurable).comp
    ((coordinates hX).symm.measurable.comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  have heq (ω : Inputs N X) : F (reciprocal ω)=D4ActionReflection.observable hX FF ω := by
    apply hUpper
    apply reciprocal_local
    let η := (coordinates hX).symm ((coordinates hX ω).1,((coordinates hX ω).2.1,1))
    have hs : coordinates hX η=((coordinates hX ω).1,((coordinates hX ω).2.1,1)) :=
      (coordinates hX).apply_symm_apply _
    apply FiniteReflection.agree_nonnegative (edgeReflection hX) (edgeReflection_involutive hX)
      height (height_reflect hX) (plane_fixed hX) ω η
    · change (coordinates hX ω).1=(coordinates hX η).1
      rw [hs]
    · change (coordinates hX ω).2.1=(coordinates hX η).2.1
      rw [hs]
  have hθ : Measurable (fun ω : Inputs N X => fun e => ω (edgeReflection hX e)) :=
    Measurable.of_eval fun e => measurable_pi_apply _
  have hInt : Measurable (fun ω : Inputs N X =>
      F ω * starRingEnd ℂ (F (fun e => ω (edgeReflection hX e)))) := by fun_prop
  dsimp only
  unfold gibbs
  rw [integral_map reciprocal_measurable.aemeasurable hInt.aestronglyMeasurable]
  simp_rw [← reciprocal_reflect hX,heq]
  exact raw_reflection_positive hX β hβ FF hFF (fun z => hFb _)

end PMAction.ReciprocalReflection
