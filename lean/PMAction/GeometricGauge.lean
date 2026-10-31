import PMAction.D4ActionReflection
import PMAction.GaugeInvariance
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Local gauge transformations act on the actual finite geometric directed
link space, not on an arbitrary edge-identification quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.GeometricGauge
open Matrix MeasureTheory FiniteD4Reflection
open scoped ENNReal
set_option maxHeartbeats 300000
variable {N : ℕ} {X : Finset Vertex}
abbrev G (N : ℕ) : Type := UnitaryHaar.UN N
abbrev Config (N : ℕ) (X : Finset Vertex) := Edge X → G N

/-- Right invariance follows from uniqueness of normalized Haar, since right
translation preserves left invariance and probability. -/
instance haar_right : (UnitaryHaar.haar N).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : IsProbabilityMeasure ((UnitaryHaar.haar N).map (· * g)) := inferInstance
    have : (UnitaryHaar.haar N).IsHaarMeasure := by
      unfold UnitaryHaar.haar
      infer_instance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

def act (g : Vertex → G N) (ω : Config N X) : Config N X :=
  fun e => g e.1.1 * ω e * (g e.1.2)⁻¹

lemma act_one (ω : Config N X) : act 1 ω = ω := by funext e; simp [act]
lemma act_mul (g h : Vertex → G N) (ω : Config N X) : act (g*h) ω=act g (act h ω) := by
  funext e
  simp [act,mul_assoc]

lemma act_measurable (g : Vertex → G N) : Measurable (act (X := X) g) := by
  apply Measurable.of_eval
  intro e
  exact (measurable_mul_const _).comp ((measurable_const_mul _).comp (measurable_pi_apply e))

/-- Every site gauge assignment gives a measurable bijection of configurations. -/
def equivalence (g : Vertex → G N) : Config N X ≃ᵐ Config N X where
  toFun := act g
  invFun := act g⁻¹
  left_inv ω := by rw [← act_mul]; simpa using act_one ω
  right_inv ω := by rw [← act_mul]; simpa using act_one ω
  measurable_toFun := act_measurable g
  measurable_invFun := act_measurable g⁻¹

lemma triangle_act (g : Vertex → G N) (ω : Config N X) (c : Cell X) :
    act g ω (edgeSlot c 0) * act g ω (edgeSlot c 1) * (act g ω (edgeSlot c 2))⁻¹ =
      g (cellVertex c 0) * (ω (edgeSlot c 0) * ω (edgeSlot c 1) * (ω (edgeSlot c 2))⁻¹) *
        (g (cellVertex c 0))⁻¹ := by
  change (g (cellVertex c 0)*ω (edgeSlot c 0)*(g (cellVertex c 1))⁻¹) *
    (g (cellVertex c 1)*ω (edgeSlot c 1)*(g (cellVertex c 2))⁻¹) *
    (g (cellVertex c 0)*ω (edgeSlot c 2)*(g (cellVertex c 2))⁻¹)⁻¹ = _
  group

lemma term_act (g : Vertex → G N) (ω : Config N X) (c : Cell X) : term c (act g ω)=term c ω := by
  have ht := congrArg (fun u : G N => (trace (1-(u : Matrix (Fin N) (Fin N) ℂ))).re)
    (triangle_act g ω c)
  have hinv (u : G N) : (↑(u⁻¹) : Matrix (Fin N) (Fin N) ℂ) = (u : Matrix (Fin N) (Fin N) ℂ)ᴴ := rfl
  simp only [Submonoid.coe_mul,hinv] at ht
  change term c (act g ω)=term c ω
  rw [term,ht]
  unfold term
  have hu : (g (cellVertex c 0) : Matrix (Fin N) (Fin N) ℂ)ᴴ *
      (g (cellVertex c 0) : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp (g (cellVertex c 0)).2).1
  rw [trace_sub,trace_sub,mul_assoc,trace_mul_comm,mul_assoc,hu,mul_one]

lemma action_act (g : Vertex → G N) (ω : Config N X) : action X (act g ω)=action X ω := by
  unfold action
  simp only [term_act]

/-- The geometric gauge action preserves the product Haar reference law. -/
theorem reference_preserving (g : Vertex → G N) :
    MeasurePreserving (act (X := X) g) (Measure.pi fun _ : Edge X => UnitaryHaar.haar N)
      (Measure.pi fun _ : Edge X => UnitaryHaar.haar N) := by
  have he (e : Edge X) : MeasurePreserving
      (fun u : G N => g e.1.1*u*(g e.1.2)⁻¹) (UnitaryHaar.haar N) (UnitaryHaar.haar N) :=
    (measurePreserving_mul_right (UnitaryHaar.haar N) (g e.1.2)⁻¹).comp
      (measurePreserving_mul_left (UnitaryHaar.haar N) (g e.1.1))
  exact measurePreserving_pi (fun _ : Edge X => UnitaryHaar.haar N)
    (fun _ : Edge X => UnitaryHaar.haar N) he

/-- An invariant measurable density preserves every measure-preserving map. -/
lemma weighted_preserving {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → Ω}
    (hf : MeasurePreserving f μ μ) (w : Ω → ℝ≥0∞) (hw : Measurable w)
    (hinv : ∀ x, w (f x)=w x) : MeasurePreserving f (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hf.measurable,?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs,withDensity_apply _ (hf.measurable hs),withDensity_apply _ hs]
  simpa only [hinv] using hf.setLIntegral_comp_preimage hs hw

/-- Invariance survives normalization of an invariant Gibbs density. -/
lemma gibbs_preserving_of_invariant {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → Ω} (hf : MeasurePreserving f μ μ) (S : Ω → ℝ)
    (hS : Measurable S) (hinv : ∀ x, S (f x)=S x) (β : ℝ) :
    MeasurePreserving f (LatticeGibbs.gibbs μ β S) (LatticeGibbs.gibbs μ β S) := by
  have hw : Measurable (LatticeGibbs.weight β S) := by
    unfold LatticeGibbs.weight
    fun_prop
  have hp := weighted_preserving hf (LatticeGibbs.weight β S) hw
    (fun ω => by simp only [LatticeGibbs.weight,hinv])
  refine ⟨hp.measurable,?_⟩
  unfold LatticeGibbs.gibbs
  rw [Measure.map_smul _ hp.measurable.aemeasurable,hp.map_eq]

/-- Gauge invariance of the normalized finite geometric-link Gibbs measure. -/
theorem gibbs_preserving (g : Vertex → G N) (β : ℝ) :
    MeasurePreserving (act (X := X) g)
      (LatticeGibbs.gibbs (Measure.pi fun _ : Edge X => UnitaryHaar.haar N) β (action X))
      (LatticeGibbs.gibbs (Measure.pi fun _ : Edge X => UnitaryHaar.haar N) β (action X)) :=
  gibbs_preserving_of_invariant (reference_preserving g) (action X)
    (action_measurable X) (action_act g) β

/-- The configuration action realizes the local gauge law on every geometric edge. -/
lemma edge_realization (g : Vertex → G N) (ω : Config N X) (e : Edge X) :
    D4ActionReflection.edgeValue X (act g ω) (D4ActionReflection.realVertex e.1.1)
      (D4ActionReflection.realVertex e.1.2) =
      (g e.1.1 : Matrix (Fin N) (Fin N) ℂ)*(ω e : Matrix (Fin N) (Fin N) ℂ)*
        (g e.1.2 : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
  rw [D4ActionReflection.edgeValue_edge]
  rfl

end PMAction.GeometricGauge
