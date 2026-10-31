import PMAction.GeometricGauge

/-! Reciprocal links on the same finite geometric edges. A reflection-invariant
spatial orientation chooses one variable per unoriented edge; its reverse is the
inverse. Unused reverse-input variables are ignored, never identified arbitrarily. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ReciprocalLinks
open Matrix MeasureTheory FiniteD4Reflection D4Gauge
variable {N : ℕ} {X : Finset Vertex}

set_option maxHeartbeats 1000000 in
lemma root_reverse : ∀ k : Fin 4 → Fin 3, dot (vec k) (vec k)=2 →
    dot (vec (fun i => Fin.rev (k i))) (vec (fun i => Fin.rev (k i)))=2 ∧
    ∀ i, vec (fun i => Fin.rev (k i)) i = -vec k i := by decide +kernel

lemma root_score : ∀ k : Fin 4 → Fin 3, dot (vec k) (vec k)=2 →
    vec k 1+3*vec k 2+9*vec k 3 ≠ 0 := by decide +kernel

def reverseEdge (e : Edge X) : Edge X := by
  refine ⟨(e.1.2,e.1.1),?_⟩
  obtain ⟨hp,k,hk,he⟩ := Finset.mem_filter.mp e.2
  have hroot := hk
  simp only [roots,Finset.mem_filter,Finset.mem_univ,true_and] at hroot
  obtain ⟨hneg,hn⟩ := root_reverse k hroot
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2,(Finset.mem_product.mp hp).1⟩,
    fun i => Fin.rev (k i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hneg⟩,?_⟩
  funext i
  have hi := congrFun he i
  change e.1.1 i=e.1.2 i+vec (fun i => Fin.rev (k i)) i
  rw [hn]
  change e.1.2 i=e.1.1 i+vec k i at hi
  linarith

lemma reverse_involutive (e : Edge X) : reverseEdge (reverseEdge e)=e := Subtype.ext rfl
lemma reverse_height (e : Edge X) : height (reverseEdge e)=height e := by
  simp [height,reverseEdge,add_comm]
lemma reverse_reflect (hX : ∀ x ∈ X, reflect x ∈ X) (e : Edge X) :
    reverseEdge (edgeReflection hX e)=edgeReflection hX (reverseEdge e) := Subtype.ext rfl

def score (x : Vertex) : ℤ := x 1+3*x 2+9*x 3
def positive (e : Edge X) : Prop := 0 < score e.1.2-score e.1.1
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma score_ne (e : Edge X) : score e.1.2-score e.1.1 ≠ 0 := by
  obtain ⟨_,k,hk,he⟩ := Finset.mem_filter.mp e.2
  have hr := hk
  simp only [roots,Finset.mem_filter,Finset.mem_univ,true_and] at hr
  have hn := root_score k hr
  rw [he]
  simp only [score,Pi.add_apply,rootVector]
  intro hz
  apply hn
  linarith

lemma positive_reverse (e : Edge X) : positive (reverseEdge e) ↔ ¬positive e := by
  have hn := score_ne e
  change (0 < score e.1.1-score e.1.2) ↔ ¬(0 < score e.1.2-score e.1.1)
  omega
lemma positive_reflect (hX : ∀ x ∈ X, reflect x ∈ X) (e : Edge X) :
    positive (edgeReflection hX e) ↔ positive e := by
  simp [positive,score,edgeReflection,reflect]

abbrev Config (N : ℕ) (X : Finset Vertex) := GeometricGauge.Config N X

def reciprocal (ω : Config N X) : Config N X :=
  fun e => if positive e then ω e else (ω (reverseEdge e))⁻¹

lemma reciprocal_reverse (ω : Config N X) (e : Edge X) :
    reciprocal ω (reverseEdge e)=(reciprocal ω e)⁻¹ := by
  by_cases h : positive e <;> simp [reciprocal,positive_reverse,reverse_involutive,h]

lemma reciprocal_idempotent (ω : Config N X) : reciprocal (reciprocal ω)=reciprocal ω := by
  funext e
  by_cases h : positive e
  · simp [reciprocal,h]
  · rw [reciprocal,ite_eq_right h,reciprocal_reverse,inv_inv]

lemma reciprocal_measurable : Measurable (reciprocal (N := N) (X := X)) := by
  apply Measurable.of_eval
  intro e
  by_cases h : positive e
  · simpa only [reciprocal,ite_eq_left h] using (measurable_pi_apply e : Measurable (fun ω : Config N X => ω e))
  · simp only [reciprocal,ite_eq_right h]
    exact (measurable_pi_apply (reverseEdge e) : Measurable (fun ω : Config N X => ω (reverseEdge e))).inv


lemma reciprocal_local (ω η : Config N X)
    (h : ∀ e, 0 ≤ height e → ω e=η e) :
    ∀ e, 0 ≤ height e → reciprocal ω e=reciprocal η e := by
  intro e he
  by_cases hp : positive e
  · simp only [reciprocal,ite_eq_left hp,h e he]
  · simp only [reciprocal,ite_eq_right hp,h (reverseEdge e) (by simpa only [reverse_height] using he)]

lemma reciprocal_reflect (hX : ∀ x ∈ X, reflect x ∈ X) (ω : Config N X) :
    reciprocal (fun e => ω (edgeReflection hX e))=
      fun e => reciprocal ω (edgeReflection hX e) := by
  funext e
  simp only [reciprocal,positive_reflect,reverse_reflect]

lemma reciprocal_gauge (g : Vertex → GeometricGauge.G N) (ω : Config N X) :
    reciprocal (GeometricGauge.act g ω)=GeometricGauge.act g (reciprocal ω) := by
  funext e
  by_cases h : positive e
  · simp [reciprocal,GeometricGauge.act,h]
  · simp only [reciprocal,ite_eq_right h,GeometricGauge.act]
    change (g e.1.2*ω (reverseEdge e)*(g e.1.1)⁻¹)⁻¹ =
      g e.1.1*(ω (reverseEdge e))⁻¹*(g e.1.2)⁻¹
    group

end PMAction.ReciprocalLinks
