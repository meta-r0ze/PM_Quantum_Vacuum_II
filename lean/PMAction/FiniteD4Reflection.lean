import PMAction.D4Reflection
import PMAction.FiniteReflection
import PMAction.UnitaryHaar
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! Finite geometric shared-edge indexing for a reflection-symmetric D₄ region.
The finite halo contains every vertex used by the region's based triangles.
Edges are geometric ordered nearest-neighbour pairs, not independent copies for
each triangle. This module concerns the directed-link convention of the current
finite action; a reciprocal orientation convention must be identified separately. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.FiniteD4Reflection
open D4Gauge
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma triangle_difference : ∀ p ∈ tri, ∃ k ∈ roots, ∀ i,
    vec k i=vec p.2 i-vec p.1 i := by
  have hraw : ∀ (a b : Fin 4 → Fin 3), dot (vec a) (vec a)=2 → dot (vec b) (vec b)=2 →
      dot (vec a) (vec b)=1 → ∃ k : Fin 4 → Fin 3,
        dot (vec k) (vec k)=2 ∧ ∀ i, vec k i=vec b i-vec a i := by decide +kernel
  intro p hp
  have hp' := hp
  simp only [tri,Finset.mem_filter,Finset.mem_product] at hp'
  have ha := hp'.1.1
  have hb := hp'.1.2
  simp only [roots,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
  obtain ⟨k,hk,he⟩ := hraw p.1 p.2 ha hb hp'.2
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩,he⟩

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Vertex := Fin 4 → ℤ

def reflect (x : Vertex) : Vertex := fun i => if i=0 then -x i else x i

theorem reflect_involutive : Function.Involutive reflect := by
  intro x
  funext i
  by_cases h : i=0 <;> simp [reflect,h]

lemma reflect_add (x y : Vertex) : reflect (x+y)=reflect x+reflect y := by
  funext i
  by_cases h : i=0 <;> simp [reflect,h,add_comm]

def rootVector (k : Fin 4 → Fin 3) : Vertex := vec k

lemma reflect_root (k : Fin 4 → Fin 3) : reflect (rootVector k)=rootVector (D4Reflection.θ k) := by
  funext i
  simpa [reflect,rootVector] using (D4Reflection.vec_reflect k i).symm

/-- One finite vertex halo, with no wrapping or identification of boundary links. -/
def halo (X : Finset Vertex) : Finset Vertex :=
  X ∪ X.biUnion (fun x => roots.image (fun k => x+rootVector k))

lemma halo_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) :
    ∀ x ∈ halo X, reflect x ∈ halo X := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union.mpr (Or.inl (hX x hx))
  · obtain ⟨y,hy,hm⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨reflect y,hX y hy,Finset.mem_image.mpr ⟨D4Reflection.θ k,D4Reflection.reflect_root k hk,?_⟩⟩
    rw [reflect_add,reflect_root]

/-- The actual geometric nearest-neighbour edges of the finite halo. -/
def edges (X : Finset Vertex) : Finset (Vertex × Vertex) :=
  (halo X ×ˢ halo X).filter (fun e => ∃ k ∈ roots, e.2=e.1+rootVector k)

abbrev Edge (X : Finset Vertex) := ↥(edges X)

lemma edges_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X)
    (e : Vertex × Vertex) (he : e ∈ edges X) : (reflect e.1,reflect e.2) ∈ edges X := by
  obtain ⟨he, k,hk,hr⟩ := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨halo_reflect hX _ (Finset.mem_product.mp he).1,
    halo_reflect hX _ (Finset.mem_product.mp he).2⟩,D4Reflection.θ k,D4Reflection.reflect_root k hk,?_⟩
  rw [hr,reflect_add,reflect_root]

def edgeReflection {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) : Edge X ≃ Edge X where
  toFun e := ⟨(reflect e.1.1,reflect e.1.2),edges_reflect hX e.1 e.2⟩
  invFun e := ⟨(reflect e.1.1,reflect e.1.2),edges_reflect hX e.1 e.2⟩
  left_inv e := Subtype.ext (Prod.ext (reflect_involutive e.1.1) (reflect_involutive e.1.2))
  right_inv e := Subtype.ext (Prod.ext (reflect_involutive e.1.1) (reflect_involutive e.1.2))

theorem edgeReflection_involutive {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) :
    Function.Involutive (edgeReflection hX) := fun e =>
  Subtype.ext (Prod.ext (reflect_involutive e.1.1) (reflect_involutive e.1.2))

/-- Signed height classifies plane, upper and lower links. -/
def height {X : Finset Vertex} (e : Edge X) : ℤ := e.1.1 0+e.1.2 0

theorem height_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (e : Edge X) :
    height (edgeReflection hX e) = -height e := by
  simp [height,edgeReflection,reflect,add_comm]

/-- A height-zero D₄ link has both endpoints in the plane, and is pointwise
fixed by the site reflection. There are no hidden crossing links in this class. -/
theorem plane_fixed {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X)
    (e : Edge X) (h0 : height e=0) : edgeReflection hX e=e := by
  obtain ⟨_,k,hk,hr⟩ := Finset.mem_filter.mp e.2
  have hv := congrFun hr 0
  have hb := D4Reflection.coord_range k hk
  have hz : e.1.1 0=0 ∧ e.1.2 0=0 := by
    dsimp [height] at h0
    simp only [Pi.add_apply,rootVector] at hv
    omega
  apply Subtype.ext
  apply Prod.ext <;> funext i <;> by_cases hi : i=0 <;>
    simp [edgeReflection,reflect,hi,hz.1,hz.2]

/-- Product measure on the region's shared links really factors into plane,
upper and reflected-upper measures. Haar is an instance of this general theorem. -/
theorem shared_link_measure {G : Type*} [MeasurableSpace G] (ν : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure ν] {X : Finset Vertex}
    (hX : ∀ x ∈ X, reflect x ∈ X) :
    MeasureTheory.MeasurePreserving
      (FiniteReflection.split (G := G) (edgeReflection hX) (edgeReflection_involutive hX)
        height (height_reflect hX) (plane_fixed hX))
      (MeasureTheory.Measure.pi fun _ : Edge X => ν)
      ((MeasureTheory.Measure.pi fun _ : FiniteReflection.Plane (@height X) => ν).prod
        ((MeasureTheory.Measure.pi fun _ : FiniteReflection.Upper (@height X) => ν).prod
          (MeasureTheory.Measure.pi fun _ : FiniteReflection.Upper (@height X) => ν))) :=
  FiniteReflection.measure_preserving ν _ _ _ _ _

abbrev Cell (X : Finset Vertex) := ↥X × ↥tri

def cellVertex {X : Finset Vertex} (c : Cell X) : Fin 3 → Vertex :=
  ![c.1.1,c.1.1+rootVector c.2.1.1,c.1.1+rootVector c.2.1.2]

lemma cell_roots {X : Finset Vertex} (c : Cell X) :
    c.2.1.1 ∈ roots ∧ c.2.1.2 ∈ roots := by
  have hp := c.2.2
  simp only [tri,Finset.mem_filter,Finset.mem_product] at hp
  exact hp.1

lemma cellVertex_mem {X : Finset Vertex} (c : Cell X) (i : Fin 3) : cellVertex c i ∈ halo X := by
  fin_cases i
  · exact Finset.mem_union.mpr (Or.inl c.1.2)
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨c.1.1,c.1.2,Finset.mem_image.mpr ⟨c.2.1.1,(cell_roots c).1,rfl⟩⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨c.1.1,c.1.2,Finset.mem_image.mpr ⟨c.2.1.2,(cell_roots c).2,rfl⟩⟩))

def edgePair {X : Finset Vertex} (c : Cell X) : Fin 3 → Vertex × Vertex :=
  ![(cellVertex c 0,cellVertex c 1),(cellVertex c 1,cellVertex c 2),(cellVertex c 0,cellVertex c 2)]

lemma edgePair_mem {X : Finset Vertex} (c : Cell X) (i : Fin 3) : edgePair c i ∈ edges X := by
  apply Finset.mem_filter.mpr
  constructor
  · fin_cases i
    · exact Finset.mem_product.mpr ⟨cellVertex_mem c 0,cellVertex_mem c 1⟩
    · exact Finset.mem_product.mpr ⟨cellVertex_mem c 1,cellVertex_mem c 2⟩
    · exact Finset.mem_product.mpr ⟨cellVertex_mem c 0,cellVertex_mem c 2⟩
  · fin_cases i
    · exact ⟨c.2.1.1,(cell_roots c).1,rfl⟩
    · obtain ⟨k,hk,hd⟩ := triangle_difference c.2.1 c.2.2
      refine ⟨k,hk,?_⟩
      funext j
      change c.1.1 j+vec c.2.1.2 j=(c.1.1 j+vec c.2.1.1 j)+vec k j
      rw [hd]
      ring
    · exact ⟨c.2.1.2,(cell_roots c).2,rfl⟩

def edgeSlot {X : Finset Vertex} (c : Cell X) (i : Fin 3) : Edge X := ⟨edgePair c i,edgePair_mem c i⟩

def reflectCell {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (c : Cell X) : Cell X :=
  (⟨reflect c.1.1,hX _ c.1.2⟩,⟨(D4Reflection.θ c.2.1.1,D4Reflection.θ c.2.1.2),
    D4Reflection.reflect_tri c.2.1 c.2.2⟩)

lemma reflectCell_involutive {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) :
    Function.Involutive (reflectCell hX) := by
  intro c
  apply Prod.ext
  · exact Subtype.ext (reflect_involutive c.1.1)
  · apply Subtype.ext
    apply Prod.ext <;> funext i <;> by_cases hi : i=0 <;> simp [reflectCell,D4Reflection.θ,hi]

def cellReflection {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) : Cell X ≃ Cell X :=
  Function.Involutive.toPerm (reflectCell hX) (reflectCell_involutive hX)

lemma cellVertex_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (c : Cell X) (i : Fin 3) :
    cellVertex (reflectCell hX c) i=reflect (cellVertex c i) := by
  fin_cases i <;> simp [cellVertex,reflectCell,reflect_add,reflect_root]

lemma edgeSlot_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (c : Cell X) (i : Fin 3) :
    edgeSlot (reflectCell hX c) i=edgeReflection hX (edgeSlot c i) := by
  apply Subtype.ext
  fin_cases i <;> simp [edgeSlot,edgePair,edgeReflection,cellVertex_reflect]

def level {X : Finset Vertex} (c : Cell X) : ℤ := cellVertex c 0 0+cellVertex c 1 0+cellVertex c 2 0

lemma level_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (c : Cell X) :
    level (reflectCell hX c) = -level c := by
  simp [level,cellVertex_reflect,reflect,add_comm,add_assoc]

/-- Positive triangles get full weight, plane triangles half, and negative zero. -/
def halfWeight (z : ℤ) : ℝ := if 0<z then 1 else if z=0 then 1/2 else 0

lemma weight_reflect (z : ℤ) : halfWeight z+halfWeight (-z)=1 := by
  unfold halfWeight
  by_cases h : 0<z
  · rw [ite_eq_left h,ite_eq_right (show ¬0 < -z by omega),ite_eq_right (show -z ≠ 0 by omega)]
    norm_num
  · rw [ite_eq_right h]
    by_cases hz : z=0
    · subst z; norm_num
    · rw [ite_eq_right hz,ite_eq_left (show 0 < -z by omega)]
      norm_num

lemma weight_nonneg (z : ℤ) : 0 ≤ halfWeight z := by
  unfold halfWeight
  split_ifs <;> norm_num

lemma active_vertices {X : Finset Vertex} (c : Cell X) (hc : halfWeight (level c) ≠ 0) :
    0 ≤ cellVertex c 0 0 ∧ 0 ≤ cellVertex c 1 0 ∧ 0 ≤ cellVertex c 2 0 := by
  have hl : 0 ≤ level c := by
    by_contra hn
    have : level c<0 := by omega
    apply hc
    simp [halfWeight,show ¬0<level c by omega,show level c ≠ 0 by omega]
  have hs := D4Reflection.one_side (c.1.1 0) c.2.1 c.2.2
  change (0 ≤ cellVertex c 0 0 ∧ 0 ≤ cellVertex c 1 0 ∧ 0 ≤ cellVertex c 2 0) ∨
    (cellVertex c 0 0 ≤ 0 ∧ cellVertex c 1 0 ≤ 0 ∧ cellVertex c 2 0 ≤ 0) at hs
  rcases hs with hs | hs
  · exact hs
  · dsimp [level] at hl
    omega

lemma active_edges {X : Finset Vertex} (c : Cell X) (hc : halfWeight (level c) ≠ 0) (i : Fin 3) :
    0 ≤ height (edgeSlot c i) := by
  have hv := active_vertices c hc
  fin_cases i <;> dsimp [height,edgeSlot,edgePair] <;> omega

open Matrix
local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))
variable {n : ℕ}

/-- The Wilson term reads shared geometric edges, including the adjoint closing edge. -/
def term {X : Finset Vertex} (c : Cell X) (ω : Edge X → UnitaryHaar.UN n) : ℝ :=
  (Matrix.trace (1-((ω (edgeSlot c 0) : Matrix (Fin n) (Fin n) ℂ)*
    (ω (edgeSlot c 1) : Matrix (Fin n) (Fin n) ℂ)*(ω (edgeSlot c 2) : Matrix (Fin n) (Fin n) ℂ)ᴴ))).re

lemma term_reflect {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X) (c : Cell X)
    (ω : Edge X → UnitaryHaar.UN n) :
    term (reflectCell hX c) ω=term c (fun e => ω (edgeReflection hX e)) := by
  simp only [term,edgeSlot_reflect]

def action (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) : ℝ := ∑ c : Cell X, term c ω

def upperAction (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) : ℝ :=
  ∑ c : Cell X, halfWeight (level c)*term c ω

/-- The full shared-link action is exactly the two reflected half-actions. -/
theorem action_split {X : Finset Vertex} (hX : ∀ x ∈ X, reflect x ∈ X)
    (ω : Edge X → UnitaryHaar.UN n) :
    action X ω=upperAction X ω+upperAction X (fun e => ω (edgeReflection hX e)) := by
  have hθ (e : Edge X) : edgeReflection hX (edgeReflection hX e)=e := edgeReflection_involutive hX e
  have he : upperAction X (fun e => ω (edgeReflection hX e)) =
      ∑ c : Cell X, halfWeight (-level c)*term c ω := by
    unfold upperAction
    rw [← Equiv.sum_comp (cellReflection hX)]
    apply Finset.sum_congr rfl
    intro c _
    change halfWeight (level (reflectCell hX c))*term (reflectCell hX c)
      (fun e => ω (edgeReflection hX e))=halfWeight (-level c)*term c ω
    rw [level_reflect,term_reflect]
    simp only [hθ]
  rw [he,upperAction,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← add_mul,weight_reflect,one_mul]

/-- The half-action only reads plane and upper links. This is an actual support
statement for the shared Wilson terms, not a hypothesis that the action splits. -/
theorem upperAction_congr {X : Finset Vertex} (ω η : Edge X → UnitaryHaar.UN n)
    (h : ∀ e, 0 ≤ height e → ω e=η e) : upperAction X ω=upperAction X η := by
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : halfWeight (level c)=0
  · simp [hc]
  · have he (i : Fin 3) : ω (edgeSlot c i)=η (edgeSlot c i) := h _ (active_edges c hc i)
    simp only [term,he]

theorem term_bounds {X : Finset Vertex} (c : Cell X) (ω : Edge X → UnitaryHaar.UN n) :
    0 ≤ term c ω ∧ term c ω ≤ 2*(n : ℝ) :=
  LatticeGibbs.wilson_bounds _ ((unitary _).mul_mem
    ((unitary _).mul_mem (ω (edgeSlot c 0)).2 (ω (edgeSlot c 1)).2)
    (Unitary.star_mem (ω (edgeSlot c 2)).2))

@[fun_prop]
theorem term_measurable {X : Finset Vertex} (c : Cell X) :
    Measurable (term (n := n) c) := by
  have hv (i : Fin 3) : Measurable (fun ω : Edge X → UnitaryHaar.UN n =>
      (ω (edgeSlot c i) : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_subtype_val.measurable.comp (measurable_pi_apply _)
  have hm : Measurable (fun ω : Edge X → UnitaryHaar.UN n =>
      (1 : Matrix (Fin n) (Fin n) ℂ) -
        (ω (edgeSlot c 0) : Matrix (Fin n) (Fin n) ℂ) *
        (ω (edgeSlot c 1) : Matrix (Fin n) (Fin n) ℂ) *
        (ω (edgeSlot c 2) : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by fun_prop
  have ht : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => A.trace.re) :=
    (Complex.continuous_re.comp continuous_id.matrix_trace).measurable
  exact ht.comp hm

theorem upperAction_measurable (X : Finset Vertex) : Measurable (upperAction (n := n) X) := by
  unfold upperAction
  fun_prop

theorem action_measurable (X : Finset Vertex) : Measurable (action (n := n) X) := by
  unfold action
  fun_prop

theorem upperAction_nonneg (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) :
    0 ≤ upperAction X ω :=
  Finset.sum_nonneg fun c _ => mul_nonneg (weight_nonneg _) (term_bounds c ω).1

end PMAction.FiniteD4Reflection
