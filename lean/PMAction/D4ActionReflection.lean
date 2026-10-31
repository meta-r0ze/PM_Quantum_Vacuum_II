import PMAction.FiniteD4Reflection

/-! Identification of the finite shared-edge Wilson action with the current
`LatticeGibbs.action`, at unit lattice spacing. Off-lattice link values are a
unitary extension used only to match that API; every action term reads the
explicit geometric edge. No link law is derived from a microscopic PM update. -/
noncomputable section
namespace PMAction.D4ActionReflection
open Matrix FiniteD4Reflection
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped Matrix.Norms.L2Operator

abbrev V := Fin 4 → ℝ
variable {n : ℕ}

def realVertex (x : Vertex) : V := fun i => (x i : ℝ)
def floorVertex (y : V) : Vertex := fun i => ⌊y i⌋

lemma floor_real (x : Vertex) : floorVertex (realVertex x)=x := by
  funext i
  simp [floorVertex,realVertex]

lemma realVertex_injective : Function.Injective realVertex := by
  intro x y h
  funext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

lemma realVertex_add_root (x : Vertex) (k : Fin 4 → Fin 3) :
    realVertex (x+rootVector k)=realVertex x+VaryingFields.rv k := by
  funext i
  simp [realVertex,rootVector,VaryingFields.rv]

def edgeValue (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) (x y : V) :
    Matrix (Fin n) (Fin n) ℂ :=
  if h : (floorVertex x,floorVertex y) ∈ edges X then
    (ω ⟨(floorVertex x,floorVertex y),h⟩ : Matrix (Fin n) (Fin n) ℂ) else 1

def links (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) (y v : V) (h : ℝ) :=
  edgeValue X ω y (y+h • v)

lemma edgeValue_edge (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) (e : Edge X) :
    edgeValue X ω (realVertex e.1.1) (realVertex e.1.2)=(ω e : Matrix (Fin n) (Fin n) ℂ) := by
  simp [edgeValue,floor_real,e.2]

theorem links_unitary (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) (y v : V) (h : ℝ) :
    links X ω y v h ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  unfold links edgeValue
  split_ifs with he
  · exact (ω ⟨_,he⟩).2
  · exact (unitary _).one_mem

lemma first_link {X : Finset Vertex} (ω : Edge X → UnitaryHaar.UN n) (c : Cell X) :
    links X ω (realVertex c.1.1) (VaryingFields.rv c.2.1.1) 1=
      (ω (edgeSlot c 0) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold links
  rw [one_smul,← realVertex_add_root]
  exact edgeValue_edge X ω (edgeSlot c 0)

lemma last_link {X : Finset Vertex} (ω : Edge X → UnitaryHaar.UN n) (c : Cell X) :
    links X ω (realVertex c.1.1) (VaryingFields.rv c.2.1.2) 1=
      (ω (edgeSlot c 2) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold links
  rw [one_smul,← realVertex_add_root]
  exact edgeValue_edge X ω (edgeSlot c 2)

lemma middle_link {X : Finset Vertex} (ω : Edge X → UnitaryHaar.UN n) (c : Cell X) :
    links X ω (realVertex c.1.1+VaryingFields.rv c.2.1.1)
      (VaryingFields.rv c.2.1.2-VaryingFields.rv c.2.1.1) 1=
      (ω (edgeSlot c 1) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold links
  rw [one_smul,show realVertex c.1.1+VaryingFields.rv c.2.1.1+
      (VaryingFields.rv c.2.1.2-VaryingFields.rv c.2.1.1)=
      realVertex c.1.1+VaryingFields.rv c.2.1.2 by abel,
    ← realVertex_add_root,← realVertex_add_root]
  exact edgeValue_edge X ω (edgeSlot c 1)

lemma term_eq_holonomy {X : Finset Vertex} (ω : Edge X → UnitaryHaar.UN n) (c : Cell X) :
    term c ω=(trace (1-LinkConsistency.holonomy (links X ω) (realVertex c.1.1)
      (VaryingFields.rv c.2.1.1) (VaryingFields.rv c.2.1.2) 1)).re := by
  simp only [LinkConsistency.holonomy,one_smul,first_link,middle_link,last_link,term]

/-- Exact equality to the pre-existing finite D₄ action, not a replacement by
independent per-triangle variables or a newly posited split action. -/
theorem action_eq (X : Finset Vertex) (ω : Edge X → UnitaryHaar.UN n) :
    action X ω=LatticeGibbs.action (X.image realVertex) (links X ω) 1 := by
  rw [LatticeGibbs.action,Finset.sum_image (g := realVertex) (by
    intro x hx y hy h; exact realVertex_injective h)]
  simp only [action,Fintype.sum_prod_type,term_eq_holonomy]
  let f (x : Vertex) (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) : ℝ :=
    (trace (1-LinkConsistency.holonomy (links X ω) (realVertex x)
      (VaryingFields.rv p.1) (VaryingFields.rv p.2) 1)).re
  change (∑ x : ↥X, ∑ p : ↥D4Gauge.tri, f x.1 p.1) =
    ∑ x ∈ X, ∑ p ∈ D4Gauge.tri, f x p
  have hs (x : Vertex) : (∑ p : ↥D4Gauge.tri, f x p.1) = ∑ p ∈ D4Gauge.tri, f x p :=
    Finset.sum_coe_sort D4Gauge.tri (f x)
  simp_rw [hs]
  exact Finset.sum_coe_sort X (fun x => ∑ p ∈ D4Gauge.tri, f x p)

end PMAction.D4ActionReflection

namespace PMAction.D4ActionReflection
open Matrix MeasureTheory FiniteD4Reflection
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {n : ℕ} {X : Finset Vertex}

abbrev PlaneLinks (X : Finset Vertex) := FiniteReflection.Plane (@height X)
abbrev UpperLinks (X : Finset Vertex) := FiniteReflection.Upper (@height X)
abbrev Group (n : ℕ) := UnitaryHaar.UN n

def coordinates (hX : ∀ x ∈ X, reflect x ∈ X) :=
  FiniteReflection.split (G := Group n) (edgeReflection hX) (edgeReflection_involutive hX)
    height (height_reflect hX) (plane_fixed hX)

/-- Fill unused lower links with the identity to define an upper-half function.
The support theorem below proves that this filler has no effect on the half-action. -/
def halfAction (hX : ∀ x ∈ X, reflect x ∈ X)
    (z : (PlaneLinks X → Group n) × (UpperLinks X → Group n)) : ℝ :=
  upperAction X ((coordinates hX).symm (z.1,(z.2,1)))

theorem halfAction_measurable (hX : ∀ x ∈ X, reflect x ∈ X) :
    Measurable (halfAction (n := n) hX) := by
  apply (upperAction_measurable X).comp
  exact (coordinates hX).symm.measurable.comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

theorem halfAction_nonneg (hX : ∀ x ∈ X, reflect x ∈ X)
    (z : (PlaneLinks X → Group n) × (UpperLinks X → Group n)) : 0 ≤ halfAction hX z :=
  upperAction_nonneg X _

lemma upper_eq_half (hX : ∀ x ∈ X, reflect x ∈ X) (ω : Edge X → Group n) :
    upperAction X ω=halfAction hX ((coordinates hX ω).1,(coordinates hX ω).2.1) := by
  let η := (coordinates hX).symm ((coordinates hX ω).1,((coordinates hX ω).2.1,1))
  have hs : coordinates hX η=((coordinates hX ω).1,((coordinates hX ω).2.1,1)) :=
    (coordinates hX).apply_symm_apply _
  apply upperAction_congr
  apply FiniteReflection.agree_nonnegative (edgeReflection hX) (edgeReflection_involutive hX)
    height (height_reflect hX) (plane_fixed hX) ω η
  · change (coordinates hX ω).1=(coordinates hX η).1
    rw [hs]
  · change (coordinates hX ω).2.1=(coordinates hX η).2.1
    rw [hs]

/-- The actual shared-edge Wilson action in its product coordinates is exactly
A(p,u)+A(p,d). Plane triangles have been shared by half, not dropped or doubled. -/
theorem action_factor (hX : ∀ x ∈ X, reflect x ∈ X) (ω : Edge X → Group n) :
    action X ω=halfAction hX ((coordinates hX ω).1,(coordinates hX ω).2.1)+
      halfAction hX ((coordinates hX ω).1,(coordinates hX ω).2.2) := by
  rw [action_split hX,upper_eq_half hX,upper_eq_half hX]
  have hs := FiniteReflection.split_reflect (edgeReflection hX) (edgeReflection_involutive hX)
    height (height_reflect hX) (plane_fixed hX) ω
  rw [show coordinates hX (fun e => ω (edgeReflection hX e))=
    ((coordinates hX ω).1,((coordinates hX ω).2.2,(coordinates hX ω).2.1)) from hs]

/-- An upper observable, pulled back to the finite shared-edge configuration. -/
def observable (hX : ∀ x ∈ X, reflect x ∈ X)
    (F : (PlaneLinks X → Group n) × (UpperLinks X → Group n) → ℂ) (ω : Edge X → Group n) : ℂ :=
  F ((coordinates hX ω).1,(coordinates hX ω).2.1)

lemma observable_reflect (hX : ∀ x ∈ X, reflect x ∈ X)
    (F : (PlaneLinks X → Group n) × (UpperLinks X → Group n) → ℂ) (ω : Edge X → Group n) :
    observable hX F (fun e => ω (edgeReflection hX e))=F ((coordinates hX ω).1,(coordinates hX ω).2.2) := by
  unfold observable coordinates
  rw [FiniteReflection.split_reflect]

/-- Site-reflection identity for the finite geometric D₄ action with product
Haar on shared directed links. This closes the action and measure bridge to the
abstract Fubini theorem. Physical Euclidean/update identification is separate. -/
theorem reflection_identity (hX : ∀ x ∈ X, reflect x ∈ X) (β : ℝ) (hβ : 0 ≤ β)
    (F : (PlaneLinks X → Group n) × (UpperLinks X → Group n) → ℂ) (hF : Measurable F)
    {B : ℝ} (hFb : ∀ z, ‖F z‖ ≤ B) :
    (∫ ω, observable hX F ω * starRingEnd ℂ (observable hX F (fun e => ω (edgeReflection hX e))) *
      (Real.exp (-β*action X ω) : ℂ) ∂(Measure.pi fun _ : Edge X => UnitaryHaar.haar n)) =
      ((∫ p, Complex.normSq (SiteReflection.G (Measure.pi fun _ : UpperLinks X => UnitaryHaar.haar n)
        F (fun z => β*halfAction hX z) p) ∂(Measure.pi fun _ : PlaneLinks X => UnitaryHaar.haar n) : ℝ) : ℂ) := by
  have heq (ω : Edge X → Group n) :
      observable hX F ω * starRingEnd ℂ (observable hX F (fun e => ω (edgeReflection hX e))) *
        (Real.exp (-β*action X ω) : ℂ) =
      SiteReflection.integrand F (fun z => β*halfAction hX z) (coordinates hX ω) := by
    rw [observable_reflect,action_factor hX]
    simp only [observable,SiteReflection.integrand,mul_add,neg_add,neg_mul]
  simp_rw [heq]
  have hmp := shared_link_measure (UnitaryHaar.haar n) hX
  change MeasurePreserving (coordinates hX) _ _ at hmp
  rw [hmp.integral_comp']
  apply SiteReflection.reflection_identity _ _ F (fun z => β*halfAction hX z) hF
    (measurable_const.mul (halfAction_measurable hX)) hFb (M := 0)
  intro z
  simpa only [neg_zero] using mul_nonneg hβ (halfAction_nonneg hX z)

/-- The finite D₄ Osterwalder–Schrader form is real and nonnegative. -/
theorem reflection_positive (hX : ∀ x ∈ X, reflect x ∈ X) (β : ℝ) (hβ : 0 ≤ β)
    (F : (PlaneLinks X → Group n) × (UpperLinks X → Group n) → ℂ) (hF : Measurable F)
    {B : ℝ} (hFb : ∀ z, ‖F z‖ ≤ B) :
    let z := ∫ ω, observable hX F ω * starRingEnd ℂ (observable hX F (fun e => ω (edgeReflection hX e))) *
      (Real.exp (-β*action X ω) : ℂ) ∂(Measure.pi fun _ : Edge X => UnitaryHaar.haar n)
    z.im=0 ∧ 0 ≤ z.re := by
  dsimp only
  rw [reflection_identity hX β hβ F hF hFb,Complex.ofReal_im,Complex.ofReal_re]
  exact ⟨rfl,integral_nonneg fun p => Complex.normSq_nonneg _⟩

end PMAction.D4ActionReflection

namespace PMAction.D4ActionReflection
open Matrix MeasureTheory FiniteD4Reflection
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bochner expectations in the existing Gibbs measure have the usual density
and partition-function factor; measurability of the action is explicit. -/
lemma gibbs_integral {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (β : ℝ)
    (S : Ω → ℝ) (hS : Measurable S) (f : Ω → ℂ) :
    (∫ ω, f ω ∂LatticeGibbs.gibbs ν β S)=
      ((LatticeGibbs.Z ν β S)⁻¹).toReal •
        (∫ ω, f ω*(Real.exp (-β*S ω) : ℂ) ∂ν) := by
  rw [LatticeGibbs.gibbs,integral_smul_measure]
  congr 1
  have hw : Measurable (LatticeGibbs.weight β S) := by
    unfold LatticeGibbs.weight
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    simp [LatticeGibbs.weight,Complex.real_smul,Real.exp_nonneg,mul_comm]

variable {n : ℕ} {X : Finset Vertex}

/-- Probability normalization for the same explicit geometric-link model. -/
theorem gibbs_probability (X : Finset Vertex) (β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (LatticeGibbs.gibbs (Measure.pi fun _ : Edge X => UnitaryHaar.haar n) β
      (fun ω => LatticeGibbs.action (X.image realVertex) (links X ω) 1)) :=
  LatticeGibbs.gibbs_isProbability _ hβ _
    (fun ω => LatticeGibbs.action_bounds _ _ (links_unitary X ω) 1)

/-- Reflection positivity for the normalized finite Gibbs measure of the
pre-existing D₄ triangle action, with explicit shared geometric directed links.
This is a finite-spacing site-reflection theorem, not a transfer-matrix or
continuum/mass-gap construction. -/
theorem gibbs_reflection_positive (hX : ∀ x ∈ X, reflect x ∈ X) (β : ℝ) (hβ : 0 ≤ β)
    (F : (PlaneLinks X → Group n) × (UpperLinks X → Group n) → ℂ) (hF : Measurable F)
    {B : ℝ} (hFb : ∀ z, ‖F z‖ ≤ B) :
    let z := ∫ ω, observable hX F ω * starRingEnd ℂ (observable hX F (fun e => ω (edgeReflection hX e)))
      ∂LatticeGibbs.gibbs (Measure.pi fun _ : Edge X => UnitaryHaar.haar n) β
        (fun ω => LatticeGibbs.action (X.image realVertex) (links X ω) 1)
    z.im=0 ∧ 0 ≤ z.re := by
  dsimp only
  have hs : (fun ω : Edge X → Group n => LatticeGibbs.action (X.image realVertex) (links X ω) 1)=
      action X := by
    funext ω
    exact (action_eq X ω).symm
  rw [hs,gibbs_integral _ β (action X) (action_measurable X)]
  have hp := reflection_positive hX β hβ F hF hFb
  constructor
  · simp only [Complex.smul_im,smul_eq_mul,hp.1,mul_zero]
  · simpa only [Complex.smul_re,smul_eq_mul] using
      mul_nonneg (ENNReal.toReal_nonneg) hp.2

end PMAction.D4ActionReflection
