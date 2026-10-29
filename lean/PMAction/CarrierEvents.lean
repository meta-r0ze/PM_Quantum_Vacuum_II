import PMArch.Channels
import PMArch.NetCost
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Actual minimal D4 glue-class carriers and reversible reflection events.
Uniform sampling is explicit; this does not select the physical event law. -/
noncomputable section
namespace PMAction.CarrierEvents
open Matrix Finset
open PMArch.Channels

/-- A nontrivial glue class: vector, spinor or conjugate spinor. -/
def classLabel (c : Fin 3) : ℕ := c.val+1
abbrev Box := Fin 4 → Fin 5

def valid (c : Fin 3) (k : Box) : Prop :=
  glueClass (boxVec k)=classLabel c ∧ norm4 (boxVec k)=4

instance (c : Fin 3) : DecidablePred (valid c) := fun k => by unfold valid; infer_instance

/-- These are Paper I's actual minimal-vector states, not eight arbitrary labels. -/
abbrev Carrier (c : Fin 3) := { k : Box // valid c k }

theorem carrier_card (c : Fin 3) : Fintype.card (Carrier c)=8 := by
  fin_cases c <;> decide +kernel

def vector {c : Fin 3} (v : Carrier c) : Fin 4 → ℤ := boxVec v.1

theorem vector_injective (c : Fin 3) : Function.Injective (@vector c) := by
  intro v w h
  apply Subtype.ext
  exact boxVec_injective h

theorem vector_properties {c : Fin 3} (v : Carrier c) :
    glueClass (vector v)=classLabel c ∧ norm4 (vector v)=4 := v.2

/-- Every integer minimal vector of this class is represented; the finite box loses none. -/
theorem vector_surjective (c : Fin 3) (y : Fin 4 → ℤ)
    (hc : glueClass y=classLabel c) (hn : norm4 y=4) : ∃ v : Carrier c, vector v=y := by
  obtain ⟨k,hk⟩ := mem_box y hn
  exact ⟨⟨k, by simpa [valid, hk] using And.intro hc hn⟩,hk⟩

def relabel (p : Equiv.Perm (Fin 4)) (k : Box) : Box := k ∘ p

lemma vector_relabel (p : Equiv.Perm (Fin 4)) (k : Box) :
    boxVec (relabel p k)=boxVec k ∘ p := rfl

lemma norm_relabel (p : Equiv.Perm (Fin 4)) (k : Box) :
    norm4 (boxVec (relabel p k))=norm4 (boxVec k) := by
  exact Equiv.sum_comp p (fun i => boxVec k i ^ 2)

lemma glue_relabel (p : Equiv.Perm (Fin 4)) (k : Box) :
    glueClass (boxVec (relabel p k))=glueClass (boxVec k) := by
  have he : (∀ i, Even (boxVec k (p i))) ↔ ∀ i, Even (boxVec k i) :=
    ⟨fun h i => by simpa using h (p.symm i), fun h i => h (p i)⟩
  have ho : (∀ i, Odd (boxVec k (p i))) ↔ ∀ i, Odd (boxVec k i) :=
    ⟨fun h i => by simpa using h (p.symm i), fun h i => h (p i)⟩
  have hs : (∑ i, boxVec k (p i))=∑ i, boxVec k i := Equiv.sum_comp p _
  simp only [glueClass, vector_relabel, Function.comp_apply, he, ho, hs]

/-- Every coordinate permutation acts reversibly on each fixed glue class. -/
def permute (c : Fin 3) (p : Equiv.Perm (Fin 4)) : Equiv.Perm (Carrier c) where
  toFun v := ⟨relabel p v.1, by
    simpa only [valid, glue_relabel, norm_relabel] using v.2⟩
  invFun v := ⟨relabel p.symm v.1, by
    simpa only [valid, glue_relabel, norm_relabel] using v.2⟩
  left_inv v := by apply Subtype.ext; funext i; simp [relabel]
  right_inv v := by apply Subtype.ext; funext i; simp [relabel]

/-- Reflection in the D4 root e0-e1. -/
def reflect (c : Fin 3) : Equiv.Perm (Carrier c) := permute c (Equiv.swap 0 1)
def root : Fin 4 → ℤ := ![1,-1,0,0]

theorem root_norm : norm4 root=2 ∧ (∑ i, root i)=0 := by decide +kernel

theorem reflection_formula {c : Fin 3} (v : Carrier c) :
    vector (reflect c v)=vector v-(vector v 0-vector v 1) • root := by
  ext i
  change vector v (Equiv.swap 0 1 i)=vector v i-(vector v 0-vector v 1)*root i
  fin_cases i <;> norm_num [root, Equiv.swap_apply_def]

theorem reflection_involutive (c : Fin 3) : Function.Involutive (reflect c) := by
  intro v; apply Subtype.ext; funext i
  simp [reflect, permute, relabel]

def active (c : Fin 3) : Finset (Carrier c) := univ.filter (fun v => reflect c v ≠ v)

/-- The moving-carrier count is derived from the actual class, independently of its label. -/
theorem active_card (c : Fin 3) : (active c).card=4 := by
  fin_cases c <;> decide +kernel

theorem uniform_activation (c : Fin 3) : PMArch.NetCost.prob (active c)=1/2 := by
  rw [PMArch.NetCost.prob, active_card, carrier_card]
  norm_num

/-- Cost of one explicitly identified primitive reflection event under uniform input. -/
theorem uniform_primitive_cost (c : Fin 3) (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (fun _ : Fin 1 => active c)=toll/2 := by
  rw [PMArch.NetCost.expected_count_linear]
  simp [uniform_activation, div_eq_mul_inv]

end PMAction.CarrierEvents
