import PMAction.RootCarrierWalk
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# A native finite routing implementation of the reference protocol

The two live labels stream one way, the two record labels the other. At the
specified coupling site, the existing root exchanges them. All other labels
stay fixed. These are lookup permutations: a matrix row names its input.
The spatial neighbour permutation and the maintenance task remain supplied.
-/
noncomputable section
namespace PMAction.NativeCarrierProtocol
open Matrix
open scoped Kronecker
abbrev C := ActualRootRepair.C
abbrev Ports := ActualRootRepair.Ports
variable {X : Type*} [Fintype X] [DecidableEq X]

def labels : (X × Ports) ↪ (X × C) where
  toFun p := (p.1,ActualRootRepair.label p.2)
  inj' := by
    rintro ⟨x,j⟩ ⟨y,k⟩ h
    change (x,ActualRootRepair.label j) = (y,ActualRootRepair.label k) at h
    exact Prod.ext (Prod.mk.inj h).1 (ActualRootRepair.label_injective (Prod.mk.inj h).2)

omit [Fintype X] [DecidableEq X] in
@[simp] lemma labels_apply (p : X × Ports) : labels p = (p.1,ActualRootRepair.label p.2) := rfl

/-- Pullback lookup for the counterpropagating channels. -/
def stream (e : Equiv.Perm X) : Equiv.Perm (X × Ports) where
  toFun p := match p.2 with
    | .inl i => (e⁻¹ p.1,.inl i)
    | .inr i => (e p.1,.inr i)
  invFun p := match p.2 with
    | .inl i => (e p.1,.inl i)
    | .inr i => (e⁻¹ p.1,.inr i)
  left_inv p := by rcases p with ⟨x,i|i⟩ <;> simp
  right_inv p := by rcases p with ⟨x,i|i⟩ <;> simp

def couple (o : X) : Equiv.Perm (X × Ports) where
  toFun p := (p.1,if p.1=o then (Equiv.sumComm _ _) p.2 else p.2)
  invFun p := (p.1,if p.1=o then (Equiv.sumComm _ _) p.2 else p.2)
  left_inv p := by rcases p with ⟨x,i|i⟩ <;> by_cases h:x=o <;> simp [h]
  right_inv p := by rcases p with ⟨x,i|i⟩ <;> by_cases h:x=o <;> simp [h]

/-- Lookup first applies the on-site root, then follows the incoming stream. -/
def portStep (o : X) (e : Equiv.Perm X) : Equiv.Perm (X × Ports) :=
  (couple o).trans (stream e)

/-- Extend the port permutation by identity on the four unused carrier labels. -/
def lookup (o : X) (e : Equiv.Perm X) : Equiv.Perm (X × C) :=
  (portStep o e).viaEmbedding labels

omit [Fintype X] in
lemma lookup_label (o : X) (e : Equiv.Perm X) (x : X) (j : Ports) :
    lookup o e (x,ActualRootRepair.label j) = labels (portStep o e (x,j)) :=
  Equiv.Perm.viaEmbedding_apply (portStep o e) (labels (X := X)) (x,j)

omit [Fintype X] in
lemma lookup_unused (o : X) (e : Equiv.Perm X) (x : X) (c : C)
    (hc : c ∉ Set.range ActualRootRepair.label) : lookup o e (x,c) = (x,c) := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨⟨y,j⟩,h⟩
  exact hc ⟨j,congrArg Prod.snd h⟩

omit [Fintype X] [DecidableEq X] in
lemma field_unused (live record : X → Fin 2 → ℂ) (x : X) (c : C)
    (hc : c ∉ Set.range ActualRootRepair.label) : RootCarrierWalk.field live record (x,c)=0 := by
  have hh (j : Ports) : c ≠ ActualRootRepair.label j := by
    intro h; exact hc ⟨j,h.symm⟩
  simp [RootCarrierWalk.field, ActualRootRepair.pack, ActualRootRepair.embedding,
    mulVec, dotProduct, hh]

/-- Exact amplitude semantics derived from a finite permutation, without a frame gate. -/
theorem field_step (o : X) (e : Equiv.Perm X) (live record : X → Fin 2 → ℂ) :
    (lookup o e).permMatrix ℂ *ᵥ RootCarrierWalk.field live record =
      RootCarrierWalk.field
        (fun x => if x=o then record (e x) else live (e⁻¹ x))
        (fun x => if x=o then live (e⁻¹ x) else record (e x)) := by
  rw [Matrix.permMatrix_mulVec]
  ext p
  rcases p with ⟨x,c⟩
  change RootCarrierWalk.field live record (lookup o e (x,c)) = _
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hc
    rw [lookup_label]
    rcases j with i | i <;> by_cases hx:x=o <;>
      simp [portStep, couple, stream, hx, RootCarrierWalk.field,
        ActualRootRepair.pack, ActualRootRepair.encoded_coordinate]
  · rw [lookup_unused o e x c hc, field_unused _ _ x c hc, field_unused _ _ x c hc]

omit [Fintype X] in
/-- Routing uses only the given site, forward neighbour or backward neighbour. -/
theorem causal_lookup (o : X) (e : Equiv.Perm X) (p : X × C) :
    (lookup o e p).1 = p.1 ∨ (lookup o e p).1 = e p.1 ∨
      (lookup o e p).1 = e⁻¹ p.1 := by
  rcases p with ⟨x,c⟩
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hc
    rw [lookup_label]
    rcases j with i | i <;> by_cases hx:x=o <;> simp [portStep, couple, stream, hx]
  · rw [lookup_unused o e x c hc]
    exact Or.inl rfl

omit [Fintype X] in
/-- The only internal-label operation is the existing root at the coupling site. -/
theorem internal_root (o : X) (e : Equiv.Perm X) (x : X) (c : C) :
    (lookup o e (x,c)).2 = if x=o then ActualRootRepair.root c else c := by
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hc
    rw [lookup_label]
    have hr := (ActualRootRepair.label_exchange j).symm
    by_cases hx:x=o
    · rcases j with i | i <;> simpa [portStep, couple, stream, hx] using hr
    · rcases j with i | i <;> simp [portStep, couple, stream, hx]
  · have hn : c ∉ CarrierEvents.active 0 := by
      rw [← ActualRootRepair.moving_modes_exact]
      simpa using hc
    have hf : ActualRootRepair.root c=c := by
      simpa [CarrierEvents.active] using hn
    rw [lookup_unused o e x c hc]
    simp [hf]

/-- Sparse amplitude embedding of native ports; no coherent spinor frame appears. -/
def portEmbedding : Matrix (X × C) (X × Ports) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ ActualRootRepair.embedding

lemma port_field (ψ : X × Ports → ℂ) :
    portEmbedding *ᵥ ψ = RootCarrierWalk.field
      (fun x i => ψ (x,.inl i)) (fun x i => ψ (x,.inr i)) := by
  ext p
  rcases p with ⟨x,c⟩
  simp [portEmbedding, RootCarrierWalk.field, ActualRootRepair.pack, mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]

lemma port_column (x : X) (j : Ports) :
    portEmbedding *ᵥ Pi.single (x,j) 1 = Pi.single (x,ActualRootRepair.label j) 1 := by
  ext p
  rcases p with ⟨y,c⟩
  by_cases hy:y=x <;> by_cases hc:c=ActualRootRepair.label j <;>
    simp [portEmbedding, Matrix.col_apply, ActualRootRepair.embedding, hy, hc]

lemma interface_unused (c : C) (hc : c ∉ Set.range ActualRootRepair.label) (i : Fin 4) :
    RootWalkEncoding.interface c i = 0 := by
  have hh (j : Ports) : c ≠ ActualRootRepair.label j := by
    intro h; exact hc ⟨j,h.symm⟩
  simp [RootWalkEncoding.interface, Matrix.mul_apply, ActualRootRepair.embedding, hh]

lemma old_unused_basis (o : X) (e : Equiv.Perm X) (x : X) (c : C)
    (hc : c ∉ Set.range ActualRootRepair.label) :
    RootCarrierWalk.update o e *ᵥ Pi.single (x,c) 1 = Pi.single (x,c) 1 := by
  have hd : (RootCarrierWalk.embedding (X := X))ᴴ *ᵥ Pi.single (x,c) 1 = 0 := by
    ext q
    simp [Matrix.col_apply, conjTranspose_apply,
      RootCarrierWalk.embedding, interface_unused c hc]
  simp only [RootCarrierWalk.update, IsometricDynamics.extend, IsometricDynamics.complement,
    add_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hd, mulVec_zero, zero_add, sub_zero]

lemma native_unused_basis (o : X) (e : Equiv.Perm X) (x : X) (c : C)
    (hc : c ∉ Set.range ActualRootRepair.label) :
    (lookup o e).permMatrix ℂ *ᵥ Pi.single (x,c) 1 = Pi.single (x,c) 1 := by
  have hf := lookup_unused o e x c hc
  rw [Matrix.permMatrix_mulVec]
  ext q
  simp only [Function.comp_apply]
  by_cases hq:q=(x,c)
  · subst q; simp [hf]
  · have hn : lookup o e q ≠ (x,c) := by
      intro h
      exact hq ((lookup o e).injective (h.trans hf.symm))
    simp [hq, hn]

/-- The previous coherent-frame extension is exactly this native permutation,
including its action on unused modes. No physical frame-change gate is executed. -/
theorem matrix_eq (o : X) (e : Equiv.Perm X) :
    RootCarrierWalk.update o e = (lookup o e).permMatrix ℂ := by
  apply Matrix.ext_of_mulVec_single
  rintro ⟨x,c⟩
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j,rfl⟩ := hc
    let ψ : X × Ports → ℂ := Pi.single (x,j) 1
    have hf : RootCarrierWalk.field (fun y i => ψ (y,.inl i))
        (fun y i => ψ (y,.inr i)) = Pi.single (x,ActualRootRepair.label j) 1 := by
      rw [← port_field]
      exact port_column x j
    rw [← hf, RootCarrierWalk.field_step, field_step]
  · rw [old_unused_basis o e x c hc, native_unused_basis o e x c hc]

end PMAction.NativeCarrierProtocol
