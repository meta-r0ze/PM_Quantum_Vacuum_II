import PMAction.CarrierWeyl

/-! All simple root steps used by the native carrier words are restrictions
of integral E8 root reflections in Paper I's actual D4 ⊕ D4 embedding. -/
noncomputable section
namespace PMAction.SubstrateWeylRoots
open Matrix PMArch.Lattices
abbrev Lattice := Fin 8 → ℤ

def index (s : Bool) (j : Fin 4) : Fin 8 := if s then ⟨4+j.val, by omega⟩ else ⟨j.val, by omega⟩
def root (s : Bool) (j : Fin 4) : Lattice := fun i => d4Embedding i (index s j)
def reflect (s : Bool) (j : Fin 4) (z : Lattice) : Lattice :=
  z - pairing z (root s j) • root s j

theorem root_norm : ∀ s j, pairing (root s j) (root s j)=2 := by decide +kernel

/-- The ordinary simple-root coefficient update, in its own D4 sector. -/
def coordinates (s : Bool) (j : Fin 4) (w : Lattice) : Lattice :=
  Function.update w (index s j) (w (index s j) -
    ∑ k, PMArch.Channels.d4Gram j k * w (index s k))

def sector (s : Bool) (w : Lattice) : Fin 4 → ℤ :=
  d4Roots (fun j => w (index s j))

set_option maxHeartbeats 4000000 in
theorem embedding_intertwines (s : Bool) (j : Fin 4) (w : Lattice) :
    reflect s j (d4Embedding *ᵥ w) = d4Embedding *ᵥ coordinates s j w := by
  cases s <;> fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [reflect, root, index, coordinates, Function.update_apply, pairing, gram, d4Embedding,
      PMArch.Channels.d4Gram, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
/-- The occupied sector has exactly the already-certified carrier root action;
the other actual D4 sector is untouched. -/
theorem sector_intertwines (s t : Bool) (j : Fin 4) (w : Lattice) :
    sector t (coordinates s j w) =
      if t=s then PMArch.ChannelSymmetry.refl (PMArch.ChannelSymmetry.simple j) (sector t w)
      else sector t w := by
  cases s <;> cases t <;> fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [sector, coordinates, Function.update_apply, index, d4Roots, PMArch.Channels.d4Gram,
      PMArch.ChannelSymmetry.refl, PMArch.ChannelSymmetry.simple,
      PMArch.ChannelSymmetry.dot4, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 4000000 in
theorem preserves_norm (s : Bool) (j : Fin 4) (z : Lattice) :
    pairing (reflect s j z) (reflect s j z)=pairing z z := by
  cases s <;> fin_cases j <;>
    norm_num [reflect, root, index, pairing, gram, d4Embedding, mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

lemma root_glue_zero : ∀ s j, (root s j 0 : ZMod 2)=0 ∧ (root s j 5 : ZMod 2)=0 := by
  decide +kernel

theorem preserves_glue (s : Bool) (j : Fin 4) (z : Lattice) :
    glueCode (reflect s j z)=glueCode z := by
  apply Prod.ext
  · change ((z 0 - pairing z (root s j) * root s j 0 : ℤ) : ZMod 2) = (z 0 : ZMod 2)
    push_cast
    rw [(root_glue_zero s j).1, mul_zero, sub_zero]
  · change ((z 5 - pairing z (root s j) * root s j 5 : ℤ) : ZMod 2) = (z 5 : ZMod 2)
    push_cast
    rw [(root_glue_zero s j).2, mul_zero, sub_zero]

end PMAction.SubstrateWeylRoots
