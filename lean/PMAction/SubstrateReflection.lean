import PMAction.CarrierEvents

/-! The carrier-coordinate reflection is the restriction of an actual integral
E8 root reflection. This does not identify carrier amplitudes with physical spinors. -/
noncomputable section
namespace PMAction.SubstrateReflection
open Matrix
open PMArch.Lattices

abbrev Lattice := Fin 8 → ℤ

/-- First simple root of Paper I's explicit D4⊕D4 embedding in E8. -/
def root : Lattice := fun i => d4Embedding i 0

theorem root_coordinates : root = ![0,0,-1,0,0,0,0,0] := by decide +kernel

theorem root_norm : pairing root root=2 := by decide +kernel

def reflect (z : Lattice) : Lattice := z-pairing z root • root

lemma reflect_coordinates (z : Lattice) :
    reflect z=Function.update z 2 (z 0+z 3-z 2) := by
  ext i; fin_cases i <;>
    simp [reflect, root_coordinates, pairing, gram, mulVec, dotProduct, Fin.sum_univ_succ]; ring

theorem involutive : Function.Involutive reflect := by
  intro z
  rw [reflect_coordinates, reflect_coordinates]
  ext i; fin_cases i <;> simp

/-- The operation preserves the actual integral E8 quadratic form. -/
theorem preserves_norm (z : Lattice) : pairing (reflect z) (reflect z)=pairing z z := by
  rw [reflect_coordinates]
  simp [pairing, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- It preserves Paper I's four D4⊕D4 glue labels, not merely a norm count. -/
theorem preserves_glue (z : Lattice) : glueCode (reflect z)=glueCode z := by
  simp [glueCode, reflect_coordinates]

/-- The induced first-sector simple-root coordinate change. -/
def rootCoordinates (w : Lattice) : Lattice := Function.update w 0 (-w 0+w 1)

theorem embedding_intertwines (w : Lattice) :
    reflect (d4Embedding*ᵥw)=d4Embedding*ᵥrootCoordinates w := by
  rw [reflect_coordinates]
  ext i; fin_cases i <;>
    simp [d4Embedding, rootCoordinates, mulVec, dotProduct, Fin.sum_univ_succ]; ring

/-- In the even-sum Euclidean model this is precisely the carrier coordinate swap. -/
theorem euclidean_intertwines (w : Lattice) :
    d4Roots ![rootCoordinates w 0,rootCoordinates w 1,rootCoordinates w 2,rootCoordinates w 3] =
      (d4Roots ![w 0,w 1,w 2,w 3]) ∘ Equiv.swap (0 : Fin 4) 1 := by
  ext i; fin_cases i <;> norm_num [d4Roots, rootCoordinates, Equiv.swap_apply_def]

end PMAction.SubstrateReflection
