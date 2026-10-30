import PMAction.CarrierParity
import PMArch.ChannelSymmetry

/-!
# Native D4 root words for the internal real generators

All four simple reflections act on actual carrier labels, preserve glue and
norm, and preserve antipodal parity. Five fixed words implement beta, gamma,
alpha_0, alpha_2 and the real signed permutation -i alpha_1 on the odd sector.
Negation is a sixth root word. Word lengths are certificates, not minimum prices.
-/
noncomputable section
namespace PMAction.CarrierWeyl
open Matrix CarrierEvents CarrierParity

def simpleBox (j : Fin 4) (k : Box) : Box :=
  match j.val with
  | 0 => k ∘ Equiv.swap 0 1
  | 1 => k ∘ Equiv.swap 1 2
  | 2 => k ∘ Equiv.swap 2 3
  | _ => ![k 0,k 1,(k 3).rev,(k 2).rev]

lemma simple_valid : ∀ (j : Fin 4) (c : Fin 3) (k : Box),
    valid c k → valid c (simpleBox j k) := by decide +kernel

lemma simple_twice : ∀ (j : Fin 4) (k : Box), simpleBox j (simpleBox j k)=k := by decide +kernel

def simple (c : Fin 3) (j : Fin 4) : Equiv.Perm (Carrier c) where
  toFun v := ⟨simpleBox j v.1,simple_valid j c v.1 v.2⟩
  invFun v := ⟨simpleBox j v.1,simple_valid j c v.1 v.2⟩
  left_inv v := Subtype.ext (simple_twice j v.1)
  right_inv v := Subtype.ext (simple_twice j v.1)

lemma simple_is_root : ∀ (c : Fin 3) (j : Fin 4) (v : Carrier c),
    vector (simple c j v) = PMArch.ChannelSymmetry.refl
      (PMArch.ChannelSymmetry.simple j) (vector v) := by decide +kernel

/-- Product order in the standard coordinate representation. -/
def word : Fin 6 → List (Fin 4) := ![
  [1,0,2,1], [2,3], [0,3], [1,2,1,3,1,2], [0,1,2,3,1,2],
  [0,1,0,2,1,0,3,1,0,2,1,3]]

/-- Row lookup reverses the root word; each simple reflection is involutive. -/
def lookup (c : Fin 3) (g : Fin 6) : Equiv.Perm (Carrier c) :=
  ((word g).reverse.map (simple c)).prod

def realMatrix : Fin 6 → Matrix (Fin 4) (Fin 4) ℤ := ![
  !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0],
  !![1,0,0,0;0,1,0,0;0,0,-1,0;0,0,0,-1],
  !![0,1,0,0;1,0,0,0;0,0,0,-1;0,0,-1,0],
  !![1,0,0,0;0,-1,0,0;0,0,-1,0;0,0,0,1],
  !![0,-1,0,0;1,0,0,0;0,0,0,1;0,0,-1,0],
  !![-1,0,0,0;0,-1,0,0;0,0,-1,0;0,0,0,-1]]

def complexMatrix (g : Fin 6) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (realMatrix g i j : ℂ)

/-- Exact native lookup certificate, checked on every actual carrier of every class. -/
lemma lookup_coordinates : ∀ (c : Fin 3) (g : Fin 6) (v : Carrier c) (i : Fin 4),
    vector (lookup c g v) i = ∑ j, realMatrix g j i * vector v j := by decide +kernel

lemma lookup_antipode : ∀ (c : Fin 3) (v : Carrier c), lookup c 5 v = antipode c v := by
  decide +kernel

/-- Root words induce the intended matrices on coordinate contrasts, not the full label space. -/
theorem intertwining (c : Fin 3) (g : Fin 6) :
    (lookup c g).permMatrix ℂ * embedding c = embedding c * complexMatrix g := by
  ext v i
  change ((lookup c g).permMatrix ℂ *ᵥ (fun w => embedding c w i)) v = _
  rw [Matrix.permMatrix_mulVec]
  change scale * (vector (lookup c g v) i : ℂ) = _
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (lookup_coordinates c g v i)
  push_cast at hg
  rw [hg,Finset.mul_sum]
  simp only [mul_apply,embedding,complexMatrix]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma beta_eq : complexMatrix 0 = ConcreteFermion.beta := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [complexMatrix,realMatrix,ConcreteFermion.beta]
lemma gamma_eq : complexMatrix 1 = ConcreteFermion.gamma := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [complexMatrix,realMatrix,ConcreteFermion.gamma]
lemma alpha0_eq : complexMatrix 2 = ConcreteFermion.alpha 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [complexMatrix,realMatrix,ConcreteFermion.alpha]
lemma alpha2_eq : complexMatrix 3 = ConcreteFermion.alpha 2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [complexMatrix,realMatrix,ConcreteFermion.alpha]
lemma alpha1_eq : Complex.I • complexMatrix 4 = ConcreteFermion.alpha 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [complexMatrix,realMatrix,ConcreteFermion.alpha]

end PMAction.CarrierWeyl
