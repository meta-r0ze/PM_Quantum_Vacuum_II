import PMAction.CommonResponse

/-!
# Conservative dynamics through an on-site isometric encoding

A unitary on encoded modes extends by identity on the orthogonal complement.
Products, iterates, norms and response intertwine exactly. The extension is a
constructed amplitude update, not a primitive gate decomposition or event price.
-/
noncomputable section
namespace PMAction.IsometricDynamics
open Matrix CommonResponse
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def complement (E : Matrix a b ℂ) : Matrix a a ℂ := 1-E*Eᴴ

def extend (E : Matrix a b ℂ) (U : Matrix b b ℂ) : Matrix a a ℂ :=
  E*U*Eᴴ + complement E

lemma complement_left (E : Matrix a b ℂ) (hE : Eᴴ*E=1) : complement E * E = 0 := by
  simp [complement, Matrix.sub_mul, Matrix.mul_assoc, hE]

lemma complement_right (E : Matrix a b ℂ) (hE : Eᴴ*E=1) : Eᴴ * complement E = 0 := by
  simp [complement, Matrix.mul_sub, ← Matrix.mul_assoc, hE]

lemma complement_square (E : Matrix a b ℂ) (hE : Eᴴ*E=1) :
    complement E * complement E = complement E := by
  change (1-E*Eᴴ)*complement E = complement E
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, complement_right E hE,
    Matrix.mul_zero, sub_zero]

omit [Fintype a] in
theorem extend_one (E : Matrix a b ℂ) : extend E 1 = 1 := by
  simp only [extend, Matrix.mul_one, complement]
  abel

omit [DecidableEq a] in
lemma sandwich_mul (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U V : Matrix b b ℂ) :
    (E*U*Eᴴ)*(E*V*Eᴴ) = E*(U*V)*Eᴴ := by
  calc
    _ = E*U*(Eᴴ*E)*V*Eᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hE]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem extend_mul (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U V : Matrix b b ℂ) :
    extend E (U*V) = extend E U * extend E V := by
  have hl : (E*U*Eᴴ)*complement E=0 := by
    rw [Matrix.mul_assoc, complement_right E hE, Matrix.mul_zero]
  have hr : complement E*(E*V*Eᴴ)=0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, complement_left E hE]
    simp
  simp only [extend, add_mul, mul_add, sandwich_mul E hE, hl, hr,
    complement_square E hE, add_zero, zero_add]

omit [Fintype a] [DecidableEq b] in
lemma extend_star (E : Matrix a b ℂ) (U : Matrix b b ℂ) :
    (extend E U)ᴴ = extend E Uᴴ := by
  simp [extend, complement, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, Matrix.mul_assoc]

theorem unitary (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U : Matrix b b ℂ)
    (hU : U ∈ unitary (Matrix b b ℂ)) : extend E U ∈ unitary (Matrix a a ℂ) := by
  have hl : Uᴴ*U=1 := hU.1
  have hr : U*Uᴴ=1 := hU.2
  constructor
  · change (extend E U)ᴴ * extend E U = 1
    rw [extend_star, ← extend_mul E hE, hl, extend_one]
  · change extend E U * (extend E U)ᴴ = 1
    rw [extend_star, ← extend_mul E hE, hr, extend_one]

theorem intertwining (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U : Matrix b b ℂ) :
    extend E U * E = E*U := by
  rw [extend, Matrix.add_mul, complement_left E hE, add_zero, Matrix.mul_assoc, hE, Matrix.mul_one]

theorem iterations (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U : Matrix b b ℂ) (N : ℕ) :
    (extend E U)^N * E = E * U^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Matrix.mul_assoc, intertwining E hE, ← Matrix.mul_assoc, ih]
    simp only [pow_succ, Matrix.mul_assoc]

omit [DecidableEq a] in
theorem population (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (v : b → ℂ) :
    nsq (E *ᵥ v) = nsq v := by
  unfold nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hE, one_mulVec]

theorem response (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (U : Matrix b b ℂ) (v : b → ℂ) :
    stateFlag (extend E U) (E *ᵥ v) = stateFlag U v := by
  have hd : E *ᵥ v - extend E U *ᵥ (E *ᵥ v) = E *ᵥ (v-U *ᵥ v) := by
    rw [mulVec_mulVec, intertwining E hE, ← mulVec_mulVec, Matrix.mulVec_sub]
  rw [stateFlag, hd, population E hE]
  rfl

end PMAction.IsometricDynamics
