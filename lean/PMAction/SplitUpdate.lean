import PMAction.LocalUnitary

/-! An eight-component, finite-propagation unitary split update.
The on-site unitary is an explicit input; its physical generator is not selected. -/
noncomputable section
namespace PMAction.SplitUpdate
open Matrix ConcreteFermion
open scoped Kronecker

variable {X : Type*} [Fintype X] [DecidableEq X]

def coefficient (j : Fin 3) : Matrix Sites Sites ℂ :=
  fromBlocks (LocalUnitary.coefficient j) 0 0 (LocalUnitary.coefficient j)

lemma coefficient_relations (j : Fin 3) : coefficient j*coefficient j=0 ∧
    coefficient j*(coefficient j)ᴴ+(coefficient j)ᴴ*coefficient j=1 := by
  have hc := LocalUnitary.coefficient_relations j
  constructor
  · simp [coefficient, fromBlocks_multiply, hc.1, ← fromBlocks_zero]
  · simp only [coefficient, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      mul_zero, zero_mul, add_zero, zero_add]
    simpa only [fromBlocks_add, add_zero, fromBlocks_one] using
      congrArg (fun A : Spin => fromBlocks A (0 : Spin) (0 : Spin) A) hc.2

def neighbor (e : Equiv.Perm X) (j : Fin 3) : Matrix (X × Sites) (X × Sites) ℂ :=
  e.permMatrix ℂ ⊗ₖ coefficient j + (e.permMatrix ℂ)ᴴ ⊗ₖ (coefficient j)ᴴ

lemma neighbor_hermitian (e : Equiv.Perm X) (j : Fin 3) : (neighbor e j).IsHermitian := by
  simp [IsHermitian, neighbor, conjTranspose_add, conjTranspose_kronecker, add_comm]

lemma neighbor_square (e : Equiv.Perm X) (j : Fin 3) : neighbor e j*neighbor e j=1 := by
  have hc := coefficient_relations j
  have hcc : (coefficient j)ᴴ*(coefficient j)ᴴ=0 := by
    rw [← conjTranspose_mul, hc.1, conjTranspose_zero]
  have hs : e.permMatrix ℂ*(e.permMatrix ℂ)ᴴ=1 := by
    rw [conjTranspose_permMatrix, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  have ht : (e.permMatrix ℂ)ᴴ*e.permMatrix ℂ=1 := by
    rw [conjTranspose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  simp only [neighbor, add_mul, mul_add, ← mul_kronecker_mul, hc.1, hcc,
    kronecker_zero, zero_add, add_zero, hs, ht]
  rw [← kronecker_add, add_comm, hc.2, one_kronecker_one]

def direction (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :=
  LocalUnitary.rotation (neighbor e j) τ

lemma direction_unitary (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    direction e j τ ∈ unitary (Matrix (X × Sites) (X × Sites) ℂ) :=
  LocalUnitary.rotation_unitary _ _ (neighbor_hermitian e j) (neighbor_square e j)

/-- A precise matrix support contract, independent of lattice size. -/
def Supported (R : X → X → Prop) (A : Matrix (X × Sites) (X × Sites) ℂ) : Prop :=
  ∀ x y a b, ¬R x y → A (x,a) (y,b)=0

def Near (e : Equiv.Perm X) (x y : X) : Prop := y=x ∨ y=e x ∨ y=e.symm x

def Compose (R S : X → X → Prop) (x z : X) : Prop := ∃ y, R x y ∧ S y z

lemma supported_mul {R S : X → X → Prop} {A B : Matrix (X × Sites) (X × Sites) ℂ}
    (ha : Supported R A) (hb : Supported S B) : Supported (Compose R S) (A*B) := by
  intro x z a c hn
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨y,b⟩ _
  by_cases hr : R x y
  · have hs : ¬ S y z := fun hh => hn ⟨y,hr,hh⟩
    rw [hb y z b c hs, mul_zero]
  · rw [ha x y a b hr, zero_mul]

lemma direction_supported (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    Supported (Near e) (direction e j τ) := by
  intro x y a b hn
  have hx : x ≠ y := fun h => hn (Or.inl h.symm)
  have hp : e x ≠ y := fun h => hn (Or.inr (Or.inl h.symm))
  have hm : e.symm x ≠ y := fun h => hn (Or.inr (Or.inr h.symm))
  simp [direction, LocalUnitary.rotation, neighbor, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, hx, hp, hm, conjTranspose_permMatrix,
    Equiv.toPEquiv_apply, Prod.ext_iff]

/-- The on-site coin may mix the two walls, but never different positions. -/
def onsite (Q : Matrix Sites Sites ℂ) : Matrix (X × Sites) (X × Sites) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ Q

lemma onsite_unitary (Q : Matrix Sites Sites ℂ) (hq : Q ∈ unitary (Matrix Sites Sites ℂ)) :
    onsite (X := X) Q ∈ unitary (Matrix (X × Sites) (X × Sites) ℂ) := by
  constructor
  · change (onsite (X := X) Q)ᴴ*onsite Q=1
    simp only [onsite, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      one_mul, show Qᴴ*Q=1 from hq.1, one_kronecker_one]
  · change onsite (X := X) Q*(onsite Q)ᴴ=1
    simp only [onsite, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      one_mul, show Q*Qᴴ=1 from hq.2, one_kronecker_one]

lemma onsite_supported (Q : Matrix Sites Sites ℂ) : Supported Eq (onsite (X := X) Q) := by
  intro x y a b h
  simp [onsite, kronecker_apply, one_apply_ne h]

def update (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ) (τ : ℝ) :=
  onsite Q * (direction (e 0) 0 τ * direction (e 1) 1 τ * direction (e 2) 2 τ)

theorem update_unitary (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ)
    (τ : ℝ) (hq : Q ∈ unitary (Matrix Sites Sites ℂ)) :
    update e Q τ ∈ unitary (Matrix (X × Sites) (X × Sites) ℂ) :=
  (unitary _).mul_mem (onsite_unitary Q hq)
    ((unitary _).mul_mem ((unitary _).mul_mem (direction_unitary (e 0) 0 τ)
      (direction_unitary (e 1) 1 τ)) (direction_unitary (e 2) 2 τ))

/-- Three neighbor reads in succession; at most 3^3 possible spatial sites. -/
def Reach (e : Fin 3 → Equiv.Perm X) : X → X → Prop :=
  Compose (Compose (Near (e 0)) (Near (e 1))) (Near (e 2))

theorem update_supported (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ) (τ : ℝ) :
    Supported (Reach e) (update e Q τ) := by
  have h := supported_mul (onsite_supported (X := X) Q)
    (supported_mul (supported_mul (direction_supported (e 0) 0 τ)
      (direction_supported (e 1) 1 τ)) (direction_supported (e 2) 2 τ))
  intro x y a b hn
  apply h x y a b
  rintro ⟨z,hz,hr⟩
  subst z
  exact hn hr

/-- An exact input-dependence theorem, including arbitrary internal wall mixing. -/
theorem update_local (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ) (τ : ℝ)
    (ψ φ : X × Sites → ℂ) (x : X)
    (h : ∀ y, Reach e x y → ∀ a, ψ (y,a)=φ (y,a)) :
    ∀ a, (update e Q τ*ᵥψ) (x,a)=(update e Q τ*ᵥφ) (x,a) := by
  intro a
  simp only [mulVec, dotProduct]
  apply Finset.sum_congr rfl
  rintro ⟨y,b⟩ _
  by_cases hr : Reach e x y
  · rw [h y hr b]
  · rw [update_supported e Q τ x y a b hr, zero_mul, zero_mul]

/-- Exact preservation of the finite-state complex inner product. -/
theorem update_inner (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ)
    (τ : ℝ) (hq : Q ∈ unitary (Matrix Sites Sites ℂ)) (ψ φ : X × Sites → ℂ) :
    star (update e Q τ*ᵥψ) ⬝ᵥ (update e Q τ*ᵥφ) = star ψ ⬝ᵥ φ := by
  have hu := update_unitary e Q τ hq
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    show (update e Q τ)ᴴ*update e Q τ=1 from hu.1, vecMul_one]

/-- In particular, total squared amplitude is conserved on the whole finite lattice. -/
theorem update_population (e : Fin 3 → Equiv.Perm X) (Q : Matrix Sites Sites ℂ)
    (τ : ℝ) (hq : Q ∈ unitary (Matrix Sites Sites ℂ)) (ψ : X × Sites → ℂ) :
    ∑ z, Complex.normSq ((update e Q τ*ᵥψ) z) = ∑ z, Complex.normSq (ψ z) := by
  have h := congrArg Complex.re (update_inner e Q τ hq ψ ψ)
  simpa [dotProduct, Complex.normSq_apply, Complex.mul_re, RCLike.star_def] using h

end PMAction.SplitUpdate
