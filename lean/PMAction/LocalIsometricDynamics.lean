import PMAction.IsometricDynamics
import PMAction.PropagationBounds
import PMAction.VacuumSplit
import PMAction.CarrierVacuumSector

/-!
# Finite-support full-label completion through an on-site isometry

Extending a local spinor update by identity on the unobserved complement gives
an exactly local unitary on all carrier labels, with the same coordinate readout
for every initial amplitude. This is an alternative completion, not an equality
to the directional-exponential completion in `StateIdentification`. It introduces
no new labels or sites. Its microscopic gate admission and event prices are not
proved by the matrix construction.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PMAction.LocalIsometricDynamics
open Matrix
open scoped Kronecker
variable {X a b : Type*} [Fintype X] [DecidableEq X]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def encoding (E : Matrix a b ℂ) : Matrix (X × a) (X × b) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ E

omit [DecidableEq a] [Fintype b] in
lemma encoding_isometry (E : Matrix a b ℂ) (hE : Eᴴ*E=1) :
    (encoding (X := X) E)ᴴ * encoding (X := X) E = 1 := by
  simp only [encoding,conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,
    one_mul,hE,one_kronecker_one]

/-- Identity on the unobserved complement is an explicit construction choice. -/
def completion (E : Matrix a b ℂ) (U : Matrix (X × b) (X × b) ℂ) :
    Matrix (X × a) (X × a) ℂ := IsometricDynamics.extend (encoding E) U

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
lemma sandwich_entry (E : Matrix a b ℂ) (U : Matrix (X × b) (X × b) ℂ)
    (x y : X) (i j : a) :
    ((encoding E * U * (encoding E)ᴴ) : Matrix (X × a) (X × a) ℂ) (x,i) (y,j) =
      ∑ k, ∑ l, E i k * U (x,k) (y,l) * star (E j l) := by
  simp [encoding,mul_apply,conjTranspose_apply,apply_ite,
    Fintype.sum_prod_type,Matrix.one_apply,ite_mul,Finset.sum_mul]
  rw [Finset.sum_comm]

omit [Fintype a] [DecidableEq b] in
lemma complement_encoding (E : Matrix a b ℂ) :
    IsometricDynamics.complement (encoding (X := X) E) =
      (1 : Matrix X X ℂ) ⊗ₖ IsometricDynamics.complement E := by
  simp only [IsometricDynamics.complement,encoding,conjTranspose_kronecker,
    conjTranspose_one,← mul_kronecker_mul,one_mul]
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases h : x=y
  · subst y
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply,h]

omit [Fintype a] [DecidableEq b] in
/-- Extending through an on-site encoding does not enlarge spatial support. -/
theorem support (E : Matrix a b ℂ) (U : Matrix (X × b) (X × b) ℂ)
    (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hU : ∀ x y i j, ¬R x y → U (x,i) (y,j)=0) :
    ∀ x y i j, ¬R x y → completion E U (x,i) (y,j)=0 := by
  intro x y i j hn
  have hxy : x ≠ y := fun h => hn (h ▸ hrefl x)
  change ((encoding E * U * (encoding E)ᴴ + IsometricDynamics.complement (encoding E)) : Matrix (X × a) (X × a) ℂ) (x,i) (y,j)=0
  rw [Matrix.add_apply,sandwich_entry,complement_encoding]
  simp only [hU x y _ _ hn,mul_zero,zero_mul,Finset.sum_const_zero,
    kronecker_apply,one_apply_ne hxy,zero_add]

/-- Whole-label unitarity follows without an assumption on initial parity. -/
theorem unitary (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) (hU : U ∈ unitary _) :
    completion E U ∈ unitary _ :=
  IsometricDynamics.unitary _ (encoding_isometry E hE) U hU

theorem intertwining (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) :
    completion E U * encoding E = encoding E * U :=
  IsometricDynamics.intertwining _ (encoding_isometry E hE) U

/-- Exact coordinate observation for every ambient amplitude, including even modes. -/
theorem readout (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) :
    (encoding E)ᴴ * completion E U = U * (encoding E)ᴴ := by
  change (encoding E)ᴴ * (encoding E*U*(encoding E)ᴴ +
    IsometricDynamics.complement (encoding E)) = _
  rw [Matrix.mul_add,IsometricDynamics.complement_right _ (encoding_isometry E hE),
    add_zero,← Matrix.mul_assoc,← Matrix.mul_assoc,encoding_isometry E hE,one_mul]

/-- All readout histories agree, not only one step or initially encoded fields. -/
theorem readout_iterations (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) (n : ℕ) :
    (encoding E)ᴴ * (completion E U)^n = U^n * (encoding E)ᴴ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ,← Matrix.mul_assoc,ih,Matrix.mul_assoc,readout E hE U]
    simp only [Matrix.mul_assoc]

omit [DecidableEq b] in
/-- The complement stays present and is fixed; no filtering or erasure is executed. -/
theorem invisible_fixed (E : Matrix a b ℂ) (U : Matrix (X × b) (X × b) ℂ)
    (ψ : X × a → ℂ) (hψ : (encoding E)ᴴ *ᵥ ψ=0) : completion E U *ᵥ ψ=ψ := by
  simp [completion,IsometricDynamics.extend,IsometricDynamics.complement,
    Matrix.add_mulVec,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,hψ]

/-- The full fixed space is the original fixed readout plus arbitrary invisible
background. No additional observable stationary mode is introduced. -/
theorem fixed_iff (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) (ψ : X × a → ℂ) :
    completion E U *ᵥ ψ=ψ ↔ U *ᵥ ((encoding E)ᴴ *ᵥ ψ)=(encoding E)ᴴ *ᵥ ψ := by
  constructor
  · intro h
    have hh := congrArg ((encoding E)ᴴ *ᵥ ·) h
    rwa [mulVec_mulVec,readout E hE U,← mulVec_mulVec] at hh
  · intro h
    change (encoding E*U*(encoding E)ᴴ + (1-encoding E*(encoding E)ᴴ)) *ᵥ ψ=ψ
    rw [Matrix.add_mulVec,Matrix.sub_mulVec,one_mulVec,
      ← mulVec_mulVec,← mulVec_mulVec,h,← mulVec_mulVec]
    abel

/-- For this completion the full squared-displacement response is exactly the
coordinate response, because invisible modes are retained without displacement.
This identity is not a primitive execution-cost theorem. -/
theorem response_all (E : Matrix a b ℂ) (hE : Eᴴ*E=1)
    (U : Matrix (X × b) (X × b) ℂ) (ψ : X × a → ℂ) :
    CommonResponse.stateFlag (completion E U) ψ =
      CommonResponse.stateFlag U ((encoding E)ᴴ *ᵥ ψ) := by
  have hd : ψ-completion E U *ᵥ ψ =
      encoding E *ᵥ ((encoding E)ᴴ *ᵥ ψ-U *ᵥ ((encoding E)ᴴ *ᵥ ψ)) := by
    simp only [completion,IsometricDynamics.extend,IsometricDynamics.complement,
      Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.mulVec_sub,one_mulVec,← mulVec_mulVec]
    abel
  rw [CommonResponse.stateFlag,hd,IsometricDynamics.population _ (encoding_isometry E hE)]
  rfl

omit [DecidableEq b] in
/-- Arbitrary full-label fields agreeing on the support have the same output. -/
theorem local_dependence (E : Matrix a b ℂ) (U : Matrix (X × b) (X × b) ℂ)
    (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hU : ∀ x y i j, ¬R x y → U (x,i) (y,j)=0)
    (ψ φ : X × a → ℂ) (x : X)
    (h : ∀ y, R x y → ∀ i, ψ (y,i)=φ (y,i)) :
    ∀ i, (completion E U *ᵥ ψ) (x,i)=(completion E U *ᵥ φ) (x,i) := by
  intro i
  simp only [mulVec,dotProduct]
  apply Finset.sum_congr rfl
  rintro ⟨y,j⟩ _
  by_cases hr : R x y
  · rw [h y hr j]
  · rw [support E U R hrefl hU x y i j hr,zero_mul,zero_mul]

end PMAction.LocalIsometricDynamics

namespace PMAction.CarrierLocalCompletion
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open Matrix CarrierVacuumSector LocalIsometricDynamics
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Same two D₄ sectors of one fixed carrier class (16 labels); no ancilla. -/
def update (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :=
  completion (embedding c) (SplitUpdate.update e (VacuumSplit.onsiteCoin τ) τ)

theorem update_unitary (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    update c e τ ∈ unitary (Matrix (X × Labels c) (X × Labels c) ℂ) :=
  LocalIsometricDynamics.unitary _ (isometry c) _
    (SplitUpdate.update_unitary _ _ _ (VacuumSplit.onsiteCoin_unitary τ))

omit [Fintype X] [DecidableEq X] in
lemma reach_refl (e : Fin 3 → Equiv.Perm X) (x : X) : SplitUpdate.Reach e x x :=
  ⟨x,⟨x,Or.inl rfl,Or.inl rfl⟩,Or.inl rfl⟩

/-- The construction uses exactly the existing carrier-label space. -/
theorem label_count (c : Fin 3) : Fintype.card (Labels c)=16 := by
  simp [Labels,CarrierEvents.carrier_card]

/-- Each lifted directional factor retains the nearest-neighbour stencil. -/
theorem direction_supported (c : Fin 3) (e : Equiv.Perm X) (d : Fin 3) (τ : ℝ) :
    ∀ x y i j, ¬SplitUpdate.Near e x y →
      completion (embedding c) (SplitUpdate.direction e d τ) (x,i) (y,j)=0 :=
  support _ _ _ (fun _ => Or.inl rfl) (SplitUpdate.direction_supported e d τ)

/-- The lifted coin is still on-site on every carrier mode. -/
theorem coin_supported (c : Fin 3) (τ : ℝ) :
    ∀ x y i j, x ≠ y →
      completion (embedding c) (SplitUpdate.onsite (X := X) (VacuumSplit.onsiteCoin τ))
        (x,i) (y,j)=0 :=
  support _ _ Eq (fun _ => rfl) (SplitUpdate.onsite_supported _)

/-- Whole-label support is the same three-read stencil as the spinor update. -/
theorem update_supported (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    ∀ x y i j, ¬SplitUpdate.Reach e x y → update c e τ (x,i) (y,j)=0 :=
  support _ _ _ (reach_refl e) (SplitUpdate.update_supported e _ τ)

/-- Exact causal dependence for all carrier fields, with no odd-state premise. -/
theorem update_local (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ)
    (ψ φ : X × Labels c → ℂ) (x : X)
    (h : ∀ y, SplitUpdate.Reach e x y → ∀ i, ψ (y,i)=φ (y,i)) :
    ∀ i, (update c e τ *ᵥ ψ) (x,i)=(update c e τ *ᵥ φ) (x,i) :=
  LocalIsometricDynamics.local_dependence _ _ _ (reach_refl e)
    (SplitUpdate.update_supported e _ τ) ψ φ x h

/-- The complete dependence set has at most 27 sites, independent of lattice size. -/
theorem dependency_card (e : Fin 3 → Equiv.Perm X) (x : X) :
    (Finset.univ.filter (SplitUpdate.Reach e x)).card ≤ 27 := by
  classical
  exact SplitUpdate.reachable_card_le e x

/-- Readout follows every spinor tick for every initial full-label amplitude. -/
theorem readout_ticks (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) (n : ℕ)
    (ψ : X × Labels c → ℂ) :
    (encoding (embedding c))ᴴ *ᵥ ((update c e τ)^n *ᵥ ψ) =
      (SplitUpdate.update e (VacuumSplit.onsiteCoin τ) τ)^n *ᵥ
        ((encoding (embedding c))ᴴ *ᵥ ψ) := by
  rw [mulVec_mulVec,update,readout_iterations _ (isometry c),← mulVec_mulVec]

/-- Whole-carrier squared amplitude is conserved, including unobserved modes. -/
theorem population (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ)
    (ψ : X × Labels c → ℂ) :
    CommonResponse.nsq (update c e τ *ᵥ ψ)=CommonResponse.nsq ψ :=
  congrArg Complex.re (CommonResponse.unitary_nsq _ (update_unitary c e τ) ψ)

/-- Identity on invisible data is a reversible extension, not an erasure step. -/
theorem even_fixed (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ)
    (ψ : X × Labels c → ℂ) (hψ : (encoding (embedding c))ᴴ *ᵥ ψ=0) :
    update c e τ *ᵥ ψ=ψ := invisible_fixed _ _ ψ hψ

/-- The completion respects the four-factor schedule exactly. Each factor is
extended separately by the same local isometry; no frame change is executed. -/
theorem factorization (c : Fin 3) (e : Fin 3 → Equiv.Perm X) (τ : ℝ) :
    update c e τ =
      completion (embedding c) (SplitUpdate.onsite (X := X) (VacuumSplit.onsiteCoin τ)) *
      (completion (embedding c) (SplitUpdate.direction (e 0) 0 τ) *
        completion (embedding c) (SplitUpdate.direction (e 1) 1 τ) *
        completion (embedding c) (SplitUpdate.direction (e 2) 2 τ)) := by
  simp only [update,SplitUpdate.update,completion,
    IsometricDynamics.extend_mul _ (encoding_isometry _ (isometry c))]

/-- A periodic cubic-lattice specialization uses the already certified split. -/
theorem torus_readout (c : Fin 3) (N : ℕ) (τ : ℝ) (n : ℕ)
    (ψ : (Fin 3 → Fin N) × Labels c → ℂ) :
    (encoding (embedding c))ᴴ *ᵥ ((update c (SplitUpdate.axisShift N) τ)^n *ᵥ ψ) =
      (VacuumSplit.update N τ)^n *ᵥ ((encoding (embedding c))ᴴ *ᵥ ψ) :=
  readout_ticks c _ τ n ψ

end PMAction.CarrierLocalCompletion
