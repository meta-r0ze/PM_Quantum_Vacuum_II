import PMAction.LocalUnitary
import PMAction.RecordTransport
import PMAction.RestorationResponse

/-!
# An exact record channel in the existing neighbour-walk factors

One direction pulse at pi/2, followed by the concrete on-site beta coin and
an overall phase, has a forward internal channel. An explicit
injective two-mode encoding intertwines its forward channel with the finite
cyclic shift used by RecordTransport.

This is a composite available in the mathematical pulse/coin family. It is
not identified with the full corrected vacuum update, its selected tick, an
E8 primitive, a free clean-record preparation or an event price.
-/
noncomputable section
namespace PMAction.WalkRecordTransport
open Matrix ConcreteFermion
open scoped Kronecker

/-- A concrete two-mode forward encoding on spatial axis 2. -/
def encode (u : Fin 2 → ℂ) : Fin 4 → ℂ := ![u 0, u 1, Complex.I*u 0, -Complex.I*u 1]

lemma encode_injective : Function.Injective encode := by
  intro u v h
  funext a
  fin_cases a
  · simpa [encode] using congrFun h 0
  · simpa [encode] using congrFun h 1

lemma encode_norm (u : Fin 2 → ℂ) : CommonResponse.nsq (encode u) = 2 * CommonResponse.nsq u := by
  simp [LinkExpansion.nsq_eq, encode, Fin.sum_univ_four, Fin.sum_univ_two,
    Complex.normSq_mul]
  ring

lemma forward_local (u : Fin 2 → ℂ) :
    (beta * LocalUnitary.coefficient 2) *ᵥ encode u = encode u := by
  ext a
  fin_cases a <;>
    norm_num [encode, LocalUnitary.coefficient, beta, alpha, mul_apply,
      mulVec, dotProduct, Fin.sum_univ_four] <;> ring_nf <;> simp [Complex.I_sq]
  all_goals ring

lemma reverse_local_zero (u : Fin 2 → ℂ) :
    (beta * (LocalUnitary.coefficient 2)ᴴ) *ᵥ encode u = 0 := by
  ext a
  fin_cases a <;>
    norm_num [encode, LocalUnitary.coefficient, beta, alpha, mul_apply,
      mulVec, dotProduct, conjTranspose_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp [Complex.I_sq]

section Spatial
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The actual neighbour involution composed with the existing beta coin. -/
def transport (e : Equiv.Perm X) : Matrix (X × Fin 4) (X × Fin 4) ℂ :=
  ((1 : Matrix X X ℂ) ⊗ₖ beta) * LocalUnitary.neighbor e 2

/-- This is a specified pulse/coin composite, not an assumption of a new shift gate. -/
theorem pulse_realization (e : Equiv.Perm X) : transport e =
    (-Complex.I) • (((1 : Matrix X X ℂ) ⊗ₖ beta) * LocalUnitary.step e 2 (Real.pi/2)) := by
  simp [transport, LocalUnitary.step, LocalUnitary.rotation,
    smul_smul]

lemma transport_unitary (e : Equiv.Perm X) :
    transport e ∈ unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
  have hc : ((1 : Matrix X X ℂ) ⊗ₖ beta) ∈
      unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
    constructor <;>
      simp [star_eq_conjTranspose, conjTranspose_kronecker,
        beta_hermitian.eq, ← mul_kronecker_mul, beta_square]
  have hn : LocalUnitary.neighbor e 2 ∈
      unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
    constructor <;>
      simpa only [star_eq_conjTranspose, (LocalUnitary.neighbor_hermitian e 2).eq]
        using LocalUnitary.neighbor_square e 2
  exact (unitary _).mul_mem hc hn

lemma transport_decomposition (e : Equiv.Perm X) : transport e =
    e.permMatrix ℂ ⊗ₖ (beta * LocalUnitary.coefficient 2) +
      (e⁻¹).permMatrix ℂ ⊗ₖ (beta * (LocalUnitary.coefficient 2)ᴴ) := by
  simp [transport, LocalUnitary.neighbor, mul_add, ← mul_kronecker_mul]

/-- A spatial permutation with an internal matrix acts on the corresponding neighbour. -/
lemma neighbour_action (e : Equiv.Perm X) (A : Spin) (ψ : X × Fin 4 → ℂ) (x : X) (a : Fin 4) :
    ((e.permMatrix ℂ ⊗ₖ A) *ᵥ ψ) (x,a) = (A *ᵥ (fun b => ψ (e x,b))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = A a b * ∑ y, e.permMatrix ℂ x y * ψ (y,b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      congr 1
      exact congrFun (Matrix.permMatrix_mulVec (v := fun y => ψ (y,b)) e) x

/-- Two independent record modes at every spatial site. -/
def field (u : X × Fin 2 → ℂ) : X × Fin 4 → ℂ := fun p => encode (fun a => u (p.1,a)) p.2

omit [Fintype X] [DecidableEq X] in
lemma field_injective : Function.Injective (field (X := X)) := by
  intro u v h
  funext p
  have he : encode (fun b => u (p.1,b)) = encode (fun b => v (p.1,b)) := by
    funext a
    exact congrFun h (p.1,a)
  exact congrFun (encode_injective he) p.2

/-- The encoded field propagates exactly one site; the opposite channel cancels. -/
theorem forward_action (e : Equiv.Perm X) (u : X × Fin 2 → ℂ) (x : X) (a : Fin 4) :
    (transport e *ᵥ field u) (x,a) = encode (fun b => u (e x,b)) a := by
  rw [transport_decomposition, add_mulVec]
  simp only [Pi.add_apply, neighbour_action]
  change ((beta * LocalUnitary.coefficient 2) *ᵥ encode (fun b => u (e x,b))) a +
      ((beta * (LocalUnitary.coefficient 2)ᴴ) *ᵥ encode (fun b => u (e⁻¹ x,b))) a = _
  rw [forward_local, reverse_local_zero]
  simp

/-- Normalizing the fixed local encoding makes it an isometry. -/
def normalizedField (u : X × Fin 2 → ℂ) : X × Fin 4 → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • field u

omit [DecidableEq X] in
lemma field_norm (u : X × Fin 2 → ℂ) :
    CommonResponse.nsq (field u) = 2 * CommonResponse.nsq u := by
  simp only [LinkExpansion.nsq_eq, Fintype.sum_prod_type]
  change (∑ x, ∑ a, Complex.normSq (encode (fun b => u (x,b)) a)) = _
  have h (x : X) : (∑ a, Complex.normSq (encode (fun b => u (x,b)) a)) =
      2 * ∑ b, Complex.normSq (u (x,b)) := by
    simpa only [LinkExpansion.nsq_eq] using encode_norm (fun b => u (x,b))
  simp_rw [h]
  rw [Finset.mul_sum]

omit [DecidableEq X] in
lemma normalizedField_norm (u : X × Fin 2 → ℂ) :
    CommonResponse.nsq (normalizedField u) = CommonResponse.nsq u := by
  rw [normalizedField, ControllerHamiltonian.nsq_smul, RestorationResponse.balanced_factor,
    field_norm]
  ring

end Spatial

/-- Route A's finite-chain target: the existing walk factors contain precisely
the FIFO shift on an explicitly encoded two-mode record channel. -/
theorem cyclic_intertwining (R : ℕ) (u : Fin (R+1) × Fin 2 → ℂ) :
    transport (finRotate (R+1)) *ᵥ field u = field (RecordTransport.tick R u) := by
  ext p
  rcases p with ⟨x,a⟩
  rw [forward_action]
  simp only [field]
  congr 1
  funext b
  rw [RecordTransport.tick_apply]

/-- The same exact identification uses a norm-preserving record encoding. -/
theorem normalized_cyclic_intertwining (R : ℕ) (u : Fin (R+1) × Fin 2 → ℂ) :
    transport (finRotate (R+1)) *ᵥ normalizedField u =
      normalizedField (RecordTransport.tick R u) := by
  rw [normalizedField, Matrix.mulVec_smul, cyclic_intertwining]
  rfl

/-- The record-flow identification holds for every number of applications. -/
theorem cyclic_iterations (R t : ℕ) (u : Fin (R+1) × Fin 2 → ℂ) :
    (fun ψ => transport (finRotate (R+1)) *ᵥ ψ)^[t] (field u) =
      field ((RecordTransport.tick R)^[t] u) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, cyclic_intertwining, Function.iterate_succ_apply']

/-- This particular moving record channel is not automatically a static
zero-mode preparation of the full domain-wall Hamiltonian. -/
theorem single_wall_zero_mode (u : Fin 2 → ℂ) :
    hamiltonian 0 0 *ᵥ Sum.elim (encode u) (fun _ => 0) = 0 ↔ u = 0 := by
  rw [kernel_coordinates]
  simp [encode, funext_iff, Fin.forall_fin_two]

end PMAction.WalkRecordTransport
