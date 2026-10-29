import PMAction.WalkReferenceCoupling

/-!
# A local walk/reference interface and its complete named-operation schedule

The record and live doublets propagate in opposite velocity channels. One
on-site gamma gate at a specified coupling site exchanges the arriving packets:
if the incoming record is the reference, the outgoing live packet is restored
and the old live packet is carried away in the record channel.

Initial seed supply, incoming streams, the selected pulse family and its
physical admissibility are inputs. Prices below count all named scheduled
operations; they are not a proof that each operation is one primitive E8 event.
-/
noncomputable section
namespace PMAction.WalkReferenceProtocol
open Matrix ConcreteFermion CommonResponse WalkReferenceCoupling
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A local phase gate in the concrete spinor coordinates. -/
def coupling (o : X) : Matrix (X × Fin 4) (X × Fin 4) ℂ :=
  diagonal (fun p => if p.1 = o then gamma p.2 p.2 else 1)

theorem coupling_unitary (o : X) : coupling o ∈ unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
  constructor <;>
    simp only [star_eq_conjTranspose, coupling, diagonal_conjTranspose, diagonal_mul_diagonal]
  all_goals
    ext p q
    by_cases hp : p = q
    · subst q
      rcases p with ⟨x,a⟩
      by_cases hx : x = o <;> fin_cases a <;> simp [gamma, hx]
    · simp [diagonal, hp]

lemma coupling_action (o x : X) (ψ : X × Fin 4 → ℂ) (a : Fin 4) :
    (coupling o *ᵥ ψ) (x,a) =
      if x = o then (gamma *ᵥ (fun b => ψ (x,b))) a else ψ (x,a) := by
  rw [coupling, mulVec_diagonal]
  by_cases hx : x = o
  · fin_cases a <;> simp [hx, gamma, mulVec, dotProduct, Fin.sum_univ_four]
  · simp [hx]

/-- One actual transport followed by the local reference coupling. -/
def update (o : X) (e : Equiv.Perm X) : Matrix (X × Fin 4) (X × Fin 4) ℂ :=
  coupling o * WalkRecordTransport.transport e

theorem update_unitary (o : X) (e : Equiv.Perm X) :
    update o e ∈ unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) :=
  (unitary _).mul_mem (coupling_unitary o) (WalkRecordTransport.transport_unitary e)

/-- The actual local encoding of both incoming streams. -/
def field (live record : X → Doublet) : X × Fin 4 → ℂ :=
  fun p => pack (Sum.elim (live p.1) (record p.1)) p.2

lemma transport_action (e : Equiv.Perm X) (live record : X → Doublet) (x : X) (a : Fin 4) :
    (WalkRecordTransport.transport e *ᵥ field live record) (x,a) =
      pack (Sum.elim (live (e⁻¹ x)) (record (e x))) a := by
  rw [WalkRecordTransport.transport_decomposition, add_mulVec]
  simp only [Pi.add_apply, WalkRecordTransport.neighbour_action]
  change ((beta * LocalUnitary.coefficient 2) *ᵥ pack (Sum.elim (live (e x)) (record (e x)))) a +
      ((beta * (LocalUnitary.coefficient 2)ᴴ) *ᵥ pack
        (Sum.elim (live (e⁻¹ x)) (record (e⁻¹ x)))) a = _
  rw [forward_packet, reverse_packet]
  simp only [pack, raw, Sum.elim_inl, Sum.elim_inr, smul_add, Pi.add_apply]
  exact add_comm _ _

/-- At the designated site the incoming reference and old live packet exchange;
other sites continue their two opposing streams. -/
theorem update_action (o : X) (e : Equiv.Perm X) (live record : X → Doublet)
    (x : X) (a : Fin 4) :
    (update o e *ᵥ field live record) (x,a) =
      if x = o then pack (Sum.elim (record (e x)) (live (e⁻¹ x))) a
      else pack (Sum.elim (live (e⁻¹ x)) (record (e x))) a := by
  rw [update, ← mulVec_mulVec, coupling_action]
  by_cases hx : x = o
  · simp only [hx, ite_true]
    have he : (fun b => (WalkRecordTransport.transport e *ᵥ field live record) (o,b)) =
        pack (Sum.elim (live (e⁻¹ o)) (record (e o))) := by
      funext b
      exact transport_action e live record o b
    rw [he, repair]
  · simp only [hx, ite_false]
    exact transport_action e live record x a

/-- A supplied incoming reference gives exact live restoration and record retention
in the actual spatial-spinor update, with no discarded amplitude. -/
theorem reference_arrival (o : X) (e : Equiv.Perm X) (live record : X → Doublet)
    (r : Doublet) (hclean : record (e o) = r) :
    (fun a => (update o e *ᵥ field live record) (o,a)) =
      pack (Sum.elim r (live (e⁻¹ o))) := by
  funext a
  simp [update_action, hclean]

/-- A clean record is both sufficient and necessary for this exact interface. -/
theorem reference_arrival_iff (o : X) (e : Equiv.Perm X) (live record : X → Doublet)
    (r : Doublet) :
    ((fun a => (update o e *ᵥ field live record) (o,a)) =
      pack (Sum.elim r (live (e⁻¹ o)))) ↔ record (e o) = r := by
  rw [reference_arrival o e live record (record (e o)) rfl]
  constructor
  · intro h
    have he := pack_injective h
    funext a
    exact congrFun he (.inl a)
  · rintro h
    rw [h]

/-- The initially uniform forward reference train is compatible with transport.
The statement is before consumption by coupling, not indefinite free renewal. -/
theorem prepared_train_stationary (e : Equiv.Perm X) :
    WalkRecordTransport.transport e *ᵥ field (fun _ : X => 0) (fun _ => reference) =
      field (fun _ : X => 0) (fun _ => reference) := by
  ext p
  rcases p with ⟨x,a⟩
  rw [transport_action]
  rfl

/-- Preparing a known seed at every site consumes an explicitly counted array. -/
def preparationArray : Matrix (X × Fin 4) (X × Fin 4) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ preparation

theorem preparationArray_unitary : preparationArray (X := X) ∈
    unitary (Matrix (X × Fin 4) (X × Fin 4) ℂ) := by
  have hl : preparationᴴ * preparation = 1 := preparation_unitary.1
  have hr : preparation * preparationᴴ = 1 := preparation_unitary.2
  constructor <;>
    simp [preparationArray, star_eq_conjTranspose, conjTranspose_kronecker,
      ← mul_kronecker_mul, hl, hr]

lemma preparationArray_action (ψ : X × Fin 4 → ℂ) (x : X) (a : Fin 4) :
    (preparationArray *ᵥ ψ) (x,a) = (preparation *ᵥ (fun b => ψ (x,b))) a := by
  simpa [preparationArray] using
    WalkRecordTransport.neighbour_action (Equiv.refl X) preparation ψ x a

/-- No copying from an absent seed: the source array is part of the initial state. -/
theorem prepares_record_array :
    preparationArray *ᵥ (fun p : X × Fin 4 => seed p.2) =
      field (fun _ => 0) (fun _ => reference) := by
  ext p
  rcases p with ⟨x,a⟩
  rw [preparationArray_action]
  exact congrFun prepares_forward a

omit [DecidableEq X] in
/-- Unit reference packets at every site have population proportional to array size. -/
theorem prepared_array_population : nsq (field (X := X) (fun _ => 0) (fun _ => reference)) =
    (Fintype.card X : ℝ) := by
  simp only [LinkExpansion.nsq_eq, Fintype.sum_prod_type]
  have he (x : X) : (∑ a : Fin 4, Complex.normSq (field (fun _ : X => 0)
      (fun _ => reference) (x,a))) = 1 := by
    change (∑ a, Complex.normSq (pack (Sum.elim (fun _ : Fin 2 => 0) reference) a)) = 1
    rw [← LinkExpansion.nsq_eq, pack_norm]
    simp [LinkExpansion.nsq_eq, reference, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp_rw [he]
  simp

inductive Instruction where
  | hop
  | coin
  | phase
  | couple

/-- Matrix-product order: execution is hop, coin, phase, then coupling. -/
def program : List Instruction := [.couple, .phase, .coin, .hop]

def decode (o : X) (e : Equiv.Perm X) : Instruction → Matrix (X × Fin 4) (X × Fin 4) ℂ
  | .hop => LocalUnitary.step e 2 (Real.pi/2)
  | .coin => (1 : Matrix X X ℂ) ⊗ₖ beta
  | .phase => (-Complex.I) • 1
  | .couple => coupling o

theorem program_correct (o : X) (e : Equiv.Perm X) :
    (program.map (decode o e)).prod = update o e := by
  simp only [program, decode, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [update, WalkRecordTransport.pulse_realization]
  simp

def price (hop coin phase couple : ℝ) : Instruction → ℝ
  | .hop => hop
  | .coin => coin
  | .phase => phase
  | .couple => couple

/-- Every named executed operation is charged; no macro is declared one E8 event. -/
theorem step_price (hop coin phase couple : ℝ) :
    (program.map (price hop coin phase couple)).sum = hop + coin + phase + couple := by
  simp [program, price]
  ring

omit [DecidableEq X] in
/-- Initial preparation is charged separately from N transport/coupling trials. -/
theorem complete_price (N : ℕ) (setup : X → ℝ) (hop coin phase couple : ℝ) :
    (∑ x, setup x) + (∑ _ : Fin N, (program.map (price hop coin phase couple)).sum) =
      (∑ x, setup x) + N * (hop + coin + phase + couple) := by
  simp [step_price]
  ring

omit [DecidableEq X] in
/-- Under the inherited comparison tariff, all separately prepared seeds are counted. -/
theorem preparation_readout_price (toll : ℝ) (m : ℕ) :
    (∑ _ : X, responseCost toll m (stateFlag preparation seed)) =
      Fintype.card X * (toll * m * ((1 - Real.cos (Real.pi/4))/2)) := by
  rw [preparation_response]
  simp [responseCost]

end PMAction.WalkReferenceProtocol
