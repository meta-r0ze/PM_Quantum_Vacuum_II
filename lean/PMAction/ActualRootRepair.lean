import PMAction.RootBranchEncoding
import PMAction.CoherentRecordRestoration
import PMAction.RestorationResponse

/-!
# An actual E8-induced carrier root implements a two-mode record exchange

The four moving vector-class carriers encode two live and two record amplitude
modes. Their actual root reflection is precisely exchange, with no new branch
labels. The amplitude lift and prepared coherent record remain explicit model
inputs. The classical label-event price below is not a coherent phase tariff.
-/
noncomputable section
namespace PMAction.ActualRootRepair
open Matrix CommonResponse
abbrev C := CarrierEvents.Carrier 0
abbrev Ports := (Fin 2) ⊕ (Fin 2)

def positive : C := ⟨![4,2,2,2], by decide +kernel⟩
def negative : C := ⟨![0,2,2,2], by decide +kernel⟩
abbrev root := CarrierEvents.reflect 0

def label : Ports → C := Sum.elim
  (fun i => if i = 0 then positive else negative)
  (fun i => root (if i = 0 then positive else negative))

lemma label_injective : Function.Injective label := by decide +kernel

lemma label_moves (j : Ports) : root (label j) ≠ label j := by
  rcases j with j | j <;> fin_cases j <;> decide +kernel

lemma label_exchange (j : Ports) : root (label j) = label ((Equiv.sumComm _ _) j) := by
  rcases j with j | j <;> fin_cases j <;> decide +kernel

/-- The encoding uses exactly the existing four moving labels, not additional modes. -/
theorem moving_modes_exact : Finset.univ.image label = CarrierEvents.active 0 := by
  decide +kernel

def embedding : Matrix C Ports ℂ := fun i j => if i = label j then 1 else 0

theorem isometry : embeddingᴴ * embedding = 1 := by
  ext i j
  have hh : label j = label i ↔ i = j := by
    rw [label_injective.eq_iff, eq_comm]
  simp [embedding, mul_apply, conjTranspose_apply, one_apply, hh]

def pack (live record : Fin 2 → ℂ) : C → ℂ := embedding *ᵥ Sum.elim live record

lemma encoded_coordinate (x : Ports → ℂ) (j : Ports) :
    (embedding *ᵥ x) (label j) = x j := by
  have hh (i : Ports) : label j = label i ↔ j = i := label_injective.eq_iff
  simp [embedding, mulVec, dotProduct, hh]

theorem pack_injective (l r l' r' : Fin 2 → ℂ) (h : pack l r = pack l' r') :
    l = l' ∧ r = r' := by
  constructor
  · funext i
    have hh := congrFun h (label (.inl i))
    simpa only [pack, encoded_coordinate, Sum.elim_inl] using hh
  · funext i
    have hh := congrFun h (label (.inr i))
    simpa only [pack, encoded_coordinate, Sum.elim_inr] using hh

theorem population (live record : Fin 2 → ℂ) :
    nsq (pack live record) = nsq live + nsq record := by
  unfold pack nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, isometry, one_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

lemma column (j : Ports) : embedding *ᵥ Pi.single j 1 = Pi.single (label j) 1 := by
  ext i
  simp [embedding, Pi.single_apply]

/-- The existing root, not a named abstract exchange gate, acts on the four ports. -/
theorem intertwining : root.permMatrix ℂ * embedding =
    embedding * BranchMixerSynthesis.exchange := by
  apply Matrix.ext
  intro i j
  have h := CoherentRecordRestoration.exchange_is_permutation (n := Fin 2)
  have hs : Function.Involutive (Equiv.sumComm (Fin 2) (Fin 2)) := by
    intro x; cases x <;> rfl
  have hc := RootTransferAccounting.basis_move (Equiv.sumComm (Fin 2) (Fin 2)) hs j
  have hl := RootTransferAccounting.basis_move root (CarrierEvents.reflection_involutive 0) (label j)
  have he : (root.permMatrix ℂ * embedding) *ᵥ Pi.single j 1 =
      (embedding * BranchMixerSynthesis.exchange) *ᵥ Pi.single j 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, column, hl, h, hc, column, label_exchange]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun he i

theorem repair (live record : Fin 2 → ℂ) :
    root.permMatrix ℂ *ᵥ pack live record = pack record live := by
  rw [pack, mulVec_mulVec, intertwining, ← mulVec_mulVec,
    CoherentRecordRestoration.exchange_action]
  rfl

/-- The prepared record is consumed by exact live restoration, retaining all input. -/
theorem prepared_repair (input reference : Fin 2 → ℂ) :
    (∀ i, (root.permMatrix ℂ *ᵥ pack input reference) (label (.inl i)) = reference i) ∧
      (∀ i, (root.permMatrix ℂ *ᵥ pack input reference) (label (.inr i)) = input i) := by
  rw [repair]
  exact ⟨fun i => encoded_coordinate _ _, fun i => encoded_coordinate _ _⟩

/-- Omitting the operation succeeds on all live modes exactly when no repair is needed. -/
theorem idle_correct_iff (input reference : Fin 2 → ℂ) :
    (∀ i, pack input reference (label (.inl i)) = reference i) ↔ input = reference := by
  simp only [pack, encoded_coordinate, Sum.elim_inl]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Reusing the occupied record restores the old input, not a fresh reference. -/
theorem occupied_record_returns (input reference : Fin 2 → ℂ) :
    root.permMatrix ℂ *ᵥ (root.permMatrix ℂ *ᵥ pack input reference) = pack input reference := by
  rw [repair, repair]

/-- Classical carrier-label sampling over these ports charges every root operation.
This supplied experiment differs from a coherent comparison measurement. -/
theorem classical_event_price (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (fun _ : Fin 1 =>
      Finset.univ.filter (fun j : Ports => root (label j) ≠ label j)) = toll := by
  have he : Finset.univ.filter (fun j : Ports => root (label j) ≠ label j) = Finset.univ := by
    ext j; simp [label_moves]
  rw [he, PMArch.NetCost.expected_count_linear]
  norm_num [PMArch.NetCost.prob, Fintype.card_sum]

/-- A coherently equal live/reference pair is fixed by the very same root operator. -/
theorem reference_response (reference : Fin 2 → ℂ) :
    stateFlag (root.permMatrix ℂ) (pack reference reference) = 0 := by
  rw [stateFlag, repair, sub_self]
  simp [nsq]

lemma embedding_population (x : Ports → ℂ) : nsq (embedding *ᵥ x) = nsq x := by
  unfold nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, isometry, one_mulVec]

/-- The operational response is inherited through the actual-carrier isometry. -/
theorem response_intertwining (live record : Fin 2 → ℂ) :
    stateFlag (root.permMatrix ℂ) (pack live record) =
      stateFlag BranchMixerSynthesis.exchange (Sum.elim live record) := by
  have hd : pack live record - root.permMatrix ℂ *ᵥ pack live record =
      embedding *ᵥ (Sum.elim live record -
        BranchMixerSynthesis.exchange *ᵥ Sum.elim live record) := by
    rw [pack, mulVec_mulVec, intertwining, ← mulVec_mulVec, Matrix.mulVec_sub]
  rw [stateFlag, hd, embedding_population]
  rfl

/-- Exact discrepancy response of the root-implemented conservative repair.
A probability interpretation also needs normalization of the whole preparation. -/
theorem repair_response (live reference : Fin 2 → ℂ) :
    stateFlag (root.permMatrix ℂ) (pack live reference) = nsq (live-reference)/2 := by
  rw [response_intertwining]
  exact RestorationResponse.prepared_exchange_response live reference

/-- The same actual root supplies the continuous branch rotation algebra on
both payload modes, conditional on admitting that coherent rotation. -/
theorem rotation_pack (θ : ℝ) (live record : Fin 2 → ℂ) :
    LocalUnitary.rotation (root.permMatrix ℂ) θ *ᵥ pack live record =
      pack ((Real.cos θ : ℂ) • live + (Complex.I*(Real.sin θ : ℂ)) • record)
        ((Complex.I*(Real.sin θ : ℂ)) • live + (Real.cos θ : ℂ) • record) := by
  rw [LocalUnitary.rotation, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, repair]
  unfold pack
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 1
  ext j
  rcases j with j | j <;> simp [add_comm]

open scoped Matrix.Norms.Operator in
/-- The root-reconstructed phase acts as the same branch pulse on both live/record
payload modes. Its scalar phase is part of the result. -/
theorem phase_pack (p t : ℝ) (live record : Fin 2 → ℂ) :
    RootTransferPhase.phase root p t *ᵥ pack live record =
      Complex.exp (-(RootTransferPhase.gap p*t/2 : ℝ)*Complex.I) •
        pack ((Real.cos (RootTransferPhase.gap p*t/2) : ℂ) • live +
          (Complex.I*(Real.sin (RootTransferPhase.gap p*t/2) : ℂ)) • record)
        ((Complex.I*(Real.sin (RootTransferPhase.gap p*t/2) : ℂ)) • live +
          (Real.cos (RootTransferPhase.gap p*t/2) : ℂ) • record) := by
  have h := InvolutionSpectral.phase_rotation (root.permMatrix ℂ)
    (RootTransferPhase.gap p*t/2)
  rw [show 2*(RootTransferPhase.gap p*t/2)=RootTransferPhase.gap p*t by ring] at h
  rw [RootTransferPhase.phase_formula root (CarrierEvents.reflection_involutive 0), h,
    smul_mulVec, rotation_pack]

/-- For any normalized initial carrier-label law supported on these four ports,
there is one changed-label event per root application. No uniformity is needed.
The initial-label experiment is explicit; this is not a coherent flag price. -/
theorem supported_label_price (toll : ℝ) (μ : Ports → ℝ) (hμ : ∑ j, μ j = 1) :
    EventAccounting.cost toll μ (fun _ : Fin 1 =>
      Finset.univ.filter (fun j : Ports => root (label j) ≠ label j)) = toll := by
  have he : Finset.univ.filter (fun j : Ports => root (label j) ≠ label j) = Finset.univ := by
    ext j; simp [label_moves]
  rw [he, EventAccounting.weighted_linear]
  simp [EventAccounting.eventMass, hμ]

/-- A substrate record is not automatically clean: correct restoration at this
interface is equivalent to its arriving in the required reference state. -/
theorem clean_record_iff (input record reference : Fin 2 → ℂ) :
    (∀ i, (root.permMatrix ℂ *ᵥ pack input record) (label (.inl i)) = reference i) ↔
      record = reference := by
  rw [repair]
  simp only [pack, encoded_coordinate, Sum.elim_inl]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

end PMAction.ActualRootRepair
