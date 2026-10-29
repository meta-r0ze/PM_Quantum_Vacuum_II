import PMAction.WallChiralCurrent
import PMAction.CarrierResponse

/-!
# A spectral guard on extending the four-mode carrier identification

One vector/glue-class root has trace four on all eight carrier labels. The
doubled spinor gamma has trace zero. They cannot be intertwined by an onto
unitary frame. This rules out only that single-root identification, not a
full vacuum model using different operators, composites or counted extra modes.
-/
noncomputable section
namespace PMAction.FullCarrierIdentification
open Matrix ConcreteFermion

lemma root_trace_re (c : Fin 3) : ((CarrierEvents.reflect c).permMatrix ℂ).trace.re = 4 := by
  let : Nonempty (CarrierEvents.Carrier c) := Fintype.card_pos_iff.mp (by
    rw [CarrierEvents.carrier_card]; norm_num)
  have h := CarrierResponse.reflection_flag c
  rw [InterferenceReadout.mean_trace _ (CarrierResponse.perm_unitary _),
    CarrierEvents.carrier_card] at h
  norm_num at h
  linarith

lemma doubled_gamma_trace : WallChiralCurrent.chirality.trace = 0 := by
  simp [WallChiralCurrent.chirality, gamma, Matrix.trace, Fintype.sum_sum_type,
    Fin.sum_univ_four]

/-- Cardinality matching alone does not identify the operator or its primitive price. -/
theorem no_single_root_full_gamma (c : Fin 3)
    (J : Matrix (CarrierEvents.Carrier c) Sites ℂ) (hL : Jᴴ*J=1) (hR : J*Jᴴ=1) :
    (CarrierEvents.reflect c).permMatrix ℂ * J ≠ J * WallChiralCurrent.chirality := by
  intro h
  have ht : ((CarrierEvents.reflect c).permMatrix ℂ).trace = WallChiralCurrent.chirality.trace := by
    calc
      _ = (((CarrierEvents.reflect c).permMatrix ℂ * J) * Jᴴ).trace := by
        rw [Matrix.mul_assoc,hR,Matrix.mul_one]
      _ = ((J * WallChiralCurrent.chirality)*Jᴴ).trace := by rw [h]
      _ = (Jᴴ*(J*WallChiralCurrent.chirality)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by rw [← Matrix.mul_assoc,hL,Matrix.one_mul]
  have hr := congrArg Complex.re ht
  rw [root_trace_re,doubled_gamma_trace] at hr
  norm_num at hr

/-- Anticommuting generators cannot share a nonzero fixed mode. A representation
sector must be identified before discarding an invariant uniform mode. -/
theorem common_fixed_obstruction {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (hA : A *ᵥ v=v) (hB : B *ᵥ v=v) : A*B ≠ -(B*A) := by
  intro h
  have hh := congrArg (fun M => M *ᵥ v) h
  rw [← mulVec_mulVec,hB,hA,neg_mulVec,← mulVec_mulVec,hA,hB] at hh
  apply hv
  ext i
  have hi := congrFun hh i
  change v i = -(v i) at hi
  change v i = 0
  linear_combination hi / 2

/-- All carrier permutations fix the uniform mode. Their full amplitude-space
matrices cannot already be a Clifford pair; invariant subspaces remain possible. -/
theorem no_full_permutation_clifford (c : Fin 3)
    (e f : Equiv.Perm (CarrierEvents.Carrier c)) :
    e.permMatrix ℂ * f.permMatrix ℂ ≠ -(f.permMatrix ℂ * e.permMatrix ℂ) := by
  let : Nonempty (CarrierEvents.Carrier c) := Fintype.card_pos_iff.mp (by
    rw [CarrierEvents.carrier_card]; norm_num)
  apply common_fixed_obstruction _ _ (fun _ => 1)
  · intro h
    have hh := congrFun h (Classical.choice inferInstance)
    norm_num at hh
  · rw [Matrix.permMatrix_mulVec]; rfl
  · rw [Matrix.permMatrix_mulVec]; rfl

end PMAction.FullCarrierIdentification
