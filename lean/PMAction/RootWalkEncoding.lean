import PMAction.ActualRootRepair
import PMAction.WalkReferenceProtocol

/-!
# Exact interface between actual root carriers and the walk's spinor frame

The previously constructed live/record encodings determine an explicit on-site
isometry from the walk's four spinor modes to the four moving vector-class
carrier modes. It intertwines gamma coupling with the actual root reflection.
This is a representation theorem, not a free physical change-of-frame gate or
a selection of a microscopic walk, coherent control tariff or reference source.
-/
noncomputable section
namespace PMAction.RootWalkEncoding
open Matrix CommonResponse ConcreteFermion
abbrev C := ActualRootRepair.C
abbrev Ports := ActualRootRepair.Ports

def rawFrame : Matrix (Fin 4) Ports ℂ :=
  fun i j => WalkReferenceCoupling.raw (Pi.single j 1) i

def scale : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
def frame : Matrix (Fin 4) Ports ℂ := scale • rawFrame

lemma raw_left : rawFrameᴴ * rawFrame = (2 : ℂ) • (1 : Matrix Ports Ports ℂ) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rawFrame, WalkReferenceCoupling.raw, WalkReferenceCoupling.backward,
      WalkRecordTransport.encode, Pi.single_apply, mul_apply, conjTranspose_apply,
      Fin.sum_univ_four, one_apply]

lemma raw_right : rawFrame * rawFrameᴴ = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rawFrame, WalkReferenceCoupling.raw, WalkReferenceCoupling.backward,
      WalkRecordTransport.encode, Pi.single_apply, mul_apply, conjTranspose_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]

lemma scale_population : star scale * scale = (1/2 : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold scale
  rw [RestorationResponse.balanced_factor]
  norm_num

theorem frame_left : frameᴴ * frame = 1 := by
  rw [frame, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    raw_left, smul_smul, scale_population]
  norm_num

theorem frame_right : frame * frameᴴ = 1 := by
  rw [frame, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    raw_right, smul_smul, mul_comm scale (star scale), scale_population]
  norm_num

lemma frame_action (x : Ports → ℂ) : frame *ᵥ x = WalkReferenceCoupling.pack x := by
  ext i
  fin_cases i <;>
    simp [frame, rawFrame, scale, WalkReferenceCoupling.pack, WalkReferenceCoupling.raw,
      WalkReferenceCoupling.backward, WalkRecordTransport.encode, mulVec, dotProduct,
      Fintype.sum_sum_type, Pi.single_apply] <;> ring

/-- All four spinor coordinates are retained within existing actual carrier labels. -/
def interface : Matrix C (Fin 4) ℂ := ActualRootRepair.embedding * frameᴴ

theorem isometry : interfaceᴴ * interface = 1 := by
  simp only [interface, conjTranspose_mul, conjTranspose_conjTranspose]
  calc
    (frame * ActualRootRepair.embeddingᴴ) * (ActualRootRepair.embedding * frameᴴ) =
      frame * (ActualRootRepair.embeddingᴴ * ActualRootRepair.embedding) * frameᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ActualRootRepair.isometry, Matrix.mul_one, frame_right]

theorem population (v : Fin 4 → ℂ) : nsq (interface *ᵥ v) = nsq v := by
  unfold nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, isometry, one_mulVec]

/-- The two pre-existing prepared encodings agree through this explicit frame. -/
theorem encoded_packet (live record : Fin 2 → ℂ) :
    interface *ᵥ WalkReferenceCoupling.pack (Sum.elim live record) =
      ActualRootRepair.pack live record := by
  rw [← frame_action, interface, ← mulVec_mulVec, mulVec_mulVec _ frameᴴ frame,
    frame_left, one_mulVec]
  rfl

lemma gamma_frame : gamma * frame = frame * BranchMixerSynthesis.exchange := by
  ext i j
  have h : (gamma * frame) *ᵥ Pi.single j 1 =
      (frame * BranchMixerSynthesis.exchange) *ᵥ Pi.single j 1 := by
    rw [← mulVec_mulVec, frame_action, WalkReferenceCoupling.coupling_intertwining,
      ← mulVec_mulVec, frame_action]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h i

lemma frame_gamma : frameᴴ * gamma = BranchMixerSynthesis.exchange * frameᴴ := by
  have h := congrArg Matrix.conjTranspose gamma_frame
  simpa only [conjTranspose_mul, gamma_hermitian.eq,
    (BranchMixerSynthesis.exchange_relations (n := Fin 2)).1.eq] using h

/-- The walk's local gamma repair is the already available root in this frame. -/
theorem root_gamma : (ActualRootRepair.root.permMatrix ℂ) * interface = interface * gamma := by
  calc
    _ = (ActualRootRepair.root.permMatrix ℂ * ActualRootRepair.embedding) * frameᴴ := by
      simp only [interface, Matrix.mul_assoc]
    _ = ActualRootRepair.embedding * (BranchMixerSynthesis.exchange * frameᴴ) := by
      rw [ActualRootRepair.intertwining, Matrix.mul_assoc]
    _ = interface * gamma := by rw [← frame_gamma]; simp only [interface, Matrix.mul_assoc]

/-- This on-site encoding preserves the comparison functional as well as population. -/
theorem response (v : Fin 4 → ℂ) :
    stateFlag (ActualRootRepair.root.permMatrix ℂ) (interface *ᵥ v) = stateFlag gamma v := by
  have hd : interface *ᵥ v - ActualRootRepair.root.permMatrix ℂ *ᵥ (interface *ᵥ v) =
      interface *ᵥ (v-gamma *ᵥ v) := by
    rw [mulVec_mulVec, root_gamma, ← mulVec_mulVec, Matrix.mulVec_sub]
  rw [stateFlag, hd, population]
  rfl

end PMAction.RootWalkEncoding
