import PMAction.NativePacketLinks
import PMAction.CommonResponse

/-! The root-response cost operator on actual carrier labels and its intrinsic
packet compression. Coherent evolution by these Hermitian operators uses the
existing amplitude/spectral dynamics contract; it is not asserted to be a
permutation event, nor is response cost identified with the full event ledger. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NativeRootGenerators
open Matrix CarrierEvents CarrierParity NativePacketLinks

lemma root_square (c : Fin 3) (j : Fin 4) : root c j*root c j=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro v
  apply Subtype.ext
  exact CarrierWeyl.simple_twice j v.1
lemma root_inverse (c : Fin 3) (j : Fin 4) : (root c j)⁻¹=root c j :=
  inv_eq_of_mul_eq_one_left (root_square c j)
lemma physical_hermitian (c : Fin 3) (j : Fin 4) : (physical c (root c j)).IsHermitian := by
  change (physical c (root c j))ᴴ=physical c (root c j)
  rw [← physical_star,root_inverse]
lemma packet_hermitian (c : Fin 3) (j : Fin 4) : (link c (root c j)).IsHermitian := by
  change (link c (root c j))ᴴ=link c (root c j)
  rw [← link_star,root_inverse]

def cost (c : Fin 3) (j : Fin 4) : Matrix (Carrier c) (Carrier c) ℂ := 1-physical c (root c j)
def packetCost (c : Fin 3) (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := 1-link c (root c j)

lemma cost_hermitian (c : Fin 3) (j : Fin 4) : (cost c j).IsHermitian :=
  isHermitian_one.sub (physical_hermitian c j)
lemma packetCost_hermitian (c : Fin 3) (j : Fin 4) : (packetCost c j).IsHermitian :=
  isHermitian_one.sub (packet_hermitian c j)

/-- The response fixes the quadratic cost operator, including its factor two. -/
theorem root_response (c : Fin 3) (j : Fin 4) (ψ : Carrier c → ℂ) :
    (star ψ ⬝ᵥ (cost c j *ᵥ ψ)).re = 2*CommonResponse.stateFlag (physical c (root c j)) ψ := by
  have hw := CommonResponse.wilson_form _ (physical_unitary c (root c j)) ψ
  have he : (2-physical c (root c j)-(physical c (root c j))ᴴ)=(2:ℂ) • cost c j := by
    rw [(physical_hermitian c j).eq, ← one_add_one_eq_two]
    unfold cost
    rw [two_smul]
    abel
  rw [he,smul_mulVec,dotProduct_smul,smul_eq_mul] at hw
  have h2 (z : ℂ) : ((2 : ℂ) * z).re = 2 * z.re := by simp [Complex.mul_re]
  rw [h2] at hw
  linarith

lemma cost_observed (c : Fin 3) (j : Fin 4) :
    NativeObservation.Obs (embedding c) (cost c j) (packetCost c j) :=
  NativeObservation.sub NativeObservation.one (observed c (root c j))

def rootMatrixZ (j : Fin 4) (a b : Fin 4) : ℤ :=
  PMSubstrate.ChannelSymmetry.refl (PMSubstrate.ChannelSymmetry.simple j) (Pi.single b 1) a

def rootMatrix (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun a b => (rootMatrixZ j a b : ℂ)

set_option maxHeartbeats 2000000 in
lemma root_coordinates : ∀ (c : Fin 3) (j : Fin 4) (v : Carrier c) (i : Fin 4),
    vector (CarrierWeyl.simple c j v) i=∑ k,rootMatrixZ j k i*vector v k := by decide +kernel

/-- The link of each native simple root is derived in the existing coordinate
frame. The integer certificate is independent of any measured constant. -/
theorem root_link (c : Fin 3) (j : Fin 4) : link c (root c j)=rootMatrix j := by
  have hi : physical c (root c j)*embedding c=embedding c*rootMatrix j := by
    ext v i
    change (physical c (root c j) *ᵥ (fun w => embedding c w i)) v = _
    rw [physical,permMatrix_mulVec]
    change scale*(vector (CarrierWeyl.simple c j v) i : ℂ)=_
    have hg := congrArg (fun z : ℤ => (z : ℂ)) (root_coordinates c j v i)
    push_cast at hg
    rw [hg,Finset.mul_sum]
    simp only [Matrix.mul_apply,embedding,rootMatrix]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold link
  rw [Matrix.mul_assoc,hi,← Matrix.mul_assoc,isometry,Matrix.one_mul]

/-- Two root-cost generators already fail to commute. Native root transport is
not restricted to flat frame relabelings. -/
theorem noncommuting_costs (c : Fin 3) :
    (packetCost c 0*packetCost c 1-packetCost c 1*packetCost c 0) 0 2=1 := by
  norm_num [packetCost,root_link,rootMatrix,rootMatrixZ,Matrix.mul_apply,Matrix.sub_apply,
    Matrix.one_apply,PMSubstrate.ChannelSymmetry.refl,PMSubstrate.ChannelSymmetry.simple,
    PMSubstrate.ChannelSymmetry.dot4,Fin.sum_univ_four,Pi.single_apply]

end PMAction.NativeRootGenerators
