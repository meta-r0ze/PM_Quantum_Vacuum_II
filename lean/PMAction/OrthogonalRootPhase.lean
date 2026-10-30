import PMAction.CarrierWeyl
import PMAction.RootTransferPhase

/-! A common odd-sector phase using four actual root transfers, rather than
postulating a lazy transfer for a composite antipodal instruction. The common
rate, phase time and physical admission of reconstructed phases remain inputs. -/
noncomputable section
namespace PMAction.OrthogonalRootPhase
open Matrix CarrierEvents CarrierParity

/-- Four mutually orthogonal norm-two D4 roots. -/
def roots : Fin 4 → (Fin 4 → ℤ) :=
  ![![1,-1,0,0], ![1,1,0,0], ![0,0,1,-1], ![0,0,1,1]]

def event (c : Fin 3) (j : Fin 4) : Equiv.Perm (Carrier c) :=
  if j=0 then CarrierWeyl.simple c 0
  else if j=1 then CarrierWeyl.lookup c 0 * CarrierWeyl.simple c 3 * CarrierWeyl.lookup c 0
  else if j=2 then CarrierWeyl.simple c 2
  else CarrierWeyl.simple c 3

lemma roots_norm : ∀ j, PMArch.ChannelSymmetry.dot4 (roots j) (roots j)=2 := by decide +kernel
lemma event_is_root : ∀ c j (v : Carrier c), vector (event c j v)=
    PMArch.ChannelSymmetry.refl (roots j) (vector v) := by decide +kernel
lemma event_involutive : ∀ c j, Function.Involutive (event c j) := by
  change ∀ c j (v : Carrier c), event c j (event c j v)=v
  decide +kernel

def realMatrix : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ := ![
  !![0,1,0,0;1,0,0,0;0,0,1,0;0,0,0,1],
  !![0,-1,0,0;-1,0,0,0;0,0,1,0;0,0,0,1],
  !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0],
  !![1,0,0,0;0,1,0,0;0,0,0,-1;0,0,-1,0]]
def R (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun i k => (realMatrix j i k : ℂ)

lemma coordinates : ∀ c j (v : Carrier c) (i : Fin 4),
    vector (event c j v) i = ∑ k, vector v k * realMatrix j k i := by decide +kernel

lemma intertwining (c : Fin 3) (j : Fin 4) :
    (event c j).permMatrix ℂ * embedding c = embedding c * R j := by
  ext v i
  change ((event c j).permMatrix ℂ *ᵥ (fun w => embedding c w i)) v = _
  rw [Matrix.permMatrix_mulVec]
  change scale * (vector (event c j v) i : ℂ)=_
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (coordinates c j v i)
  push_cast at hg
  rw [hg,Finset.mul_sum]
  simp only [mul_apply,embedding,R]
  apply Finset.sum_congr rfl
  intro k _
  ring

def factor (j : Fin 4) (q : ℂ) := InvolutionSpectral.plus (R j) + q • InvolutionSpectral.minus (R j)

set_option maxHeartbeats 1000000 in
lemma factors (q : ℂ) : factor 0 q * factor 1 q * factor 2 q * factor 3 q = q • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [factor, InvolutionSpectral.plus, InvolutionSpectral.minus, R, realMatrix,
      mul_apply, Fin.sum_univ_four] <;> ring

lemma phase_intertwining (c : Fin 3) (j : Fin 4) (p t : ℝ) :
    RootTransferPhase.phase (event c j) p t * embedding c =
      embedding c * factor j (Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I)) := by
  rw [RootTransferPhase.phase_formula _ (event_involutive c j)]
  simp only [factor, InvolutionSpectral.plus, InvolutionSpectral.minus,
    Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, intertwining]

def phase (c : Fin 3) (p t : ℝ) :=
  RootTransferPhase.phase (event c 0) p t * RootTransferPhase.phase (event c 1) p t *
    RootTransferPhase.phase (event c 2) p t * RootTransferPhase.phase (event c 3) p t

/-- Four primitive-root phase evolutions have exactly one common phase on the
coordinate sector. No transfer kernel for the twelve-root composite is needed. -/
theorem phase_sector (c : Fin 3) (p t : ℝ) : phase c p t * embedding c =
    Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I) • embedding c := by
  have hpull (A B : Matrix (Carrier c) (Carrier c) ℂ)
      (A' B' : Matrix (Fin 4) (Fin 4) ℂ)
      (ha : A*embedding c=embedding c*A') (hb : B*embedding c=embedding c*B') :
      (A*B)*embedding c=embedding c*(A'*B') := by
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  have h01 := hpull _ _ _ _ (phase_intertwining c 0 p t) (phase_intertwining c 1 p t)
  have h012 := hpull _ _ _ _ h01 (phase_intertwining c 2 p t)
  have h0123 := hpull _ _ _ _ h012 (phase_intertwining c 3 p t)
  change _ = _ at h0123
  rw [phase, h0123, factors, Matrix.mul_smul, Matrix.mul_one]

end PMAction.OrthogonalRootPhase
