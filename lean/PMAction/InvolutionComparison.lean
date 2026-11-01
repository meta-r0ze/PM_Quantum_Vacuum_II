import PMAction.BranchMixerSynthesis
import PMAction.RootTransferPhase

/-!
# Comparison of root phases without a universal branch marker

For a supplied involution R, compare its spectral phase using quarter phases
of branch exchange and of the controlled R itself. No independent branch Z
gate appears. This is a coherent circuit identity, not a branch allocation or
primitive-price theorem. Admission of the reconstructed phases remains explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.InvolutionComparison
open Matrix ComparisonFactorization BranchMixerSynthesis
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

def phase (R : M) (z : ℂ) : M := InvolutionSpectral.plus R + z • InvolutionSpectral.minus R

omit [Fintype n] in
theorem phase_ctrl (R : M) (z : ℂ) : phase (ctrl R) z = ctrl (phase R z) := by
  simp only [phase, InvolutionSpectral.plus, InvolutionSpectral.minus, ctrl,
    ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

omit [Fintype n] in
theorem exchange_phase (z : ℂ) : phase (exchange (n := n)) z =
    fromBlocks (((1+z)/2) • (1 : M)) (((1-z)/2) • (1 : M))
      (((1-z)/2) • (1 : M)) (((1+z)/2) • (1 : M)) := by
  simp only [phase, InvolutionSpectral.plus, InvolutionSpectral.minus, exchange,
    ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

/-- Five phase operations suffice for any spectral phase of an involution.
The two inverse quarter phases are counted operations, not discarded phases. -/
theorem circuit (R : M) (hR : R * R = 1) (z : ℂ) :
    phase (ctrl R) (-Complex.I) * phase exchange (-Complex.I) * ctrl (phase R z) *
      phase exchange Complex.I * phase (ctrl R) Complex.I =
      CoherentComparisonRepair.compare (phase R z) := by
  have h := InvolutionSpectral.products R hR
  rw [phase_ctrl, phase_ctrl, exchange_phase, exchange_phase]
  simp only [ctrl, fromBlocks_multiply, CoherentComparisonRepair.compare,
    CoherentComparisonRepair.plus, CoherentComparisonRepair.minus]
  rw [fromBlocks_inj]
  have hsum := InvolutionSpectral.sum R
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [phase, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      smul_zero, zero_add, add_zero, h.1, h.2.1, h.2.2.1, h.2.2.2] <;>
    rw [← hsum] <;>
    match_scalars <;> ring_nf <;> norm_num <;> ring

theorem phase_mul (R : M) (hR : R * R = 1) (z w : ℂ) :
    phase R z * phase R w = phase R (z * w) := by
  have h := InvolutionSpectral.products R hR
  simp only [phase, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    h.1, h.2.1, h.2.2.1, h.2.2.2, smul_zero, add_zero, zero_add]
  rw [mul_comm w z]

theorem phase_pow (R : M) (hR : R * R = 1) (z : ℂ) (k : ℕ) :
    (phase R z)^k = phase R (z^k) := by
  induction k with
  | zero => simpa [phase] using (InvolutionSpectral.sum R).symm
  | succ k ih => rw [pow_succ, ih, phase_mul R hR, pow_succ]

/-- An inverse quarter can be three forward quarters: its duration and price
must then include all three calls. -/
theorem inverse_quarter (R : M) (hR : R * R = 1) :
    (phase R (-Complex.I))^3 = phase R Complex.I := by
  rw [phase_pow R hR]
  congr 1
  norm_num [pow_succ, Complex.I_mul_I]

def stage (R : M) (z : ℂ) : List (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  [phase (ctrl R) (-Complex.I), phase exchange (-Complex.I), phase (ctrl R) z,
    phase exchange Complex.I, phase (ctrl R) Complex.I]

theorem stage_correct (R : M) (hR : R * R = 1) (z : ℂ) :
    (stage R z).prod = CoherentComparisonRepair.compare (phase R z) := by
  simpa only [stage, List.prod_cons, List.prod_nil, mul_one, phase_ctrl,
    Matrix.mul_assoc] using circuit R hR z

/-- The inverse calls can be expanded to forward quarters explicitly. -/
def forwardStage (R : M) (z : ℂ) : List (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  [phase (ctrl R) (-Complex.I), phase exchange (-Complex.I), phase (ctrl R) z] ++
    List.replicate 3 (phase exchange (-Complex.I)) ++
    List.replicate 3 (phase (ctrl R) (-Complex.I))

omit [Fintype n] in
theorem forward_calls (R : M) (z : ℂ) : (forwardStage R z).length = 9 := by
  simp [forwardStage]

theorem forward_correct (R : M) (hR : R * R = 1) (z : ℂ) :
    (forwardStage R z).prod = CoherentComparisonRepair.compare (phase R z) := by
  have hsquare : ctrl R * ctrl R = 1 := by
    simp [ctrl, fromBlocks_multiply, hR, fromBlocks_one]
  simp only [forwardStage, List.prod_append, List.prod_replicate, List.prod_cons,
    List.prod_nil, mul_one, inverse_quarter _ hsquare, inverse_quarter _ exchange_relations.2]
  rw [phase_ctrl R z]
  simpa only [Matrix.mul_assoc] using circuit R hR z

/-- The stages compose even when their different root involutions do not
commute. No common global branch mixer is assumed between stages. -/
theorem word_correct (word : List (M × ℂ))
    (h : ∀ s ∈ word, s.1 * s.1 = 1) :
    (word.flatMap (fun s => stage s.1 s.2)).prod =
      CoherentComparisonRepair.compare ((word.map (fun s => phase s.1 s.2)).prod) := by
  induction word with
  | nil => simp [CoherentComparisonRepair.compare_one]
  | cons s word ih =>
    simp only [List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons]
    rw [stage_correct s.1 (h s (by simp)) s.2, ih (fun t ht => h t (by simp [ht])),
      CoherentComparisonRepair.compare_mul]

/-- Link the spectral phase used here to the existing reconstructed native
root evolution, retaining its supplied attempt rate and time. -/
theorem reconstructed (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) :
    RootTransferPhase.phase e p t =
      phase (e.permMatrix ℂ) (Complex.exp (-(RootTransferPhase.gap p * t : ℝ) * Complex.I)) :=
  RootTransferPhase.phase_formula e he p t

theorem reconstructed_quarter (e : Equiv.Perm n) (he : Function.Involutive e)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.phase e p (RootTransferPhase.quarterTime p) =
      phase (e.permMatrix ℂ) (-Complex.I) := by
  rw [reconstructed e he]
  have ht : RootTransferPhase.gap p * RootTransferPhase.quarterTime p = Real.pi/2 := by
    unfold RootTransferPhase.quarterTime
    field_simp [ne_of_gt (RootTransferPhase.gap_positive p hp hp1)]
  rw [ht]
  congr 1
  rw [Complex.exp_mul_I]
  norm_num [← Complex.ofReal_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

def controlled (e : Equiv.Perm n) : Equiv.Perm (n ⊕ n) :=
  Equiv.sumCongr (Equiv.refl n) e

omit [Fintype n] [DecidableEq n] in
theorem controlled_involutive (e : Equiv.Perm n) (he : Function.Involutive e) :
    Function.Involutive (controlled e) := by
  intro v
  rcases v with v | v
  · rfl
  · exact congrArg Sum.inr (he v)

/-- The controlled signal is a phase of the controlled permutation itself,
not an additional arbitrary controlled-unitary primitive. -/
theorem controlled_reconstruction (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) :
    RootTransferPhase.phase (controlled e) p t = ctrl (RootTransferPhase.phase e p t) := by
  rw [reconstructed _ (controlled_involutive e he), reconstructed e he]
  change phase (Equiv.Perm.permMatrix ℂ (Equiv.sumCongr (Equiv.refl n) e)) _ = _
  rw [← ctrl_permutation, phase_ctrl]

omit [Fintype n] in
theorem exchange_permutation :
    exchange (n := n) = Equiv.Perm.permMatrix ℂ (Equiv.sumComm n n) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [exchange, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]

/-- Only the two native quarter-phase controls and the required controlled
signal phase need admission. The inverse quarters follow from three forward
quarters by monoid closure; no branch-marker Z or arbitrary rotation closure
is assumed here. Prices and register placement remain separate obligations. -/
theorem admitted (S : Submonoid (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (R : M) (hR : R * R = 1) (z : ℂ)
    (hD : phase (ctrl R) (-Complex.I) ∈ S)
    (hX : phase exchange (-Complex.I) ∈ S)
    (hU : phase (ctrl R) z ∈ S) : CoherentComparisonRepair.compare (phase R z) ∈ S := by
  have hsquare : ctrl R * ctrl R = 1 := by
    simp [ctrl, fromBlocks_multiply, hR, fromBlocks_one]
  have hd : phase (ctrl R) Complex.I ∈ S := by
    rw [← inverse_quarter _ hsquare]
    exact S.pow_mem hD 3
  have hx : phase (exchange (n := n)) Complex.I ∈ S := by
    rw [← inverse_quarter _ exchange_relations.2]
    exact S.pow_mem hX 3
  have hp := S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem hD hX) hU) hx) hd
  have hc : phase (ctrl R) (-Complex.I) * phase exchange (-Complex.I) * phase (ctrl R) z *
      phase exchange Complex.I * phase (ctrl R) Complex.I =
        CoherentComparisonRepair.compare (phase R z) := by
    rw [phase_ctrl R z]
    exact circuit R hR z
  rwa [hc] at hp

theorem phase_unitary (R : M) (hR : R * R = 1) (hH : R.IsHermitian)
    (z : ℂ) (hz : star z * z = 1) : phase R z ∈ unitary M := by
  have hs : (phase R z)ᴴ = phase R (star z) := by
    simp [phase, InvolutionSpectral.plus, InvolutionSpectral.minus,
      conjTranspose_add, conjTranspose_sub, conjTranspose_smul, hH.eq]
  have hz' : z * star z = 1 := by rwa [mul_comm]
  constructor
  · change (phase R z)ᴴ * phase R z = 1
    rw [hs, phase_mul R hR, hz]
    simpa only [phase, one_smul] using InvolutionSpectral.sum R
  · change phase R z * (phase R z)ᴴ = 1
    rw [hs, phase_mul R hR, hz']
    simpa only [phase, one_smul] using InvolutionSpectral.sum R

end PMAction.InvolutionComparison
