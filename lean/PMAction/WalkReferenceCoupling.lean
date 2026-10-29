import PMAction.WalkRecordTransport
import PMAction.BranchPulseContract

/-!
# Reference repair within the concrete walk's internal modes

The two velocity channels encode live and retained-record doublets at one
spatial site. The existing gamma phase gate exchanges these channels exactly.
The preparation of a pure forward reference is supplied explicitly by a
quarter beta pulse on a specified basis seed. Neither this seed's supply nor
the admissibility and primitive price of the on-site pulse is inferred from
the word persistence. These logical packet coordinates are encoded in spinor
modes; identification with a weak-isospin doublet and its gauge action is
not established merely by their common dimension.
-/
noncomputable section
namespace PMAction.WalkReferenceCoupling
open Matrix ConcreteFermion CommonResponse

abbrev Doublet := Fin 2 → ℂ
abbrev Modes := Fin 2 ⊕ Fin 2

def backward (u : Doublet) : Fin 4 → ℂ := ![u 0, u 1, -Complex.I*u 0, Complex.I*u 1]

def raw (ψ : Modes → ℂ) : Fin 4 → ℂ :=
  backward (fun a => ψ (.inl a)) + WalkRecordTransport.encode (fun a => ψ (.inr a))

def pack (ψ : Modes → ℂ) : Fin 4 → ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) • raw ψ

/-- Reconstruction of twice each modal amplitude from the unscaled spinor. -/
def recover (v : Fin 4 → ℂ) : Modes → ℂ :=
  Sum.elim ![v 0 + Complex.I*v 2, v 1 - Complex.I*v 3]
    ![v 0 - Complex.I*v 2, v 1 + Complex.I*v 3]

lemma recover_raw (ψ : Modes → ℂ) : recover (raw ψ) = (2 : ℂ) • ψ := by
  ext c
  rcases c with a | a <;> fin_cases a <;>
    simp [recover, raw, backward, WalkRecordTransport.encode] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

lemma raw_injective : Function.Injective raw := by
  intro ψ φ h
  have hh := congrArg recover h
  rw [recover_raw, recover_raw] at hh
  funext c
  have hc := congrFun hh c
  change (2 : ℂ) * ψ c = 2 * φ c at hc
  linear_combination hc / 2

lemma pack_injective : Function.Injective pack := by
  intro ψ φ h
  apply raw_injective
  have hs : ((1 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have hh := congrArg (fun v : Fin 4 → ℂ => (((1 / Real.sqrt 2 : ℝ) : ℂ)⁻¹) • v) h
  simpa [pack, smul_smul, hs] using hh

lemma raw_norm (ψ : Modes → ℂ) : nsq (raw ψ) = 2 * nsq ψ := by
  simp [LinkExpansion.nsq_eq, raw, backward, WalkRecordTransport.encode,
    Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_two,
    Complex.normSq_apply]
  ring

/-- Both channels and all retained distinctions share one conserved amplitude norm. -/
theorem pack_norm (ψ : Modes → ℂ) : nsq (pack ψ) = nsq ψ := by
  rw [pack, ControllerHamiltonian.nsq_smul, RestorationResponse.balanced_factor, raw_norm]
  ring

lemma gamma_forward (u : Doublet) :
    gamma *ᵥ WalkRecordTransport.encode u = backward u := by
  ext a
  fin_cases a <;> simp [gamma, WalkRecordTransport.encode, backward, mulVec, dotProduct,
    Fin.sum_univ_four]

lemma gamma_backward (u : Doublet) :
    gamma *ᵥ backward u = WalkRecordTransport.encode u := by
  ext a
  fin_cases a <;> simp [gamma, WalkRecordTransport.encode, backward, mulVec, dotProduct,
    Fin.sum_univ_four]

/-- A diagonal gate in the spinor coordinates is the exact live/record exchange
in the explicitly prepared velocity-channel encoding. -/
theorem coupling_intertwining (ψ : Modes → ℂ) :
    gamma *ᵥ pack ψ = pack (BranchMixerSynthesis.exchange *ᵥ ψ) := by
  rw [pack, Matrix.mulVec_smul]
  unfold raw
  rw [Matrix.mulVec_add, gamma_backward, gamma_forward]
  congr 1
  rw [BranchMixerSynthesis.exchange, fromBlocks_mulVec]
  simp [raw, add_comm]

theorem gamma_unitary : gamma ∈ unitary Spin := by
  constructor <;> simpa only [star_eq_conjTranspose, gamma_hermitian.eq] using gamma_square

/-- Exact repair with a reference packet and retention of the entire old input. -/
theorem repair (live reference : Doublet) :
    gamma *ᵥ pack (Sum.elim live reference) = pack (Sum.elim reference live) := by
  rw [coupling_intertwining, CoherentRecordRestoration.exchange_action]

/-- There is no hidden deletion in the concrete-spinor implementation. -/
theorem input_retained (reference : Doublet) :
    Function.Injective (fun live => gamma *ᵥ pack (Sum.elim live reference)) := by
  intro live other h
  change gamma *ᵥ pack (Sum.elim live reference) = gamma *ᵥ pack (Sum.elim other reference) at h
  rw [repair, repair] at h
  have he := pack_injective h
  funext a
  exact congrFun he (.inr a)

lemma pack_sub (ψ φ : Modes → ℂ) : pack (ψ - φ) = pack ψ - pack φ := by
  ext a
  fin_cases a <;> simp [pack, raw, backward, WalkRecordTransport.encode] <;> ring

/-- The coupling's common response is the already derived repair response. -/
theorem coupling_response (live reference : Doublet) :
    stateFlag gamma (pack (Sum.elim live reference)) = nsq (live-reference) / 2 := by
  rw [stateFlag, coupling_intertwining, ← pack_sub, pack_norm]
  exact RestorationResponse.prepared_exchange_response live reference

lemma forward_backward_zero (u : Doublet) :
    (beta * LocalUnitary.coefficient 2) *ᵥ backward u = 0 := by
  ext a
  fin_cases a <;>
    norm_num [backward, LocalUnitary.coefficient, beta, alpha, mul_apply,
      mulVec, dotProduct, Fin.sum_univ_four] <;> ring_nf <;> simp [Complex.I_sq]

lemma channel_complement :
    beta * LocalUnitary.coefficient 2 + beta * (LocalUnitary.coefficient 2)ᴴ = 1 := by
  have hc : LocalUnitary.coefficient 2 + (LocalUnitary.coefficient 2)ᴴ = beta := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [LocalUnitary.coefficient, beta, alpha, conjTranspose_apply] <;> ring
  rw [← mul_add, hc, beta_square]

lemma reverse_backward (u : Doublet) :
    (beta * (LocalUnitary.coefficient 2)ᴴ) *ᵥ backward u = backward u := by
  have h := congrArg (fun A => A *ᵥ backward u) channel_complement
  simpa only [add_mulVec, forward_backward_zero, zero_add, one_mulVec] using h

lemma forward_packet (live record : Doublet) :
    (beta * LocalUnitary.coefficient 2) *ᵥ pack (Sum.elim live record) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) • WalkRecordTransport.encode record := by
  rw [pack, Matrix.mulVec_smul, raw, Matrix.mulVec_add, forward_backward_zero,
    WalkRecordTransport.forward_local, zero_add]
  rfl

lemma reverse_packet (live record : Doublet) :
    (beta * (LocalUnitary.coefficient 2)ᴴ) *ᵥ pack (Sum.elim live record) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) • backward live := by
  rw [pack, Matrix.mulVec_smul, raw, Matrix.mulVec_add, reverse_backward,
    WalkRecordTransport.reverse_local_zero, add_zero]
  rfl

/-- Omitting the local coupling is correct only when no discrepancy is present. -/
theorem idle_repair_iff (live reference : Doublet) :
    pack (Sum.elim live reference) = pack (Sum.elim reference live) ↔ live = reference := by
  constructor
  · intro h
    have hh := pack_injective h
    funext a
    exact congrFun hh (.inl a)
  · rintro rfl
    rfl

/-- The common comparison functional is unchanged by the faithful internal encoding. -/
theorem response_intertwining (ψ : Modes → ℂ) :
    stateFlag gamma (pack ψ) = stateFlag BranchMixerSynthesis.exchange ψ := by
  rw [stateFlag, coupling_intertwining, ← pack_sub, pack_norm]
  rfl

/-- Balanced live/reference inputs give normalized per-trial pricing when each branch is unit. -/
theorem balanced_coupling_response (live reference : Doublet) :
    stateFlag gamma (pack (RestorationResponse.balanced live reference)) =
      nsq (live-reference) / 4 := by
  rw [response_intertwining, RestorationResponse.balanced_response]

/-- The normalized coupling's readout charge, under the existing supplied flag tariff. -/
theorem balanced_coupling_price (live reference : Doublet) (toll : ℝ) (m : ℕ) :
    responseCost toll m (stateFlag gamma (pack (RestorationResponse.balanced live reference))) =
      toll * m / 4 * nsq (live-reference) := by
  rw [balanced_coupling_response]
  unfold responseCost
  ring

/-- The packet used for this preparation is specified, not selected from all
possible vacuum preparations by the existence of this construction. -/
def reference : Doublet := ![1,0]
def seed : Fin 4 → ℂ := ![1,0,0,0]

def preparation : Spin := LocalUnitary.rotation beta (Real.pi/4)

theorem preparation_unitary : preparation ∈ unitary Spin :=
  LocalUnitary.rotation_unitary beta _ beta_hermitian beta_square

/-- A concrete existing beta rotation prepares the forward reference channel. -/
theorem prepares_forward :
    preparation *ᵥ seed = pack (Sum.elim (fun _ => 0) reference) := by
  have hs : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  ext a
  fin_cases a <;>
    simp [preparation, LocalUnitary.rotation, seed, reference, pack, raw, backward,
      WalkRecordTransport.encode, beta, mulVec, dotProduct, Fin.sum_univ_four,
      Real.cos_pi_div_four, Real.sin_pi_div_four, hs]
  all_goals ring

/-- Vanishing backward-channel amplitude is the task constraint for the incoming record. -/
def PureForward (v : Fin 4 → ℂ) : Prop := ∀ a, recover v (.inl a) = 0

lemma beta_pulse_forward_iff (t : ℝ) :
    PureForward (LocalUnitary.rotation beta t *ᵥ seed) ↔ Real.cos t = Real.sin t := by
  simp [PureForward, recover, LocalUnitary.rotation, seed, beta, mulVec, dotProduct,
    Fin.sum_univ_four, Fin.forall_fin_two, Complex.ext_iff]
  simpa only [Complex.cos_ofReal_re, Complex.sin_ofReal_re, sub_eq_add_neg] using
    (sub_eq_zero : Real.cos t - Real.sin t = 0 ↔ Real.cos t = Real.sin t)

/-- Among first-quadrant beta pulses, pure forward transport forces the quarter angle. -/
theorem preparation_angle_forced (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ Real.pi/2)
    (hf : PureForward (LocalUnitary.rotation beta t *ᵥ seed)) : t = Real.pi/4 := by
  have he := (beta_pulse_forward_iff t).mp hf
  apply (BranchPulseContract.balanced_angle_iff t h0 h1).mp
  have ht := Real.sin_sq_add_cos_sq t
  rw [he] at ht
  linarith

theorem seed_norm : nsq seed = 1 := by simp [seed, LinkExpansion.nsq_eq, Fin.sum_univ_four]

/-- The supplied seed has a concrete zero-mode representative before preparation. -/
theorem seed_zero_mode : hamiltonian 0 0 *ᵥ Sum.elim seed (fun _ => 0) = 0 := by
  rw [kernel_coordinates]
  simp [seed]

theorem prepared_norm : nsq (preparation *ᵥ seed) = 1 :=
  (congrArg Complex.re (unitary_nsq preparation preparation_unitary seed)).trans seed_norm

/-- Preparing the coherent record has a nonzero comparison response; the
operation is not silently assigned zero preparation cost. -/
theorem preparation_response :
    stateFlag preparation seed = (1 - Real.cos (Real.pi/4)) / 2 := by
  rw [RestorationResponse.response_formula preparation preparation_unitary, seed_norm]
  simp [preparation, LocalUnitary.rotation, seed, beta, mulVec, dotProduct, Fin.sum_univ_four]

end PMAction.WalkReferenceCoupling
