import PMAction.CoherentRecordRestoration
import PMAction.ControllerHamiltonian

/-!
# The common readout of conservative exact restoration

Every unitary reset of live amplitudes into retained record modes has the
same quadratic comparison response on clean-record inputs: half the incoming
squared discrepancy norm. This is independent of record encoding and capacity.
A normalized mean over unit discrepancies is therefore one half; an unnormalized
sum over d unit test directions is d/2. Neither is automatically a per-phase
primitive-work budget.

The readout and supplied flag tariff are inherited from CommonResponse.
Evaluating this response does not supply its physical readout apparatus.
The actual reference state's normalization and physical primitive decomposition
remain operational inputs. In particular the inputs below are coherent
*discrepancies*, not normalized reference-plus-discrepancy preparations.
-/
noncomputable section
namespace PMAction.RestorationResponse
open Matrix CommonResponse
variable {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

/-- The ordinary unitary comparison identity without a unit-norm restriction. -/
lemma response_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (ψ : ι → ℂ) :
    stateFlag U ψ = (nsq ψ - (star ψ ⬝ᵥ (U *ᵥ ψ)).re) / 2 := by
  unfold stateFlag nsq
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, unitary_nsq U hu]
  simp only [Complex.sub_re]
  rw [cross_re]
  ring

/-- Scaling a coherent input scales its response by the squared modulus. -/
lemma response_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (c : ℂ) (ψ : ι → ℂ) :
    stateFlag U (c • ψ) = Complex.normSq c * stateFlag U ψ := by
  unfold stateFlag
  rw [Matrix.mulVec_smul, ← smul_sub, ControllerHamiltonian.nsq_smul]
  ring

/-- The prepared record holds zero discrepancy. -/
def prepare (x : n → ℂ) : n ⊕ r → ℂ := Sum.elim x (fun _ => 0)

omit [DecidableEq n] [DecidableEq r] in
lemma prepare_norm (x : n → ℂ) : nsq (prepare (r := r) x) = nsq x := by
  simp [nsq, dotProduct, prepare, Fintype.sum_sum_type]

/-- Restore every live discrepancy; records may retain any conservative encoding. -/
def Resets (U : Matrix (n ⊕ r) (n ⊕ r) ℂ) : Prop :=
  ∀ x : n → ℂ, ∀ a : n, (U *ᵥ prepare x) (.inl a) = 0

/-- Unitarity and exact restoration fix the comparison response, without fixing
which record encoding implements the repair. -/
theorem reset_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U) (x : n → ℂ) :
    stateFlag U (prepare x) = nsq x / 2 := by
  rw [response_formula U hu, prepare_norm]
  have ho : star (prepare x) ⬝ᵥ (U *ᵥ prepare x) = 0 := by
    simp only [dotProduct, Fintype.sum_sum_type, hr x]
    simp [prepare]
  rw [ho]
  simp

/-- A fixed reference background cancels from the readout displacement. -/
lemma fixed_background_response {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (background ψ : ι → ℂ) (hfix : U *ᵥ background = background) :
    stateFlag U (background + ψ) = stateFlag U ψ := by
  unfold stateFlag
  rw [Matrix.mulVec_add, hfix]
  congr 1
  congr 1
  abel

/-- The same reset response holds above any background fixed by the full operation. -/
theorem reference_reset_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (background : n ⊕ r → ℂ) (hfix : U *ᵥ background = background) (x : n → ℂ) :
    stateFlag U (background + prepare x) = nsq x / 2 := by
  rw [fixed_background_response U background _ hfix, reset_response U hu hr]

/-- Each unit-norm discrepancy gives the same probability in this readout. -/
theorem unit_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (x : n → ℂ) (hx : nsq x = 1) : stateFlag U (prepare x) = 1/2 := by
  rw [reset_response U hu hr, hx]

/-- Net live correction matrix, as distinguished from a primitive work counter. -/
def gain (U : Matrix (n ⊕ r) (n ⊕ r) ℂ) : Matrix n n ℂ := 1 - U.toBlocks₁₁

omit [DecidableEq r] in
lemma reset_live_block (U : Matrix (n ⊕ r) (n ⊕ r) ℂ) (hr : Resets U) :
    U.toBlocks₁₁ = 0 := by
  ext a b
  change U (.inl a) (.inl b) = 0
  have h := hr (Pi.single b 1) a
  simpa [prepare, mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply] using h

omit [DecidableEq r] in
/-- Exact reset fixes the net gain, even before unitarity or a tariff is imposed. -/
theorem reset_gain (U : Matrix (n ⊕ r) (n ⊕ r) ℂ) (hr : Resets U) : gain U = 1 := by
  simp [gain, reset_live_block U hr]

omit [DecidableEq r] in
theorem gain_trace (U : Matrix (n ⊕ r) (n ⊕ r) ℂ) (hr : Resets U) :
    (gain U).trace = (Fintype.card n : ℂ) := by
  rw [reset_gain U hr]
  simp

/-- Squaring the discrepancy scale changes the readout, while the net gain is fixed. -/
theorem scaled_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (c : ℂ) (x : n → ℂ) :
    stateFlag U (prepare (c • x)) = Complex.normSq c * nsq x / 2 := by
  rw [reset_response U hu hr, ControllerHamiltonian.nsq_smul]

section Trials
variable {J : Type*} [Fintype J]

/-- A test family is supplied; it need not be an orthogonal basis. -/
theorem total_unit_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (x : J → n → ℂ) (hx : ∀ j, nsq (x j) = 1) :
    (∑ j, stateFlag U (prepare (x j))) = (Fintype.card J : ℝ) / 2 := by
  simp_rw [unit_response U hu hr _ (hx _)]
  simp
  ring

/-- Normalization removes the number of unit test directions from the mean. -/
theorem weighted_unit_response (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (x : J → n → ℂ) (hx : ∀ j, nsq (x j) = 1)
    (mass : J → ℝ) (hm : ∑ j, mass j = 1) :
    (∑ j, mass j * stateFlag U (prepare (x j))) = 1/2 := by
  simp_rw [unit_response U hu hr _ (hx _)]
  rw [← Finset.sum_mul, hm]
  ring

/-- The inherited flag tariff prices the supplied weighted second moment. -/
theorem weighted_repair_price (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U)
    (x : J → n → ℂ) (mass : J → ℝ) (toll : ℝ) (m : ℕ) :
    (∑ j, mass j * responseCost toll m (stateFlag U (prepare (x j)))) =
      toll * m / 2 * ∑ j, mass j * nsq (x j) := by
  simp_rw [reset_response U hu hr, responseCost]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Trials

/-- For complex coordinate basis tests the total response is half the net-gain trace.
The physical choice and normalization of these tests are not supplied by this identity. -/
theorem basis_response_trace (U : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (hu : U ∈ unitary (Matrix (n ⊕ r) (n ⊕ r) ℂ)) (hr : Resets U) :
    (∑ a : n, stateFlag U (prepare (Pi.single a 1))) = (gain U).trace.re / 2 := by
  rw [gain_trace U hr]
  simpa using total_unit_response U hu hr (fun a : n => Pi.single a 1)
    (fun a => by simp [nsq, dotProduct, Pi.single_apply])

section Exchange
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "X" => BranchMixerSynthesis.exchange (n := n)

lemma exchange_resets : Resets (r := n) X := by
  intro x a
  simp [BranchMixerSynthesis.exchange, prepare, fromBlocks_mulVec]

/-- Price the constructed exchange with the existing readout, not a new trace tariff. -/
theorem exchange_response (x : n → ℂ) :
    stateFlag X (prepare (r := n) x) = nsq x / 2 :=
  reset_response X CoherentRecordRestoration.exchange_unitary exchange_resets x

/-- The same exchange on full reference-plus-discrepancy amplitudes responds
only to their difference. The combined preparation need not have unit norm. -/
theorem prepared_exchange_response (live reference : n → ℂ) :
    stateFlag X (Sum.elim live reference) = nsq (live-reference) / 2 := by
  rw [stateFlag, CoherentRecordRestoration.exchange_action]
  have he : Sum.elim live reference - Sum.elim reference live =
      Sum.elim (live-reference) (-(live-reference)) := by
    ext c
    rcases c with c | c <;> simp
  rw [he, ControllerHamiltonian.nsq_sum]
  have hn (v : n → ℂ) : nsq (-v) = nsq v := by
    simpa using ControllerHamiltonian.nsq_smul (-1) v
  rw [hn]
  ring

/-- If the full coherent preparation is normalized, its response is the
squared discrepancy divided by twice the total live-plus-record population. -/
theorem normalized_prepared_response (c : ℂ) (live reference : n → ℂ)
    (hnorm : nsq (c • Sum.elim live reference) = 1) :
    stateFlag X (c • Sum.elim live reference) =
      nsq (live-reference) / (2 * (nsq live + nsq reference)) := by
  have hn : Complex.normSq c * (nsq live + nsq reference) = 1 := by
    simpa only [ControllerHamiltonian.nsq_smul, ControllerHamiltonian.nsq_sum] using hnorm
  have hne : nsq live + nsq reference ≠ 0 := by
    intro h
    rw [h, mul_zero] at hn
    norm_num at hn
  have hc : Complex.normSq c = 1 / (nsq live + nsq reference) :=
    (eq_div_iff hne).mpr (by simpa using hn)
  rw [response_smul, prepared_exchange_response, hc]
  field_simp

/-- A concrete balanced two-copy amplitude preparation. Its physical preparation
is a separate task; this definition supplies only its normalization. -/
def balanced (live reference : n → ℂ) : n ⊕ n → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • Sum.elim live reference

lemma balanced_factor : Complex.normSq ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1/2 := by
  simp [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

omit [DecidableEq n] in
theorem balanced_norm (live reference : n → ℂ) (hl : nsq live = 1) (hr : nsq reference = 1) :
    nsq (balanced live reference) = 1 := by
  rw [balanced, ControllerHamiltonian.nsq_smul, balanced_factor, ControllerHamiltonian.nsq_sum,
    hl, hr]
  norm_num

/-- For two unit branches, the prepared exchange has the original quarter-norm
comparison response. A raw, unnormalized pair would have twice this response. -/
theorem balanced_response (live reference : n → ℂ) :
    stateFlag X (balanced live reference) = nsq (live-reference) / 4 := by
  rw [balanced, response_smul, prepared_exchange_response, balanced_factor]
  ring

/-- Comparing a balanced transported/reference pair through exchange gives the
same readout as the existing common holonomy comparison, with no free factor. -/
theorem transport_response (U : Matrix n n ℂ) (φ : n → ℂ) :
    stateFlag X (balanced (U *ᵥ φ) φ) = stateFlag U φ := by
  rw [balanced_response, stateFlag]
  have he : U *ᵥ φ - φ = -(φ - U *ᵥ φ) := by abel
  rw [he]
  have hn (v : n → ℂ) : nsq (-v) = nsq v := by
    simpa using ControllerHamiltonian.nsq_smul (-1) v
  rw [hn]

/-- Unitary transport of a unit input makes that concrete balanced pair normalized. -/
theorem transported_pair_norm (U : Matrix n n ℂ)
    (hu : U ∈ unitary (Matrix n n ℂ)) (φ : n → ℂ) (hφ : nsq φ = 1) :
    nsq (balanced (U *ᵥ φ) φ) = 1 := by
  apply balanced_norm _ _ _ hφ
  exact (congrArg Complex.re (unitary_nsq U hu φ)).trans hφ

/-- The return exchange has the same response as the outward exchange. -/
theorem return_response (x : n → ℂ) :
    stateFlag X (X *ᵥ prepare (r := n) x) = nsq x / 2 := by
  rw [stateFlag, CoherentRecordRestoration.twice_undoes]
  have he : X *ᵥ prepare (r := n) x - prepare (r := n) x =
      -(prepare (r := n) x - X *ᵥ prepare (r := n) x) := by abel
  rw [he]
  have hn (v : n ⊕ n → ℂ) : nsq (-v) = nsq v := by
    simpa using ControllerHamiltonian.nsq_smul (-1) v
  rw [hn]
  exact exchange_response x

/-- A whole round trip has zero net response even though its two updates respond. -/
theorem roundtrip_response (x : n → ℂ) :
    stateFlag (X * X) (prepare (r := n) x) = 0 := by
  rw [(BranchMixerSynthesis.exchange_relations (n := n)).2]
  simp [stateFlag, nsq]

/-- Charging each of the two comparisons costs one supplied toll times the
incoming squared discrepancy; charging only the net identity costs zero. -/
theorem roundtrip_instruction_price (x : n → ℂ) (toll : ℝ) (m : ℕ) :
    responseCost toll m (stateFlag X (prepare (r := n) x)) +
        responseCost toll m (stateFlag X (X *ᵥ prepare (r := n) x)) =
      toll * m * nsq x := by
  rw [exchange_response, return_response]
  unfold responseCost
  ring

end Exchange
end PMAction.RestorationResponse
