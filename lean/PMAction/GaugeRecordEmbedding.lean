import PMAction.WalkReferenceCoupling

/-!
# Gauge-compatible record modes with a separate payload index

Spinor and internal gauge coordinates are distinct. An explicit two-channel
control encoding carries arbitrary payloads in an additional finite index.
It is isometric, intertwines every common payload gauge matrix, and realizes
record exchange by gamma on the spinor factor. No gauge group or E8 realization
of the added modes is selected merely by these tensor identities.
-/
noncomputable section
namespace PMAction.GaugeRecordEmbedding
open Matrix ConcreteFermion
open scoped Kronecker

/-- Unscaled backward/forward controls, with a fixed spin polarization. -/
def rawCarrier : Matrix (Fin 4) (Fin 2) ℂ := !![1,1; 0,0; -Complex.I,Complex.I; 0,0]
def carrier : Matrix (Fin 4) (Fin 2) ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ) • rawCarrier

def exchange : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

lemma raw_isometry : rawCarrierᴴ * rawCarrier = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rawCarrier, mul_apply, conjTranspose_apply, Fin.sum_univ_four]

lemma carrier_isometry : carrierᴴ * carrier = 1 := by
  have hr : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1/2 := by
    simpa only [Complex.normSq_ofReal] using RestorationResponse.balanced_factor
  have hc : star ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1/2 : ℂ) := by
    calc
      _ = ((1 / Real.sqrt 2 * (1 / Real.sqrt 2) : ℝ) : ℂ) := by simp
      _ = ((1/2 : ℝ) : ℂ) := congrArg Complex.ofReal hr
      _ = 1/2 := by norm_num
  rw [carrier, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    raw_isometry, smul_smul, hc]
  norm_num

lemma raw_exchange : gamma * rawCarrier = rawCarrier * exchange := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gamma, rawCarrier, exchange, mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

lemma carrier_exchange : gamma * carrier = carrier * exchange := by
  simp only [carrier, Matrix.mul_smul, Matrix.smul_mul, raw_exchange]

/-- Rectangular tensor actions preserve a separated control/payload input. -/
lemma tensor_packet {a b c d : Type*} [Fintype b] [Fintype d]
    (A : Matrix a b ℂ) (B : Matrix c d ℂ) (u : b → ℂ) (v : d → ℂ) (i : a) (j : c) :
    ((A ⊗ₖ B) *ᵥ (fun p => u p.1 * v p.2)) (i,j) = (A *ᵥ u) i * (B *ᵥ v) j := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma record_column : carrier *ᵥ Pi.single (1 : Fin 2) 1 =
    WalkReferenceCoupling.preparation *ᵥ WalkReferenceCoupling.seed := by
  rw [WalkReferenceCoupling.prepares_forward]
  ext a
  fin_cases a <;> simp [carrier, rawCarrier, WalkReferenceCoupling.pack,
    WalkReferenceCoupling.raw, WalkReferenceCoupling.backward, WalkRecordTransport.encode,
    WalkReferenceCoupling.reference, Matrix.col_apply]

section Payload
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two live/record control labels times payload labels embed in spinor times payload modes. -/
def embedding : Matrix (Fin 4 × n) (Fin 2 × n) ℂ := carrier ⊗ₖ (1 : Matrix n n ℂ)

theorem embedding_isometry : (embedding (n := n))ᴴ * embedding (n := n) =
    (1 : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) := by
  simp [embedding, conjTranspose_kronecker, ← mul_kronecker_mul, carrier_isometry]

theorem embedding_norm (ψ : Fin 2 × n → ℂ) :
    CommonResponse.nsq (embedding *ᵥ ψ) = CommonResponse.nsq ψ := by
  unfold CommonResponse.nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, embedding_isometry, one_mulVec]

theorem embedding_injective : Function.Injective (fun ψ : Fin 2 × n → ℂ => embedding *ᵥ ψ) := by
  intro ψ φ h
  have hh := congrArg (fun v => (embedding (n := n))ᴴ *ᵥ v) h
  simpa only [mulVec_mulVec, embedding_isometry, one_mulVec] using hh

/-- Every payload action, including an actual supplied gauge representation, intertwines. -/
theorem gauge_intertwining (G : Matrix n n ℂ) :
    ((1 : Spin) ⊗ₖ G) * embedding = embedding * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G) := by
  simp [embedding, ← mul_kronecker_mul]

/-- The actual gamma operator exchanges records without acting on payload gauge labels. -/
theorem exchange_intertwining :
    (gamma ⊗ₖ (1 : Matrix n n ℂ)) * embedding =
      embedding * (exchange ⊗ₖ (1 : Matrix n n ℂ)) := by
  simp [embedding, ← mul_kronecker_mul, carrier_exchange]

/-- The weak/gauge payload remains an independent index in the input reference. -/
def referenceInput (r : n → ℂ) : Fin 2 × n → ℂ :=
  fun p => (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) p.1 * r p.2

def seedInput (r : n → ℂ) : Fin 4 × n → ℂ := fun p => WalkReferenceCoupling.seed p.1 * r p.2

/-- The existing beta preparation acts on control/spin, preserving the actual payload vector. -/
theorem prepare_payload (r : n → ℂ) :
    (WalkReferenceCoupling.preparation ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ seedInput r =
      embedding *ᵥ referenceInput r := by
  ext p
  rcases p with ⟨a,j⟩
  change ((WalkReferenceCoupling.preparation ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ
      (fun p => WalkReferenceCoupling.seed p.1 * r p.2)) (a,j) =
    ((carrier ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ
      (fun p => (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) p.1 * r p.2)) (a,j)
  rw [tensor_packet, tensor_packet, one_mulVec, record_column]

/-- A gauge change transforms the reference payload, rather than fixing a preferred nonzero vector. -/
theorem reference_transforms (G : Matrix n n ℂ) (r : n → ℂ) :
    ((1 : Spin) ⊗ₖ G) *ᵥ (embedding *ᵥ referenceInput r) =
      embedding *ᵥ referenceInput (G *ᵥ r) := by
  rw [mulVec_mulVec, gauge_intertwining, ← mulVec_mulVec]
  congr 1
  ext p
  rcases p with ⟨a,j⟩
  change (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G) *ᵥ
      (fun p => (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) p.1 * r p.2)) (a,j) =
    (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) a * (G *ᵥ r) j
  rw [tensor_packet, one_mulVec]

omit [DecidableEq n] in
/-- The mode overhead is explicit; payload labels are not reused spinor coordinates. -/
theorem mode_count : Fintype.card (Fin 4 × n) = 4 * Fintype.card n ∧
    Fintype.card (Fin 2 × n) = 2 * Fintype.card n := by simp

end Payload

/-- Preparation, coupling and spatial propagation all commute with a common
payload action when lifted on the independent payload index. -/
theorem payload_commutes {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]
    (A : Matrix s s ℂ) (G : Matrix n n ℂ) :
    (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix s s ℂ) ⊗ₖ G) =
      ((1 : Matrix s s ℂ) ⊗ₖ G) * (A ⊗ₖ (1 : Matrix n n ℂ)) := by
  simp [← mul_kronecker_mul]

/-- The independent-index construction preserves the supplied unitary actions. -/
theorem tensor_unitary {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]
    (A : Matrix s s ℂ) (G : Matrix n n ℂ)
    (ha : A ∈ unitary (Matrix s s ℂ)) (hg : G ∈ unitary (Matrix n n ℂ)) :
    A ⊗ₖ G ∈ unitary (Matrix (s × n) (s × n) ℂ) := by
  have ha1 : Aᴴ * A = 1 := ha.1
  have ha2 : A * Aᴴ = 1 := ha.2
  have hg1 : Gᴴ * G = 1 := hg.1
  have hg2 : G * Gᴴ = 1 := hg.2
  constructor <;>
    simp [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul,
      ha1, ha2, hg1, hg2]

/-- A single spinor's obvious two-mode reuse is not an independent non-Abelian
internal action: commuting with chirality and the spatial alpha matrices
already restricts the action strongly. This lemma computes the restriction. -/
theorem spinor_commutant (G : Spin) (hg : G * gamma = gamma * G)
    (h0 : G * alpha 0 = alpha 0 * G) (h2 : G * alpha 2 = alpha 2 * G) :
    G = diagonal ![G 0 0, G 0 0, G 2 2, G 2 2] := by
  have hd : G 1 1 = G 0 0 := by
    have h := congrFun (congrFun h0 0) 1
    simpa [alpha, mul_apply, Fin.sum_univ_four] using h.symm
  have he : G 3 3 = G 2 2 := by
    have h := congrFun (congrFun h0 2) 3
    simpa [alpha, mul_apply, Fin.sum_univ_four] using h.symm
  ext a b
  have hga := congrFun (congrFun hg a) b
  have h2a := congrFun (congrFun h2 a) b
  fin_cases a <;> fin_cases b <;>
    norm_num [gamma, alpha, mul_apply, Fin.sum_univ_four, hd, he] at hga h2a ⊢
  all_goals first
    | exact CharZero.neg_eq_self_iff.mp hga
    | exact CharZero.eq_neg_self_iff.mp hga
    | exact CharZero.neg_eq_self_iff.mp h2a
    | exact CharZero.eq_neg_self_iff.mp h2a

/-- Such spinor-only internal actions commute with each other; they cannot
realize a faithful non-Abelian internal gauge action under these hypotheses. -/
theorem spinor_commutant_abelian (G H : Spin)
    (hg : G * gamma = gamma * G) (h0 : G * alpha 0 = alpha 0 * G)
    (h2 : G * alpha 2 = alpha 2 * G)
    (kg : H * gamma = gamma * H) (k0 : H * alpha 0 = alpha 0 * H)
    (k2 : H * alpha 2 = alpha 2 * H) : G * H = H * G := by
  rw [spinor_commutant G hg h0 h2, spinor_commutant H kg k0 k2]
  simp only [diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

end PMAction.GaugeRecordEmbedding
