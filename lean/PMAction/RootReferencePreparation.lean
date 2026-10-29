import PMAction.RootCarrierCycle

/-!
# Preparing the specified reference with an actual root event

In the actual-carrier frame the fixed reference packet is a single existing
carrier label. One root reflection prepares it from the specified distinct
carrier seed. This is an alternative to assuming the spinor-basis seed is
freely available: that seed is already coherent in the carrier frame.
Known seeds are supplied, not copied from unknown inputs or created from zero.
Setup prices count sitewise carrier-label changes under an explicit tariff.
-/
noncomputable section
namespace PMAction.RootReferencePreparation
open Matrix CommonResponse
open scoped Kronecker
abbrev C := ActualRootRepair.C
abbrev reference := WalkReferenceCoupling.reference
abbrev seedLabel : C := ActualRootRepair.positive
abbrev recordLabel : C := ActualRootRepair.label (.inr 0)

lemma distinct : seedLabel ≠ recordLabel := by decide +kernel

lemma live_basis : ActualRootRepair.pack reference 0 = Pi.single seedLabel 1 := by
  have h : Sum.elim reference (0 : Fin 2 → ℂ) = Pi.single (Sum.inl (0 : Fin 2)) 1 := by
    ext j
    rcases j with j | j <;> fin_cases j <;>
      simp [reference, WalkReferenceCoupling.reference]
  rw [ActualRootRepair.pack, h, ActualRootRepair.column]
  rfl

lemma reference_basis : ActualRootRepair.pack 0 reference = Pi.single recordLabel 1 := by
  have h : Sum.elim (0 : Fin 2 → ℂ) reference = Pi.single (Sum.inr (0 : Fin 2)) 1 := by
    ext j
    rcases j with j | j <;> fin_cases j <;>
      simp [reference, WalkReferenceCoupling.reference]
  rw [ActualRootRepair.pack, h, ActualRootRepair.column]

/-- The desired reference is a basis carrier in this frame; no fractional pulse
is needed to implement this particular known-state preparation. -/
theorem prepares_reference :
    ActualRootRepair.root.permMatrix ℂ *ᵥ Pi.single seedLabel 1 =
      ActualRootRepair.pack 0 reference := by
  rw [← live_basis, ActualRootRepair.repair]

/-- This exact operation does not manufacture the reference from an arbitrary
unknown amplitude: reversibility fixes the required input uniquely. -/
theorem prepares_iff (ψ : C → ℂ) :
    ActualRootRepair.root.permMatrix ℂ *ᵥ ψ = ActualRootRepair.pack 0 reference ↔
      ψ = Pi.single seedLabel 1 := by
  constructor
  · intro h
    have hh := congrArg (fun v => ActualRootRepair.root.permMatrix ℂ *ᵥ v) h
    rw [mulVec_mulVec, RootTransferPhase.permutation_square _
      (CarrierEvents.reflection_involutive 0), one_mulVec,
      ActualRootRepair.repair, live_basis] at hh
    exact hh
  · rintro rfl
    exact prepares_reference

/-- A zero-amplitude input cannot provide the nonzero reference. -/
theorem no_reference_from_zero :
    ActualRootRepair.root.permMatrix ℂ *ᵥ (0 : C → ℂ) ≠ ActualRootRepair.pack 0 reference := by
  intro h
  have hi := (prepares_iff (0 : C → ℂ)).mp h
  have hh := congrFun hi seedLabel
  simp at hh

/-- Even on this known basis seed, the comparator flag is a different event
from the deterministic changed-label event charged in the setup ledger. -/
theorem setup_comparison_flag :
    stateFlag (ActualRootRepair.root.permMatrix ℂ) (Pi.single seedLabel 1) = 1/2 := by
  have hu := CarrierResponse.perm_unitary ActualRootRepair.root
  rw [CommonResponse.basis_case _ hu, InterferenceReadout.flag_formula _ hu]
  have hm : ActualRootRepair.root seedLabel ≠ seedLabel := by decide +kernel
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hm]

/-- Both seed and target are actual minimal-vector states of the same glue class. -/
theorem carrier_norms :
    PMArch.Channels.norm4 (CarrierEvents.vector seedLabel) = 4 ∧
      PMArch.Channels.norm4 (CarrierEvents.vector recordLabel) = 4 :=
  ⟨(CarrierEvents.vector_properties seedLabel).2, (CarrierEvents.vector_properties recordLabel).2⟩

lemma seed_decode : RootWalkEncoding.frameᴴ *ᵥ WalkReferenceCoupling.seed =
    RootWalkEncoding.scale • Sum.elim reference reference := by
  ext j
  rcases j with j | j <;> fin_cases j <;>
    simp [RootWalkEncoding.frame, RootWalkEncoding.rawFrame, RootWalkEncoding.scale,
      WalkReferenceCoupling.seed, WalkReferenceCoupling.raw, WalkReferenceCoupling.backward,
      WalkRecordTransport.encode, reference, WalkReferenceCoupling.reference,
      mulVec, dotProduct, conjTranspose_apply, Fin.sum_univ_four]

/-- The earlier spinor seed already has two nonzero carrier amplitudes.
It cannot be counted as a free classical carrier seed. -/
theorem spinor_seed_is_coherent :
    RootWalkEncoding.interface *ᵥ WalkReferenceCoupling.seed =
      RootWalkEncoding.scale • ActualRootRepair.pack reference reference := by
  rw [RootWalkEncoding.interface, ← mulVec_mulVec, seed_decode, Matrix.mulVec_smul]
  rfl

/-- The previously specified moving walk reference is exactly this basis carrier. -/
theorem walk_reference :
    RootWalkEncoding.interface *ᵥ WalkReferenceCoupling.pack (Sum.elim 0 reference) =
      Pi.single recordLabel 1 := by
  rw [RootWalkEncoding.encoded_packet, reference_basis]

section Arrays
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The physical root is applied once at each site; no writable clock is assumed. -/
def rootArray : Matrix (X × C) (X × C) ℂ :=
  (1 : Matrix X X ℂ) ⊗ₖ ActualRootRepair.root.permMatrix ℂ

theorem array_unitary : rootArray (X := X) ∈ unitary (Matrix (X × C) (X × C) ℂ) := by
  have h := CarrierResponse.perm_unitary ActualRootRepair.root
  have hl : (ActualRootRepair.root.permMatrix ℂ)ᴴ * ActualRootRepair.root.permMatrix ℂ = 1 := h.1
  have hr : ActualRootRepair.root.permMatrix ℂ * (ActualRootRepair.root.permMatrix ℂ)ᴴ = 1 := h.2
  constructor <;>
    simp only [rootArray, star_eq_conjTranspose, conjTranspose_kronecker,
      ← mul_kronecker_mul, conjTranspose_one, one_mul, hl, hr, one_kronecker_one]

/-- Every reference has a counted supplied basis seed at the same site. -/
theorem prepares_array :
    rootArray *ᵥ (fun p : X × C => (Pi.single seedLabel (1 : ℂ) : C → ℂ) p.2) =
      RootCarrierWalk.field (fun _ => 0) (fun _ => reference) := by
  ext p
  rcases p with ⟨x,c⟩
  have h := congrFun prepares_reference c
  simpa [rootArray, RootCarrierWalk.field, mulVec, dotProduct, Fintype.sum_prod_type,
    one_apply] using h

/-- The prepared train has one unit of the model's population per supplied site.
It is not asserted to be a normalized one-particle state or a physical energy. -/
theorem prepared_population :
    nsq (RootCarrierWalk.field (X := X) (fun _ => 0) (fun _ => reference)) = Fintype.card X := by
  rw [← RootCarrierWalk.encoded_field, RootCarrierWalk.population]
  exact WalkReferenceProtocol.prepared_array_population

end Arrays

section Ledger
variable {S : Type*} [DecidableEq S]

/-- Endpoint label changes along a supplied finite site history. -/
def changes (path : ℕ → S) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, if path (k+1)=path k then 0 else 1

lemma changes_succ (path : ℕ → S) (N : ℕ) :
    changes path (N+1) = changes path N + if path (N+1)=path N then 0 else 1 := by
  simp [changes, Finset.sum_range_succ]

theorem endpoint_of_zero_changes (path : ℕ → S) (N : ℕ) (h : changes path N = 0) :
    path N = path 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [changes_succ] at h
    have h0 : changes path N = 0 := by omega
    have hs : path (N+1)=path N := by
      by_contra hn
      simp [hn] at h
    exact hs.trans (ih h0)

theorem required_change (path : ℕ → S) (N : ℕ) (h : path N ≠ path 0) :
    1 ≤ changes path N := by
  have hn : changes path N ≠ 0 := fun h0 => h (endpoint_of_zero_changes path N h0)
  omega

end Ledger

section SetupCost
variable {X : Type*} [Fintype X] [DecidableEq X]

def setupChanges (path : ℕ → X → C) (N : ℕ) : ℕ := ∑ x, changes (fun t => path t x) N

omit [DecidableEq X] in
/-- Any history accomplishing this specified sitewise task must change each site.
The lower bound even allows arbitrary intermediate carrier labels. -/
theorem setup_lower_bound (path : ℕ → X → C) (N : ℕ)
    (h0 : ∀ x, path 0 x=seedLabel) (hN : ∀ x, path N x=recordLabel) :
    Fintype.card X ≤ setupChanges path N := by
  calc
    Fintype.card X = ∑ _ : X, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun x _ => required_change (fun t => path t x) N (by
      rw [h0, hN]; exact Ne.symm distinct))

def setupPath (t : ℕ) (_x : X) : C := if t=0 then seedLabel else recordLabel

omit [Fintype X] [DecidableEq X] in
/-- The lower-bound attainment history is an actual root step, not an invented jump. -/
theorem setupPath_is_root (x : X) :
    setupPath 1 x = ActualRootRepair.root (setupPath 0 x) := by
  simp [setupPath]
  rfl

omit [DecidableEq X] in
theorem setup_attains : setupChanges (setupPath (X := X)) 1 = Fintype.card X := by
  simp [setupChanges, changes, setupPath, Ne.symm distinct]

omit [DecidableEq X] in
/-- This is the supplied price per sitewise changed-carrier event, including setup. -/
theorem minimum_setup_price (toll : ℝ) (ht : 0 ≤ toll) (path : ℕ → X → C) (N : ℕ)
    (h0 : ∀ x, path 0 x=seedLabel) (hN : ∀ x, path N x=recordLabel) :
    toll * Fintype.card X ≤ toll * setupChanges path N := by
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast setup_lower_bound path N h0 hN) ht

omit [DecidableEq X] in
/-- The conversion lower bound is conditional on the distinct initial seed.
An already supplied reference needs no conversion; its source is a separate input. -/
theorem already_prepared_cost_zero (N : ℕ) :
    setupChanges (fun _ (_x : X) => recordLabel) N = 0 := by
  simp [setupChanges, changes]

end SetupCost
end PMAction.RootReferencePreparation
