import PMAction.CommonResponse
import PMAction.LinkExpansion
import Mathlib.Data.Matrix.Block

/-! A reversible controller for the actual two-branch comparison readout.
This constructs coherent uncomputation; it does not price its E8 implementation
or identify it with a fixed number of events triggered only by a flag. -/
noncomputable section
namespace PMAction.CoherentComparisonRepair
open Matrix PMAction PMAction.InterferenceReadout
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The plus and minus amplitudes of a coherent comparison. -/
def plus (U : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℂ) • (1+U)
def minus (U : Matrix n n ℂ) : Matrix n n ℂ := (1/2 : ℂ) • (1-U)

def compare (U : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (plus U) (minus U) (minus U) (plus U)

omit [Fintype n] in
/-- Its actual minus-port entries are exactly Paper II's flag amplitudes. -/
theorem flag_entry (U : Matrix n n ℂ) (a b : n) :
    compare U (.inr b) (.inl a)=flagAmplitude U a b := rfl

omit [Fintype n] in
lemma compare_one : compare (1 : Matrix n n ℂ)=1 := by
  have hp : plus (1 : Matrix n n ℂ)=1 := by unfold plus; module
  have hm : minus (1 : Matrix n n ℂ)=0 := by simp [minus]
  rw [compare,hp,hm,fromBlocks_one]

lemma compare_mul (U V : Matrix n n ℂ) : compare (U*V)=compare U*compare V := by
  unfold compare
  rw [fromBlocks_multiply,fromBlocks_inj]
  simp only [plus,minus,smul_mul_smul_comm,add_mul,mul_add,sub_mul,mul_sub,
    one_mul,mul_one]
  constructor
  · module
  constructor
  · module
  constructor <;> module

omit [Fintype n] in
lemma compare_star (U : Matrix n n ℂ) : (compare U)ᴴ=compare Uᴴ := by
  simp [compare,plus,minus,fromBlocks_conjTranspose,conjTranspose_smul]

theorem compare_unitary (U : Matrix n n ℂ) (hu : U ∈ unitary _) :
    compare U ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have h1 : Uᴴ*U=1 := hu.1
  have h2 : U*Uᴴ=1 := hu.2
  constructor
  · change (compare U)ᴴ*compare U=1
    rw [compare_star,← compare_mul,h1,compare_one]
  · change compare U*(compare U)ᴴ=1
    rw [compare_star,← compare_mul,h2,compare_one]

/-- Exact uncomputation on every coherent state, not just the input basis.
This restores both controller and payload, retaining every distinction. -/
theorem uncompute (U : Matrix n n ℂ) (hu : U ∈ unitary _) (ψ : n ⊕ n → ℂ) :
    compare Uᴴ*ᵥ (compare U*ᵥ ψ)=ψ := by
  have h1 : Uᴴ*U=1 := hu.1
  rw [mulVec_mulVec,← compare_mul,h1,compare_one,one_mulVec]

/-- Uncomputing the actual prepared comparison restores its zero minus-port
and its original payload, without measuring or discarding the branch. -/
theorem prepared_uncompute (U : Matrix n n ℂ) (hu : U ∈ unitary _) (φ : n → ℂ) :
    compare Uᴴ*ᵥ (compare U*ᵥ Sum.elim φ (fun _ => 0))=Sum.elim φ (fun _ => 0) :=
  uncompute U hu _

/-- For an involutive carrier operation the comparison branches are the two
complementary projectors. This characterizes the actually prepared inputs. -/
lemma involution_projectors (U : Matrix n n ℂ) (hsq : U*U=1) :
    plus U*plus U=plus U ∧ minus U*minus U=minus U ∧
    plus U*minus U=0 ∧ minus U*plus U=0 := by
  simp only [plus,minus,smul_mul_smul_comm,add_mul,mul_add,sub_mul,mul_sub,
    one_mul,mul_one,hsq]
  constructor
  · module
  constructor
  · module
  constructor <;> module

/-- On the valid unflagged branch of an involutive comparison the coherent
inverse really is idle. The no-go below concerns ALL unflagged states, not
only this properly correlated subspace. -/
theorem valid_unflagged_idle (U : Matrix n n ℂ) (hsq : U*U=1) (φ : n → ℂ) :
    compare U*ᵥ Sum.elim (plus U*ᵥ φ) (fun _ => 0)=
      Sum.elim (plus U*ᵥ φ) (fun _ => 0) := by
  have hz (M : Matrix n n ℂ) : M*ᵥ (fun _ : n => (0 : ℂ))=0 := Matrix.mulVec_zero M
  obtain ⟨hpp,_,_,hmp⟩ := involution_projectors U hsq
  rw [compare,fromBlocks_mulVec]
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,hz,add_zero,
    mulVec_mulVec,hpp,hmp,zero_mulVec]
  rfl

/-- The valid flagged branch is reset while its projected payload is retained.
This is coherent branch algebra, not a claim about discarding a measurement
record or implementing the comparison at one primitive E8 toll. -/
theorem valid_flagged_reset (U : Matrix n n ℂ) (hsq : U*U=1) (φ : n → ℂ) :
    compare U*ᵥ Sum.elim (fun _ => 0) (minus U*ᵥ φ)=
      Sum.elim (minus U*ᵥ φ) (fun _ => 0) := by
  have hz (M : Matrix n n ℂ) : M*ᵥ (fun _ : n => (0 : ℂ))=0 := Matrix.mulVec_zero M
  obtain ⟨_,hmm,hpm,_⟩ := involution_projectors U hsq
  rw [compare,fromBlocks_mulVec]
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,hz,add_zero,zero_add,
    mulVec_mulVec,hmm,hpm,zero_mulVec]
  rfl

/-- A closed unitary that fixes the entire unflagged subspace cannot send any
of the flagged subspace into it. A and B describe the most general remaining
blocks after that fixing condition, not an imposed block-diagonal repair. -/
theorem conditional_unitary_blocks (A B : Matrix n n ℂ)
    (hr : fromBlocks 1 A 0 B ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    A=0 ∧ B ∈ unitary (Matrix n n ℂ) := by
  have hl : (fromBlocks (1 : Matrix n n ℂ) A 0 B)ᴴ*fromBlocks 1 A 0 B=1 := hr.1
  have hh : fromBlocks (1 : Matrix n n ℂ) A 0 B*(fromBlocks 1 A 0 B)ᴴ=1 := hr.2
  simp only [fromBlocks_conjTranspose,fromBlocks_multiply,conjTranspose_one,
    conjTranspose_zero,one_mul,mul_one,zero_mul,mul_zero,zero_add,add_zero,
    ← fromBlocks_one,fromBlocks_inj] at hl hh
  have ha := hl.2.1
  refine ⟨ha,?_,?_⟩
  · change Bᴴ*B=1
    simpa [ha] using hl.2.2.2
  · change B*Bᴴ=1
    exact hh.2.2.2

def minusPart (ψ : n ⊕ n → ℂ) (i : n) : ℂ := ψ (.inr i)

lemma conditional_minus_part (A B : Matrix n n ℂ) (ψ : n ⊕ n → ℂ) :
    minusPart (fromBlocks 1 A 0 B*ᵥ ψ)=B*ᵥ minusPart ψ := by
  funext i
  simp [minusPart,mulVec,dotProduct,Fintype.sum_sum_type]

/-- The entire minus-branch norm is conserved by a closed conditional repair
that leaves every unflagged state unchanged. -/
theorem conditional_preserves_flag_norm (A B : Matrix n n ℂ)
    (hr : fromBlocks 1 A 0 B ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (ψ : n ⊕ n → ℂ) :
    CommonResponse.nsq (minusPart (fromBlocks 1 A 0 B*ᵥ ψ))=
      CommonResponse.nsq (minusPart ψ) := by
  rw [conditional_minus_part]
  have he := CommonResponse.unitary_nsq B (conditional_unitary_blocks A B hr).2 (minusPart ψ)
  exact congrArg Complex.re he

/-- The norm of the actual comparison's minus branch is the old flag
probability, so the controller construction changes no readout convention. -/
theorem comparison_flag_norm (U : Matrix n n ℂ) (a : n) :
    CommonResponse.nsq (minusPart (compare U*ᵥ Pi.single (.inl a) 1))=flagProbability U a := by
  simp [PMAction.LinkExpansion.nsq_eq,minusPart,Matrix.col_apply,
    flagProbability,flag_entry]

/-- A nonzero comparison flag cannot be cleared by such a conditional unitary
without another retained record or a change on the unflagged subspace. This is
not a no-go for repairs with additional controller/environment degrees of freedom. -/
theorem conditional_cannot_clear (U : Matrix n n ℂ) (a : n)
    (hf : 0 < flagProbability U a) (A B : Matrix n n ℂ)
    (hr : fromBlocks 1 A 0 B ∈ unitary (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    minusPart (fromBlocks 1 A 0 B*ᵥ (compare U*ᵥ Pi.single (.inl a) 1)) ≠ 0 := by
  intro hz
  have he := conditional_preserves_flag_norm A B hr (compare U*ᵥ Pi.single (.inl a) 1)
  rw [comparison_flag_norm,hz] at he
  simp [CommonResponse.nsq] at he
  linarith

/-- Fixing every unflagged basis state determines the full left block column.
The later obstruction is therefore not limited to a guessed repair ansatz. -/
lemma fixes_unflagged_blocks (R : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hfix : ∀ a : n, R*ᵥ Pi.single (.inl a) 1=Pi.single (.inl a) 1) :
    R=fromBlocks 1 R.toBlocks₁₂ 0 R.toBlocks₂₂ := by
  have htop : R.toBlocks₁₁=1 := by
    ext i j
    have h := congrFun (hfix j) (.inl i)
    simpa [Matrix.mulVec_single_one,Matrix.col_apply,Matrix.toBlocks₁₁,Pi.single_apply,
      Matrix.one_apply] using h
  have hbottom : R.toBlocks₂₁=0 := by
    ext i j
    have h := congrFun (hfix j) (.inr i)
    simpa [Matrix.mulVec_single_one,Matrix.col_apply,Matrix.toBlocks₂₁,Pi.single_apply] using h
  calc
    R=fromBlocks R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂ :=
      (fromBlocks_toBlocks R).symm
    _ = _ := by rw [htop,hbottom]

/-- A general closed unitary repair cannot both leave every unflagged basis
state untouched and clear an actually nonzero comparison flag. -/
theorem nondisturbing_cannot_clear (U : Matrix n n ℂ) (a : n)
    (hf : 0 < flagProbability U a) (R : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hr : R ∈ unitary _) (hfix : ∀ b : n, R*ᵥ Pi.single (.inl b) 1=Pi.single (.inl b) 1) :
    minusPart (R*ᵥ (compare U*ᵥ Pi.single (.inl a) 1)) ≠ 0 := by
  have he := fixes_unflagged_blocks R hfix
  rw [he] at hr ⊢
  exact conditional_cannot_clear U a hf _ _ hr

/-- The available coherent inverse does clear the prepared flag, so it must
act nontrivially on some unflagged inputs. Its cost cannot be identified with a
flag-only instruction count merely from the uncomputation identity. -/
theorem inverse_not_flag_only (U : Matrix n n ℂ) (hu : U ∈ unitary _) (a : n)
    (hf : 0 < flagProbability U a) :
    ¬ ∀ b : n, compare Uᴴ*ᵥ Pi.single (.inl b) 1=Pi.single (.inl b) 1 := by
  intro hfix
  have hstar : Uᴴ ∈ unitary (Matrix n n ℂ) := Unitary.star_mem hu
  have hne := nondisturbing_cannot_clear U a hf (compare Uᴴ) (compare_unitary _ hstar) hfix
  apply hne
  rw [uncompute U hu]
  funext i
  simp [minusPart]

omit [Fintype n] in
lemma comparison_half_entry (e : Equiv.Perm n) (a : n) (hm : e a ≠ a) :
    compare (e.permMatrix ℂ) (.inr a) (.inl a)=(1/2 : ℂ) := by
  have hz : (e.permMatrix ℂ) a a=0 := by simp [Equiv.Perm.permMatrix,hm]
  rw [flag_entry]
  norm_num [flagAmplitude,hz,hm]

omit [Fintype n] in
lemma permutation_entry_not_half (p : Equiv.Perm (n ⊕ n)) (i j : n ⊕ n) :
    (p.permMatrix ℂ) i j ≠ (1/2 : ℂ) := by
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_apply,Pi.single_apply]
  split_ifs <;> norm_num

/-- A moved input basis state produces amplitude 1/2 in the minus port.
Permutation gates alone cannot reproduce even this prepared input column in
this basis. Superposed preparation, a changed readout basis or a richer operator
construction are separate routes, not excluded by this result. -/
theorem comparison_basis_not_permutation (e : Equiv.Perm n) (a : n) (hm : e a ≠ a)
    (p : Equiv.Perm (n ⊕ n)) :
    compare (e.permMatrix ℂ)*ᵥ Pi.single (.inl a) 1 ≠
      p.permMatrix ℂ*ᵥ Pi.single (.inl a) 1 := by
  intro he
  have h := congrFun he (.inr a)
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at h
  rw [comparison_half_entry e a hm] at h
  exact permutation_entry_not_half p _ _ h.symm

omit [Fintype n] in
/-- In particular the whole comparison controller is not a permutation matrix. -/
theorem comparison_not_permutation (e : Equiv.Perm n) (a : n) (hm : e a ≠ a)
    (p : Equiv.Perm (n ⊕ n)) : compare (e.permMatrix ℂ) ≠ p.permMatrix ℂ := by
  intro he
  have h := congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) ℂ => X (.inr a) (.inl a)) he
  rw [comparison_half_entry e a hm] at h
  exact permutation_entry_not_half p _ _ h.symm

/-- The controller for the actual class reflection requires that additional
operator/preparation step in every one of the three glue classes. -/
theorem root_comparison_not_permutation (c : Fin 3)
    (p : Equiv.Perm (PMAction.CarrierEvents.Carrier c ⊕ PMAction.CarrierEvents.Carrier c)) :
    compare ((PMAction.CarrierEvents.reflect c).permMatrix ℂ) ≠ p.permMatrix ℂ := by
  have hp : 0 < (PMAction.CarrierEvents.active c).card := by
    rw [PMAction.CarrierEvents.active_card]; norm_num
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  exact comparison_not_permutation _ a (Finset.mem_filter.mp ha).2 p

end PMAction.CoherentComparisonRepair
