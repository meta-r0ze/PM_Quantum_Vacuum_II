import PMAction.CoherentRecordRestoration
import PMAction.RefreshSchedule

/-!
# Executable coherent refresh coverage, without assuming a sector-owner function

Each addressed instruction exchanges one live amplitude with its record.
Universal restoration of the specified independent live fields forces every
address to be visited. Positive additive scheduled prices make a minimum
restoring word visit every address exactly once. Splitting that word into
sector schedules therefore gives disjoint complete coverage as a conclusion.

The required independent fields, prepared records, allowed addressed couplings
and scheduled prices are model inputs. Gauge transformations alone are not
identified with these couplings, and no electroweak ownership is selected here.
-/
noncomputable section
namespace PMAction.CoherentRefresh
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exchange precisely the selected live/record mode pairs. -/
def selected (S : Finset n) : Equiv.Perm (n ⊕ n) where
  toFun x := match x with
    | .inl i => if i ∈ S then .inr i else .inl i
    | .inr i => if i ∈ S then .inl i else .inr i
  invFun x := match x with
    | .inl i => if i ∈ S then .inr i else .inl i
    | .inr i => if i ∈ S then .inl i else .inr i
  left_inv x := by
    rcases x with i | i <;> (by_cases hi : i ∈ S <;> simp [hi])
  right_inv x := by
    rcases x with i | i <;> (by_cases hi : i ∈ S <;> simp [hi])

def act (S : Finset n) (ψ : n ⊕ n → ℂ) : n ⊕ n → ℂ := (selected S).permMatrix ℂ *ᵥ ψ

lemma act_left (S : Finset n) (ψ : n ⊕ n → ℂ) (i : n) :
    act S ψ (.inl i) = if i ∈ S then ψ (.inr i) else ψ (.inl i) := by
  rw [act, Matrix.permMatrix_mulVec]
  by_cases hi : i ∈ S <;> simp [selected, hi]

lemma act_right (S : Finset n) (ψ : n ⊕ n → ℂ) (i : n) :
    act S ψ (.inr i) = if i ∈ S then ψ (.inl i) else ψ (.inr i) := by
  rw [act, Matrix.permMatrix_mulVec]
  by_cases hi : i ∈ S <;> simp [selected, hi]

theorem act_norm (S : Finset n) (ψ : n ⊕ n → ℂ) :
    CommonResponse.nsq (act S ψ) = CommonResponse.nsq ψ :=
  congrArg Complex.re (CommonResponse.unitary_nsq _ (CarrierResponse.perm_unitary _) ψ)

/-- Head instruction executes first. -/
def run : List n → (n ⊕ n → ℂ) → (n ⊕ n → ℂ)
  | [], ψ => ψ
  | i :: L, ψ => run L (act {i} ψ)

theorem run_norm (L : List n) (ψ : n ⊕ n → ℂ) :
    CommonResponse.nsq (run L ψ) = CommonResponse.nsq ψ := by
  induction L generalizing ψ with
  | nil => rfl
  | cons i L ih => rw [run, ih, act_norm]

theorem untouched (L : List n) (ψ : n ⊕ n → ℂ) (i : n) (hi : i ∉ L) :
    run L ψ (.inl i) = ψ (.inl i) ∧ run L ψ (.inr i) = ψ (.inr i) := by
  induction L generalizing ψ with
  | nil => exact ⟨rfl,rfl⟩
  | cons j L ih =>
    simp only [List.mem_cons, not_or] at hi
    simpa only [run, act_left, act_right, Finset.mem_singleton, hi.1, ite_false] using
      ih (act {j} ψ) hi.2

theorem run_nodup (L : List n) (hL : L.Nodup) (ψ : n ⊕ n → ℂ) (i : n) :
    (run L ψ (.inl i) = if i ∈ L then ψ (.inr i) else ψ (.inl i)) ∧
      (run L ψ (.inr i) = if i ∈ L then ψ (.inl i) else ψ (.inr i)) := by
  induction L generalizing ψ with
  | nil => simp [run]
  | cons j L ih =>
    obtain ⟨hj, ht⟩ := List.nodup_cons.mp hL
    have hh := ih ht (act {j} ψ)
    by_cases he : i = j
    · subst i
      simpa [run, hj, act_left, act_right] using hh
    · simpa [run, he, act_left, act_right] using hh

/-- Correctness concerns all independent input amplitudes, not their gauge charges. -/
def Restores (L : List n) : Prop :=
  ∀ input : n → ℂ, ∀ i, run L (Sum.elim input (fun _ => 0)) (.inl i) = 0

theorem restoring_visits (L : List n) (h : Restores L) :
    RefreshSchedule.admissible Finset.univ L := by
  intro i _
  by_contra hi
  have he := (untouched L (Sum.elim (fun _ => 1) (fun _ => 0)) i hi).1
  have hz := h (fun _ => 1) i
  rw [he] at hz
  norm_num at hz

theorem canonical_restores : Restores (Finset.univ : Finset n).toList := by
  intro input i
  have h := (run_nodup (Finset.univ : Finset n).toList (Finset.univ : Finset n).nodup_toList
    (Sum.elim input (fun _ => 0)) i).1
  simpa using h

theorem minimum_cost (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsLeast {c | ∃ L, Restores L ∧ RefreshSchedule.cost w L = c} (∑ i, w i) := by
  refine ⟨⟨Finset.univ.toList, canonical_restores,
    (RefreshSchedule.minimal_attained w Finset.univ).2⟩, ?_⟩
  rintro c ⟨L,hL,rfl⟩
  exact RefreshSchedule.admissible_cost_ge w hw _ L (restoring_visits L hL)

/-- Once-only coverage is derived from correctness and a minimum price. -/
theorem minimum_once (w : n → ℝ) (hw : ∀ i, 0 < w i) (L : List n)
    (hL : Restores L) (hmin : RefreshSchedule.cost w L = ∑ i, w i) :
    L.Nodup ∧ L.toFinset = Finset.univ := by
  by_contra hn
  have hs := RefreshSchedule.strict_if_extra w hw Finset.univ L (restoring_visits L hL) hn
  rw [hmin] at hs
  exact (lt_irrefl _ hs)

/-- A two-sector minimum produces a partition; none was assumed in the input. -/
theorem minimum_pair_partition (w : n → ℝ) (hw : ∀ i, 0 < w i) (A B : List n)
    (hr : Restores (A ++ B)) (hm : RefreshSchedule.cost w (A ++ B) = ∑ i, w i) :
    Disjoint A.toFinset B.toFinset ∧ A.toFinset ∪ B.toFinset = Finset.univ := by
  obtain ⟨hn, hu⟩ := minimum_once w hw (A ++ B) hr hm
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    exact (List.nodup_append.mp hn).2.2 i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj) rfl
  · simpa only [List.toFinset_append] using hu

/-- Full matched record exchange respects every common linear action, not only charged ones. -/
theorem full_exchange_covariant (G : Matrix n n ℂ) :
    BranchMixerSynthesis.exchange * fromBlocks G 0 0 G =
      fromBlocks G 0 0 G * BranchMixerSynthesis.exchange := by
  simp [BranchMixerSynthesis.exchange, fromBlocks_multiply]

end PMAction.CoherentRefresh
