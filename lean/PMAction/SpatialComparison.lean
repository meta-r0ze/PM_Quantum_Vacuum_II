import PMAction.FiniteEncoding
import PMAction.InvolutionComparison
import PMAction.StateIdentification
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# A comparison register on two spatial cells

The two comparison branches embed into two supplied distinct cells, with every
payload label retained in each. Supplied permutations extend by identity outside
those cells. Their spectral phases therefore realize the marker-free comparison
with exact all-state readout and no use of the chirality wall as a spare branch.
The cell allocation, clean/prepared input, coherent phase admission, times and
prices are still supplied. This is a construction, not the selected vacuum
schedule or a claim that an occupied cell can be cleared for free.
An arbitrary payload permutation is not thereby certified as an E8 primitive.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.SpatialComparison
open Matrix NativeObservation InvolutionComparison
variable {X n : Type*} [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n]

def label (live record : X) (j : n ⊕ n) : X × n :=
  Sum.elim (fun k => (live, k)) (fun k => (record, k)) j

omit [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n] in
theorem label_injective (live record : X) (h : live ≠ record) :
    Function.Injective (label (n := n) live record) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (congrArg Prod.snd hij)
  · exact (h (congrArg Prod.fst hij)).elim
  · exact (h (congrArg Prod.fst hij).symm).elim
  · exact congrArg Sum.inr (congrArg Prod.snd hij)

def ports (live record : X) (h : live ≠ record) : (n ⊕ n) ↪ (X × n) :=
  ⟨label live record, label_injective live record h⟩

def encoding (live record : X) : Matrix (X × n) (n ⊕ n) ℂ :=
  FiniteEncoding.matrix (label live record)

theorem isometry (live record : X) (h : live ≠ record) :
    (encoding (n := n) live record)ᴴ * encoding (n := n) live record = 1 :=
  FiniteEncoding.isometry (label (n := n) live record) (label_injective live record h)

def extend (live record : X) (h : live ≠ record) (e : Equiv.Perm (n ⊕ n)) :
    Equiv.Perm (X × n) := e.viaEmbedding (ports live record h)

theorem permutation_observed (live record : X) (h : live ≠ record)
    (e : Equiv.Perm (n ⊕ n)) :
    Obs (encoding live record) ((extend live record h e).permMatrix ℂ) (e.permMatrix ℂ) := by
  have he (j) : extend live record h e (label live record j) = label live record (e j) :=
    Equiv.Perm.viaEmbedding_apply e (ports live record h) j
  exact ⟨FiniteEncoding.intertwining _ e _ he, FiniteEncoding.readout_intertwining _ e _ he⟩

theorem phase_observed (live record : X) (h : live ≠ record)
    (e : Equiv.Perm (n ⊕ n)) (z : ℂ) :
    Obs (encoding live record) (phase ((extend live record h e).permMatrix ℂ) z)
      (phase (e.permMatrix ℂ) z) := by
  have he := permutation_observed live record h e
  exact NativeObservation.add
    (NativeObservation.smul (1/2) (NativeObservation.add NativeObservation.one he))
    (NativeObservation.smul z
      (NativeObservation.smul (1/2) (NativeObservation.sub NativeObservation.one he)))

def controlledMatrix (live record : X) (h : live ≠ record) (e : Equiv.Perm n) :=
  (extend live record h (controlled e)).permMatrix ℂ

def exchangeMatrix (live record : X) (h : live ≠ record) :=
  (extend (n := n) live record h (Equiv.sumComm n n)).permMatrix ℂ

def circuit (live record : X) (h : live ≠ record) (e : Equiv.Perm n) (z : ℂ) :=
  phase (controlledMatrix live record h e) (-Complex.I) *
    phase (exchangeMatrix (n := n) live record h) (-Complex.I) *
    phase (controlledMatrix live record h e) z *
    phase (exchangeMatrix (n := n) live record h) Complex.I *
    phase (controlledMatrix live record h e) Complex.I

/-- Exact comparison semantics for the complete ambient field. -/
theorem circuit_observed (live record : X) (h : live ≠ record) (e : Equiv.Perm n)
    (he : Function.Involutive e) (z : ℂ) :
    Obs (encoding live record) (circuit live record h e z)
      (CoherentComparisonRepair.compare (phase (e.permMatrix ℂ) z)) := by
  have hd (w : ℂ) := phase_observed live record h (controlled e) w
  have hx (w : ℂ) := phase_observed live record h (Equiv.sumComm n n) w
  simp only [controlled, ← ComparisonFactorization.ctrl_permutation] at hd
  rw [← exchange_permutation] at hx
  have ht := NativeObservation.mul (NativeObservation.mul (NativeObservation.mul
    (NativeObservation.mul (hd (-Complex.I)) (hx (-Complex.I))) (hd z))
    (hx Complex.I)) (hd Complex.I)
  rw [phase_ctrl (e.permMatrix ℂ) z,
    InvolutionComparison.circuit _ (RootTransferPhase.permutation_square e he)] at ht
  exact ht

omit [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n] in
theorem extend_involutive (live record : X) (h : live ≠ record)
    (e : Equiv.Perm (n ⊕ n)) (he : Function.Involutive e) :
    Function.Involutive (extend live record h e) := by
  have hs : e * e = 1 := by ext i; exact he i
  have hh := congrArg (Equiv.Perm.viaEmbeddingHom (ports live record h)) hs
  simp only [map_mul, map_one, Equiv.Perm.viaEmbeddingHom_apply] at hh
  intro i
  exact congrArg (fun d : Equiv.Perm (X × n) => d i) hh

theorem phase_unitary_on_pair (live record : X) (h : live ≠ record)
    (e : Equiv.Perm (n ⊕ n)) (he : Function.Involutive e) (z : ℂ) (hz : star z * z = 1) :
    phase ((extend live record h e).permMatrix ℂ) z ∈ unitary (Matrix (X × n) (X × n) ℂ) :=
  InvolutionComparison.phase_unitary _
    (RootTransferPhase.permutation_square _ (extend_involutive live record h e he))
    (RootTransferPhase.permutation_hermitian _ (extend_involutive live record h e he)) z hz

theorem circuit_unitary (live record : X) (h : live ≠ record) (e : Equiv.Perm n)
    (he : Function.Involutive e) (z : ℂ) (hz : star z * z = 1) :
    circuit live record h e z ∈ unitary (Matrix (X × n) (X × n) ℂ) := by
  have hd := phase_unitary_on_pair live record h (controlled e) (controlled_involutive e he)
  have hs : Function.Involutive (Equiv.sumComm n n) := by
    intro i; rcases i with i | i <;> rfl
  have hx := phase_unitary_on_pair live record h (Equiv.sumComm n n) hs
  have hm : star (-Complex.I) * (-Complex.I) = 1 := by simp
  have hp : star Complex.I * Complex.I = 1 := by simp
  exact (unitary _).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem
    ((unitary _).mul_mem (hd _ hm) (hx _ hm)) (hd z hz)) (hx _ hp)) (hd _ hp)

omit [Fintype X] [DecidableEq X] [Fintype n] [DecidableEq n] in
/-- Every extended native permutation fixes all registers outside the allocated pair. -/
theorem outside_fixed (live record : X) (h : live ≠ record) (e : Equiv.Perm (n ⊕ n))
    (x : X) (j : n) (hl : x ≠ live) (hr : x ≠ record) :
    extend live record h e (x, j) = (x, j) := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  rcases i with i | i
  · exact hl (congrArg Prod.fst hi).symm
  · exact hr (congrArg Prod.fst hi).symm

/-- Spectral phases also fix outside cells exactly, including their phase. -/
theorem outside_phase_basis (live record : X) (h : live ≠ record)
    (e : Equiv.Perm (n ⊕ n)) (z : ℂ) (x : X) (j : n) (hl : x ≠ live) (hr : x ≠ record) :
    phase ((extend live record h e).permMatrix ℂ) z *ᵥ Pi.single (x, j) 1 = Pi.single (x, j) 1 := by
  have hf := outside_fixed live record h e x j hl hr
  have he : (extend live record h e).permMatrix ℂ *ᵥ Pi.single (x, j) 1 = Pi.single (x, j) 1 := by
    rw [permMatrix_mulVec]
    ext q
    have hh : extend live record h e q = (x, j) ↔ q = (x, j) := by
      constructor
      · intro heq
        exact (extend live record h e).injective (heq.trans hf.symm)
      · rintro rfl
        exact hf
    simp only [Function.comp_apply, Pi.single_apply, hh]
  simp only [phase, InvolutionSpectral.plus, InvolutionSpectral.minus, add_mulVec,
    smul_mulVec, sub_mulVec, one_mulVec, he, sub_self, smul_zero, add_zero]
  module

theorem outside_circuit_basis (live record : X) (h : live ≠ record)
    (e : Equiv.Perm n) (z : ℂ) (x : X) (j : n) (hl : x ≠ live) (hr : x ≠ record) :
    circuit live record h e z *ᵥ Pi.single (x, j) 1 = Pi.single (x, j) 1 := by
  have hf (g : Equiv.Perm (n ⊕ n)) (w : ℂ) := outside_phase_basis live record h g w x j hl hr
  simp only [circuit, controlledMatrix, exchangeMatrix, ← mulVec_mulVec, hf]

end PMAction.SpatialComparison
