import PMAction.CommonResponse
import PMAction.LinkExpansion
import PMAction.TensorObservation
import PMAction.IsometricDynamics

/-!
# Comparing two admitted updates in opposite orders

Use the existing link comparison to compare ABψ with BAψ. With unitary A,B
this is exactly a state comparison after the reversible loop (AB)†BA. The
sum over a complete orthonormal coordinate ensemble is the squared Frobenius
norm of AB−BA divided by four; it vanishes exactly when the updates commute.
Native observation carries the same loop to its readout without feedback.

Admission/preparation of this comparison, its necessity in a physical update,
the primitive lengths of A,B and the event price are not derived. Four routine
calls in the loop are not asserted to be four primitive substrate events.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.OrderComparison
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def flag (A B : Matrix n n ℂ) (ψ : n → ℂ) : ℝ :=
  CommonResponse.linkFlag (B*A) ψ ((A*B) *ᵥ ψ)

def compareLoop (A B : Matrix n n ℂ) : Matrix n n ℂ := (A*B)ᴴ * (B*A)

def total (A B : Matrix n n ℂ) : ℝ := ∑ a, flag A B (Pi.single a 1)

theorem loop_unitary (A B : Matrix n n ℂ) (hA : A ∈ unitary _) (hB : B ∈ unitary _) :
    compareLoop A B ∈ unitary _ :=
  (unitary _).mul_mem (Unitary.star_mem ((unitary _).mul_mem hA hB))
    ((unitary _).mul_mem hB hA)

theorem flag_eq_stateFlag (A B : Matrix n n ℂ) (hA : A ∈ unitary _)
    (hB : B ∈ unitary _) (ψ : n → ℂ) :
    flag A B ψ = CommonResponse.stateFlag (compareLoop A B) ψ := by
  have hu := (unitary (Matrix n n ℂ)).mul_mem hA hB
  have hr : (A*B)*(A*B)ᴴ=1 := hu.2
  have he : (A*B) *ᵥ (ψ - compareLoop A B *ᵥ ψ) = (A*B)*ᵥ ψ - (B*A)*ᵥ ψ := by
    rw [mulVec_sub, mulVec_mulVec, compareLoop, ← Matrix.mul_assoc, hr, one_mul]
  unfold flag CommonResponse.linkFlag CommonResponse.stateFlag
  rw [← he, LinkExpansion.unitary_nsq' (A*B) hu.1]

theorem flag_single (A B : Matrix n n ℂ) (a : n) :
    flag A B (Pi.single a 1) = (∑ i, Complex.normSq ((A*B-B*A) i a))/4 := by
  unfold flag CommonResponse.linkFlag
  rw [← sub_mulVec, LinkExpansion.nsq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem total_formula (A B : Matrix n n ℂ) :
    total A B = (∑ i, ∑ j, Complex.normSq ((A*B-B*A) i j))/4 := by
  simp only [total, flag_single]
  rw [← Finset.sum_div, Finset.sum_comm]

theorem total_nonneg (A B : Matrix n n ℂ) : 0 ≤ total A B := by
  rw [total_formula]
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (by norm_num)

theorem total_zero_iff (A B : Matrix n n ℂ) : total A B = 0 ↔ A*B=B*A := by
  constructor
  · intro h
    have hs : (∑ i, ∑ j, Complex.normSq ((A*B-B*A) i j)) = 0 := by
      rw [total_formula] at h
      linarith
    have hz : A*B-B*A=0 := by
      ext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg ((A*B-B*A) i j))).mp hs i (Finset.mem_univ i)
      have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        Complex.normSq_nonneg ((A*B-B*A) i j))).mp hi j (Finset.mem_univ j)
      exact Complex.normSq_eq_zero.mp hij
    exact sub_eq_zero.mp hz
  · intro h
    simp [total_formula, h]

theorem total_pos_iff (A B : Matrix n n ℂ) : 0 < total A B ↔ A*B≠B*A := by
  rw [lt_iff_le_and_ne]
  simp only [total_nonneg, true_and, ne_eq, eq_comm (a := (0:ℝ)), total_zero_iff]

/-- The loop inherits the established native all-state observation identities. -/
theorem observed_loop {a b : Type*} [Fintype a] [Fintype b]
    (E : Matrix a b ℂ) (A B : Matrix a a ℂ) (C D : Matrix b b ℂ)
    (hA : NativeObservation.Obs E A C) (hB : NativeObservation.Obs E B D) :
    NativeObservation.Obs E ((A*B)ᴴ*(B*A)) ((C*D)ᴴ*(D*C)) :=
  NativeObservation.mul (NativeObservation.star (NativeObservation.mul hA hB))
    (NativeObservation.mul hB hA)

/-- On prepared encoded states the actual comparison flag is preserved, not just
the compressed loop matrix. The isometry and both observation identities are explicit. -/
theorem encoded_flag {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (E : Matrix a b ℂ) (hE : Eᴴ*E=1) (A B : Matrix a a ℂ) (C D : Matrix b b ℂ)
    (hA : NativeObservation.Obs E A C) (hB : NativeObservation.Obs E B D) (ψ : b → ℂ) :
    flag A B (E *ᵥ ψ) = flag C D ψ := by
  have hAB := NativeObservation.mul hA hB
  have hBA := NativeObservation.mul hB hA
  have hd : (A*B)*ᵥ (E*ᵥ ψ) - (B*A)*ᵥ (E*ᵥ ψ) =
      E*ᵥ ((C*D)*ᵥ ψ - (D*C)*ᵥ ψ) := by
    calc
      _ = ((A*B)*E)*ᵥ ψ - ((B*A)*E)*ᵥ ψ := by rw [mulVec_mulVec, mulVec_mulVec]
      _ = (E*(C*D))*ᵥ ψ - (E*(D*C))*ᵥ ψ := by rw [hAB.1, hBA.1]
      _ = _ := by simp only [mulVec_sub, mulVec_mulVec]
  unfold flag CommonResponse.linkFlag
  rw [hd, IsometricDynamics.population E hE]

end PMAction.OrderComparison
