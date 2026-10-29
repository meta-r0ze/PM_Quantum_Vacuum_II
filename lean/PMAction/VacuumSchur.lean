import PMAction.VacuumPrincipal
import PMAction.VacuumFixedSpace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Exact elimination of the four complementary components near the vacuum.
The remaining nonlinear spectral question is invertibility of the Schur complement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumSchur
open Matrix ConcreteFermion VacuumTangent Filter Topology
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

def complementIndex : Fin 4 → Sites := ![.inl 2, .inl 3, .inr 0, .inr 1]
def complementState (u : Fin 4 → ℂ) : Sites → ℂ :=
  Sum.elim ![0,0,u 0,u 1] ![u 2,u 3,0,0]

def basisIndex : (Fin 4 ⊕ Fin 4) → Sites := Sum.elim vacuumIndex complementIndex
def basisEquiv : (Fin 4 ⊕ Fin 4) ≃ Sites := Equiv.ofBijective basisIndex (by decide)

def defect (t : ℝ) (k : Fin 3 → ℝ) : M := VacuumSplit.momentumUpdate k t-1

def blockA (t : ℝ) (k : Fin 3 → ℝ) : Spin := (defect t k).submatrix vacuumIndex vacuumIndex
def blockB (t : ℝ) (k : Fin 3 → ℝ) : Spin := (defect t k).submatrix vacuumIndex complementIndex
def blockC (t : ℝ) (k : Fin 3 → ℝ) : Spin := (defect t k).submatrix complementIndex vacuumIndex
def blockD (t : ℝ) (k : Fin 3 → ℝ) : Spin := (defect t k).submatrix complementIndex complementIndex

theorem block_decomposition (t : ℝ) (k : Fin 3 → ℝ) :
    (defect t k).submatrix basisEquiv basisEquiv = fromBlocks (blockA t k) (blockB t k)
      (blockC t k) (blockD t k) := by
  ext i j
  cases i <;> cases j <;> rfl

set_option maxHeartbeats 1000000 in
theorem projector_row (A : M) (i : Fin 4) (y : Sites) :
    (VacuumSplit.vacuumProjector*A) (vacuumIndex i) y=A (vacuumIndex i) y := by
  fin_cases i <;> norm_num [VacuumSplit.vacuumProjector, vacuumIndex,
    DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma, mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_four]

set_option maxHeartbeats 1000000 in
theorem projector_col (A : M) (x : Sites) (i : Fin 4) :
    (A*VacuumSplit.vacuumProjector) x (vacuumIndex i)=A x (vacuumIndex i) := by
  fin_cases i <;> norm_num [VacuumSplit.vacuumProjector, vacuumIndex,
    DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma, mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_four]

theorem projector_vac_row (i : Fin 4) (y : Sites) :
    VacuumSplit.vacuumProjector (vacuumIndex i) y=(1 : M) (vacuumIndex i) y := by
  fin_cases i <;> cases y <;> rename_i j <;> fin_cases j <;>
    norm_num [VacuumSplit.vacuumProjector, vacuumIndex,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma, Matrix.one_apply]

theorem projector_vac_col (x : Sites) (i : Fin 4) :
    VacuumSplit.vacuumProjector x (vacuumIndex i)=(1 : M) x (vacuumIndex i) := by
  fin_cases i <;> cases x <;> rename_i j <;> fin_cases j <;>
    norm_num [VacuumSplit.vacuumProjector, vacuumIndex,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma, Matrix.one_apply]

theorem origin_vac_row (t : ℝ) (i : Fin 4) (y : Sites) : defect t 0 (vacuumIndex i) y=0 := by
  have hh := congrArg (fun A : M => A (vacuumIndex i) y) (projector_wallCoin t)
  rw [projector_row, projector_vac_row] at hh
  simp only [defect, VacuumSplit.origin_update, Matrix.sub_apply, hh, sub_self]

theorem origin_vac_col (t : ℝ) (x : Sites) (i : Fin 4) : defect t 0 x (vacuumIndex i)=0 := by
  have hh := congrArg (fun A : M => A x (vacuumIndex i)) (VacuumSplit.wallCoin_projector t)
  rw [projector_col, projector_vac_col] at hh
  simp only [defect, VacuumSplit.origin_update, Matrix.sub_apply, hh, sub_self]

theorem blockA_zero (t : ℝ) : blockA t 0=0 := by
  ext i j
  exact origin_vac_row t i (vacuumIndex j)

theorem blockB_zero (t : ℝ) : blockB t 0=0 := by
  ext i j
  exact origin_vac_row t i (complementIndex j)

theorem blockC_zero (t : ℝ) : blockC t 0=0 := by
  ext i j
  exact origin_vac_col t (complementIndex i) j

set_option maxHeartbeats 1000000 in
theorem complement_action (t : ℝ) (u : Fin 4 → ℂ) :
    defect t 0*ᵥcomplementState u=complementState (blockD t 0*ᵥu) := by
  have h0 (y : Sites) : defect t 0 (.inl 0) y=0 := origin_vac_row t 0 y
  have h1 (y : Sites) : defect t 0 (.inl 1) y=0 := origin_vac_row t 1 y
  have h2 (y : Sites) : defect t 0 (.inr 2) y=0 := origin_vac_row t 2 y
  have h3 (y : Sites) : defect t 0 (.inr 3) y=0 := origin_vac_row t 3 y
  ext x
  cases x <;> rename_i i <;> fin_cases i <;>
    simp [complementState, blockD, complementIndex, submatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_four, h0, h1, h2, h3, add_assoc]

theorem blockD_isUnit (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) : IsUnit (blockD t 0) := by
  have hker (u : Fin 4 → ℂ) (hu : blockD t 0*ᵥu=0) : u=0 := by
    have hh := complement_action t u
    rw [hu] at hh
    have hf : VacuumSplit.momentumUpdate 0 t*ᵥcomplementState u=complementState u := by
      have hz : complementState (0 : Fin 4 → ℂ)=0 := by
        ext x
        cases x <;> rename_i i <;> fin_cases i <;> rfl
      rw [hz] at hh
      simpa only [defect, sub_mulVec, one_mulVec, sub_eq_zero] using hh
    have hc := (VacuumFixedSpace.origin_fixed_coordinates t ht hb (complementState u)).mp hf
    have hc' : u 0=0 ∧ u 1=0 ∧ u 2=0 ∧ u 3=0 := by simpa [complementState] using hc
    ext i
    fin_cases i
    · exact hc'.1
    · exact hc'.2.1
    · exact hc'.2.2.1
    · exact hc'.2.2.2
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v he
  exact sub_eq_zero.mp (hker (u-v) (by rw [mulVec_sub, he, sub_self]))

def schur (t : ℝ) (k : Fin 3 → ℝ) : Spin :=
  blockA t k-blockB t k*(blockD t k)⁻¹*blockC t k

theorem defect_isUnit_iff_schur (t : ℝ) (k : Fin 3 → ℝ) (hD : IsUnit (blockD t k)) :
    IsUnit (defect t k) ↔ IsUnit (schur t k) := by
  let := hD.invertible
  rw [← Matrix.isUnit_submatrix_equiv basisEquiv basisEquiv, block_decomposition]
  simpa only [schur, Matrix.invOf_eq_nonsing_inv] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := blockA t k) (B := blockB t k)
      (C := blockC t k) (D := blockD t k))

theorem continuous_update (t : ℝ) : Continuous (fun k : Fin 3 → ℝ => VacuumSplit.momentumUpdate k t) := by
  unfold VacuumSplit.momentumUpdate LocalUnitary.rotation
  simp only [direction_eq]
  fun_prop

theorem continuous_blockD (t : ℝ) : Continuous (blockD t) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply (complementIndex j)).comp
    ((continuous_apply (complementIndex i)).comp ((continuous_update t).sub continuous_const))

theorem gapped_neighborhood (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) :
    ∃ r : ℝ, 0<r ∧ ∀ k : Fin 3 → ℝ, ‖k‖<r → IsUnit (blockD t k) := by
  have he : ∀ᶠ k in 𝓝 (0 : Fin 3 → ℝ), IsUnit (blockD t k) :=
    (continuous_blockD t).continuousAt.tendsto.eventually
      (Units.isOpen.mem_nhds (blockD_isUnit t ht hb))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r, hr, fun k hk => h (by simpa only [dist_zero_right] using hk)⟩

def submatrixLinear (r c : Fin 4 → Sites) : M →ₗ[ℝ] Spin where
  toFun A := A.submatrix r c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def submatrixCLM (r c : Fin 4 → Sites) : M →L[ℝ] Spin :=
  (submatrixLinear r c).toContinuousLinearMap

theorem block_deriv (r c : Fin 4 → Sites) (t : ℝ) (p : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => (defect t (fun j => s*p j)).submatrix r c)
      ((rawTangent t p).submatrix r c) 0 := by
  have hd := (momentum_deriv t p).sub_const (1 : M)
  have h := (submatrixCLM r c).hasFDerivAt.comp_hasDerivAt 0 hd
  have he : (submatrixCLM r c : M → Spin)=(fun A : M => A.submatrix r c) :=
    LinearMap.coe_toContinuousLinearMap' (submatrixLinear r c)
  rw [he] at h
  simpa only [defect, Function.comp_def] using h

theorem schur_zero (t : ℝ) : schur t 0=0 := by
  simp only [schur, blockA_zero, blockB_zero, blockC_zero, zero_mul, sub_zero]

set_option maxHeartbeats 1000000 in
/-- Eliminating the complementary components does not alter the leading vacuum tangent. -/
theorem schur_deriv (t : ℝ) (ht : t ≠ 0) (hb : |t|≤1/2) (p : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => schur t (fun j => s*p j))
      ((-Complex.I) • VacuumTangent.principal t p) 0 := by
  have hA := block_deriv vacuumIndex vacuumIndex t p
  have hB := block_deriv vacuumIndex complementIndex t p
  have hC := block_deriv complementIndex vacuumIndex t p
  have hD := block_deriv complementIndex complementIndex t p
  change HasDerivAt (fun s : ℝ => blockA t (fun j => s*p j))
    (compress (rawTangent t p)) 0 at hA
  change HasDerivAt (fun s : ℝ => blockB t (fun j => s*p j)) _ 0 at hB
  change HasDerivAt (fun s : ℝ => blockC t (fun j => s*p j)) _ 0 at hC
  change HasDerivAt (fun s : ℝ => blockD t (fun j => s*p j)) _ 0 at hD
  have hi : DifferentiableAt ℝ (fun s : ℝ => (blockD t (fun j => s*p j))⁻¹) 0 := by
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    apply hD.differentiableAt.inverse
    simp only [zero_mul, ← Pi.zero_def]
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (blockD_isUnit t ht hb)
    refine ⟨⟨blockD t 0, (blockD t 0)⁻¹, ?_, ?_⟩, rfl⟩
    · exact Matrix.mul_nonsing_inv _ hdet
    · exact Matrix.nonsing_inv_mul _ hdet
  have hs := hA.sub ((hB.mul hi.hasDerivAt).mul hC)
  simpa only [schur, Pi.sub_def, Pi.mul_def, zero_mul, ← Pi.zero_def, blockB_zero, blockC_zero,
    mul_zero, zero_mul, add_zero, sub_zero, compressed_tangent] using hs

end PMAction.VacuumSchur
