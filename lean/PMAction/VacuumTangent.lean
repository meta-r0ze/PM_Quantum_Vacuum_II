import PMAction.VacuumErrorRate
import PMAction.RotationAlgebra

/-! The actual near-origin momentum tangent on the four vacuum coordinates.
Nondegeneracy of this tangent is not yet a nonlinear fixed-space exclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.VacuumTangent
open Matrix ConcreteFermion LocalUnitary RotationAlgebra
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

def alpha8 (j : Fin 3) : M := fromBlocks (alpha j) 0 0 (alpha j)
def vacuumIndex : Fin 4 → Sites := ![.inl 0, .inl 1, .inr 2, .inr 3]
def compress (A : M) : Spin := A.submatrix vacuumIndex vacuumIndex

theorem compress_add (A B : M) : compress (A+B)=compress A+compress B := rfl
theorem compress_smul (c : ℂ) (A : M) : compress (c • A)=c • compress A := rfl

theorem compress_alpha8 (j : Fin 3) : compress (alpha8 j)=alpha j := by
  fin_cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [compress, vacuumIndex, alpha8, alpha, submatrix]

set_option maxHeartbeats 1000000 in
theorem compress_alpha_beta (j : Fin 3) : compress (alpha8 j*VacuumSplit.beta8)=0 := by
  fin_cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [compress, vacuumIndex, alpha8, alpha, VacuumSplit.beta8, beta, submatrix,
      mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four]

theorem compress_alpha_rotation (j : Fin 3) (t : ℝ) :
    compress (alpha8 j*rotation VacuumSplit.beta8 t)=(Real.cos t : ℂ) • alpha j := by
  simp only [rotation, mul_add, mul_smul_comm, mul_one, compress_add, compress_smul,
    compress_alpha8, compress_alpha_beta, smul_zero, add_zero]

theorem beta_alpha (j : Fin 3) : VacuumSplit.beta8*alpha8 j = -(alpha8 j*VacuumSplit.beta8) := by
  have h : beta*alpha j=-(alpha j*beta) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using clifford.2.2.2 j
  simp [VacuumSplit.beta8, alpha8, fromBlocks_multiply, h, fromBlocks_neg]

theorem projector_hermitian : VacuumSplit.vacuumProjector.IsHermitian := by
  simp [IsHermitian, VacuumSplit.vacuumProjector, fromBlocks_conjTranspose,
    DomainWallSpectrum.plus, DomainWallSpectrum.minus, conjTranspose_smul,
    gamma_hermitian.eq]

theorem projector_wallCoin (t : ℝ) :
    VacuumSplit.vacuumProjector*VacuumSplit.wallCoin t=VacuumSplit.vacuumProjector := by
  have hc := congrArg conjTranspose (VacuumSplit.wallCoin_projector t)
  rw [conjTranspose_mul, projector_hermitian.eq] at hc
  have hh := congrArg (fun A : M => A*VacuumSplit.wallCoin t) hc
  have hu : (VacuumSplit.wallCoin t)ᴴ*VacuumSplit.wallCoin t=1 :=
    (VacuumSplit.wallCoin_unitary t).1
  rw [Matrix.mul_assoc, hu, mul_one] at hh
  exact hh.symm

set_option maxHeartbeats 1000000 in
theorem compress_projector (A : M) : compress (VacuumSplit.vacuumProjector*A)=compress A := by
  ext i j
  fin_cases i <;>
    norm_num [compress, submatrix, vacuumIndex, VacuumSplit.vacuumProjector,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, gamma, mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_four, one_apply]

theorem compress_wallCoin (t : ℝ) (A : M) : compress (VacuumSplit.wallCoin t*A)=compress A := by
  have h := congrArg (fun B : M => compress (B*A)) (projector_wallCoin t)
  rw [Matrix.mul_assoc, compress_projector, compress_projector] at h
  exact h

theorem direction_eq (j : Fin 3) (q : ℝ) :
    WilsonSplit.directionSymbol j q = (Real.cos q : ℝ) • VacuumSplit.beta8-
      (Real.sin q : ℝ) • alpha8 j := by
  ext x y
  cases x <;> cases y <;>
    simp [WilsonSplit.directionSymbol, VacuumSplit.beta8, alpha8]

def insertion (t : ℝ) (p : Fin 3 → ℝ) (j : Fin 3) : M :=
  (-Complex.I*(Real.sin t : ℂ)*(p j : ℂ)) • alpha8 j

theorem factor_deriv (j : Fin 3) (t : ℝ) (p : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => rotation (WilsonSplit.directionSymbol j (s*p j)) t)
      (insertion t p j) 0 := by
  have hc := ((Real.hasDerivAt_cos ((0 : ℝ)*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j)))
  have hs := ((Real.hasDerivAt_sin ((0 : ℝ)*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j)))
  simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul, Function.comp_def, id_eq] at hc hs
  have hd := (hc.smul_const VacuumSplit.beta8).sub (hs.smul_const (alpha8 j))
  have hr := (hd.const_smul (Complex.I*(Real.sin t : ℂ))).const_add ((Real.cos t : ℂ) • (1 : M))
  have hv : (Complex.I*(Real.sin t : ℂ)) • ((0 : ℝ) • VacuumSplit.beta8-(p j) • alpha8 j) =
      insertion t p j := by
    rw [zero_smul, zero_sub, smul_neg]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    simp only [insertion, neg_smul, neg_mul]
    rfl
  rw [hv] at hr
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [rotation, direction_eq, Pi.sub_def, Pi.smul_def] using hr.tendsto_slope

def rawTangent (t : ℝ) (p : Fin 3 → ℝ) : M :=
  ((VacuumSplit.onsiteCoin t*insertion t p 0*VacuumSplit.rotation t+
    (VacuumSplit.onsiteCoin t*VacuumSplit.rotation t)*insertion t p 1)*VacuumSplit.rotation t)+
    ((VacuumSplit.onsiteCoin t*VacuumSplit.rotation t)*VacuumSplit.rotation t)*insertion t p 2

theorem momentum_deriv (t : ℝ) (p : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => VacuumSplit.momentumUpdate (fun j => s*p j) t)
      (rawTangent t p) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (VacuumSplit.onsiteCoin t)).mul
    (factor_deriv 0 t p)).mul (factor_deriv 1 t p)).mul (factor_deriv 2 t p)
  simpa only [VacuumSplit.momentumUpdate, rawTangent, Pi.mul_def, Pi.mul_apply, zero_mul,
    VacuumSplit.direction_zero, zero_add, VacuumSplit.rotation] using h

theorem onsite_eq (t : ℝ) : VacuumSplit.onsiteCoin t =
    VacuumSplit.wallCoin t*rotation VacuumSplit.beta8 (-(3*t)) := by
  rw [VacuumSplit.onsiteCoin, VacuumSplit.rotation,
    rotation_adjoint _ VacuumSplit.beta8_hermitian,
    rotation_nsmul _ VacuumSplit.beta8_square]
  congr 2
  norm_num

theorem inserted_rotation (j : Fin 3) (x y : ℝ) (c : ℂ) :
    (rotation VacuumSplit.beta8 (-x)*(c • alpha8 j))*rotation VacuumSplit.beta8 y =
      c • (alpha8 j*rotation VacuumSplit.beta8 (x+y)) := by
  rw [mul_smul_comm, rotation_transport _ _ (beta_alpha j), smul_mul_assoc,
    Matrix.mul_assoc, rotation_add _ VacuumSplit.beta8_square]

def normalTangent (t : ℝ) (p : Fin 3 → ℝ) : M :=
  (-Complex.I*(Real.sin t : ℂ)) •
    ((p 0 : ℂ) • (alpha8 0*rotation VacuumSplit.beta8 (5*t))+
     (p 1 : ℂ) • (alpha8 1*rotation VacuumSplit.beta8 (3*t))+
     (p 2 : ℂ) • (alpha8 2*rotation VacuumSplit.beta8 t))

theorem tangent_normal (t : ℝ) (p : Fin 3 → ℝ) :
    rawTangent t p=VacuumSplit.wallCoin t*normalTangent t p := by
  have h2 : rotation VacuumSplit.beta8 t*rotation VacuumSplit.beta8 t =
      rotation VacuumSplit.beta8 (2*t) := by
    rw [rotation_add _ VacuumSplit.beta8_square]
    congr 1
    ring
  have h32 : rotation VacuumSplit.beta8 (-(3*t))*rotation VacuumSplit.beta8 t =
      rotation VacuumSplit.beta8 (-(2*t)) := by
    rw [rotation_add _ VacuumSplit.beta8_square]
    congr 1
    ring
  have h21 : rotation VacuumSplit.beta8 (-(2*t))*rotation VacuumSplit.beta8 t =
      rotation VacuumSplit.beta8 (-t) := by
    rw [rotation_add _ VacuumSplit.beta8_square]
    congr 1
    ring
  have hi : rawTangent t p = VacuumSplit.wallCoin t*
      (((rotation VacuumSplit.beta8 (-(3*t))*insertion t p 0)*
          (rotation VacuumSplit.beta8 t*rotation VacuumSplit.beta8 t))+
       ((rotation VacuumSplit.beta8 (-(3*t))*rotation VacuumSplit.beta8 t)*
          insertion t p 1)*rotation VacuumSplit.beta8 t+
       ((rotation VacuumSplit.beta8 (-(3*t))*rotation VacuumSplit.beta8 t)*
          rotation VacuumSplit.beta8 t)*insertion t p 2) := by
    rw [rawTangent, onsite_eq]
    unfold VacuumSplit.rotation
    noncomm_ring
  rw [hi, h2, h32, h21]
  have ht0 : 3*t+2*t=5*t := by ring
  have ht1 : 2*t+t=3*t := by ring
  have ht2 : t+0=t := by ring
  have hz : rotation VacuumSplit.beta8 (-t)*insertion t p 2 =
      (-Complex.I*(Real.sin t : ℂ)*(p 2 : ℂ)) •
        (alpha8 2*rotation VacuumSplit.beta8 t) := by
    have he := inserted_rotation 2 t 0 (-Complex.I*(Real.sin t : ℂ)*(p 2 : ℂ))
    simpa only [rotation_zero, mul_one, add_zero, insertion] using he
  rw [insertion, inserted_rotation 0 (3*t) (2*t), ht0]
  rw [insertion, inserted_rotation 1 (2*t) t, ht1, hz]
  congr 1
  simp only [normalTangent, smul_add, smul_smul]

/-- The finite-tick vacuum velocities retain the ordering of the three factors. -/
def weights (t : ℝ) : Fin 3 → ℝ :=
  ![Real.sin t*Real.cos (5*t), Real.sin t*Real.cos (3*t), Real.sin t*Real.cos t]

def principal (t : ℝ) (p : Fin 3 → ℝ) : Spin :=
  Dirac.H alpha beta (fun j => weights t j*p j) 0

theorem compressed_tangent (t : ℝ) (p : Fin 3 → ℝ) :
    compress (rawTangent t p)=(-Complex.I) • principal t p := by
  rw [tangent_normal, compress_wallCoin]
  simp only [normalTangent, compress_smul, compress_add, compress_alpha_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principal, Dirac.H, weights, alpha, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ)] <;> ring

def compressLinear : M →ₗ[ℝ] Spin where
  toFun := compress
  map_add' := compress_add
  map_smul' _ _ := rfl

def compressCLM : M →L[ℝ] Spin := compressLinear.toContinuousLinearMap

/-- Actual directional derivative of the compressed split, not an imposed Dirac ansatz. -/
theorem compressed_deriv (t : ℝ) (p : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => compress (VacuumSplit.momentumUpdate (fun j => s*p j) t))
      ((-Complex.I) • principal t p) 0 := by
  have h := compressCLM.hasFDerivAt.comp_hasDerivAt 0 (momentum_deriv t p)
  have he : (compressCLM : M → Spin)=compress := LinearMap.coe_toContinuousLinearMap' compressLinear
  rw [he, compressed_tangent] at h
  simpa only [Function.comp_def] using h

end PMAction.VacuumTangent
