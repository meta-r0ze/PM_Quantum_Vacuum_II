import PMAction.NormalizedIncrement

/-! Jointly analytic Schur reduction of the normalized time increment. The
complementary block is invertible even at the extended zero tick. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NormalizedSchur
open Matrix ConcreteFermion VacuumTangent NormalizedIncrement Filter Topology
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

def A (z : Joint) : Spin := (increment z).submatrix vacuumIndex vacuumIndex
def B (z : Joint) : Spin := (increment z).submatrix vacuumIndex VacuumSchur.complementIndex
def C (z : Joint) : Spin := (increment z).submatrix VacuumSchur.complementIndex vacuumIndex
def D (z : Joint) : Spin := (increment z).submatrix VacuumSchur.complementIndex VacuumSchur.complementIndex

theorem analytic_block (r c : Fin 4 → Sites) :
    AnalyticAt ℝ (fun z : Joint => (increment z).submatrix r c) 0 := by
  have hh := (VacuumSchur.submatrixCLM r c).analyticAt (increment 0)
  have h := hh.comp (f := increment) (x := 0) analytic_increment
  have he : (VacuumSchur.submatrixCLM r c : M → Spin)=(fun X : M => X.submatrix r c) :=
    LinearMap.coe_toContinuousLinearMap' (VacuumSchur.submatrixLinear r c)
  rw [he] at h
  simpa only [Function.comp_def] using! h

theorem block_of_ne (r c : Fin 4 → Sites) (t : ℝ) (ht : t ≠ 0) (k : Momentum) :
    (increment (t,k)).submatrix r c=t⁻¹ • (VacuumSchur.defect t k).submatrix r c := by
  rw [increment_of_ne t ht]
  rfl

theorem axis_zero_of_punctured (f : Joint → Spin) (hf : AnalyticAt ℝ f 0)
    (hzero : ∀ t : ℝ, t ≠ 0 → f (t,0)=0) : ∀ t : ℝ, f (t,0)=0 := by
  intro t
  by_cases ht : t=0
  · subst t
    have hp : Tendsto (fun s : ℝ => (s,(0 : Momentum))) (𝓝 0) (𝓝 (0 : Joint)) :=
      tendsto_id.prodMk_nhds tendsto_const_nhds
    have hl : Tendsto (fun s : ℝ => f (s,0)) (𝓝[≠] 0) (𝓝 (f 0)) :=
      (hf.continuousAt.tendsto.comp hp).mono_left nhdsWithin_le_nhds
    have he : ∀ᶠ s : ℝ in 𝓝[≠] 0, f (s,0)=0 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hzero s hs
    have hz : Tendsto (fun s : ℝ => f (s,0)) (𝓝[≠] 0) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with s hs
      exact hs.symm
    exact tendsto_nhds_unique hl hz
  · exact hzero t ht

theorem A_axis_zero (t : ℝ) : A (t,0)=0 := by
  apply axis_zero_of_punctured A (analytic_block _ _)
  intro s hs
  change (increment (s,0)).submatrix vacuumIndex vacuumIndex=0
  rw [block_of_ne _ _ s hs]
  change s⁻¹ • VacuumSchur.blockA s 0=0
  rw [VacuumSchur.blockA_zero, smul_zero]

theorem B_axis_zero (t : ℝ) : B (t,0)=0 := by
  apply axis_zero_of_punctured B (analytic_block _ _)
  intro s hs
  change (increment (s,0)).submatrix vacuumIndex VacuumSchur.complementIndex=0
  rw [block_of_ne _ _ s hs]
  change s⁻¹ • VacuumSchur.blockB s 0=0
  rw [VacuumSchur.blockB_zero, smul_zero]

theorem C_axis_zero (t : ℝ) : C (t,0)=0 := by
  apply axis_zero_of_punctured C (analytic_block _ _)
  intro s hs
  change (increment (s,0)).submatrix VacuumSchur.complementIndex vacuumIndex=0
  rw [block_of_ne _ _ s hs]
  change s⁻¹ • VacuumSchur.blockC s 0=0
  rw [VacuumSchur.blockC_zero, smul_zero]

set_option maxHeartbeats 1000000 in
theorem D_origin : D 0=Complex.I • beta := by
  change (increment (0,0)).submatrix VacuumSchur.complementIndex VacuumSchur.complementIndex=_
  rw [increment_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [VacuumIteration.generator, hamiltonian, DomainWallSpectrum.H,
      DomainWallSpectrum.wilson, DomainWallSpectrum.momentum, DomainWallSpectrum.hop,
      DomainWallSpectrum.back, DomainWallSpectrum.plus, DomainWallSpectrum.minus,
      submatrix, VacuumSchur.complementIndex, beta, gamma, mul_apply,
      vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem D_origin_isUnit : IsUnit (D 0) := by
  rw [D_origin]
  refine ⟨⟨Complex.I • beta, (-Complex.I) • beta, ?_, ?_⟩, rfl⟩ <;>
    simp only [smul_mul_smul_comm, beta_square, mul_neg, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

theorem analytic_D_inverse : AnalyticAt ℝ (fun z : Joint => (D z)⁻¹) 0 := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact (analyticAt_inverse (𝕜 := ℝ) D_origin_isUnit.unit).comp (f := D) (x := 0) (analytic_block _ _)

def S (z : Joint) : Spin := A z-B z*(D z)⁻¹*C z

theorem analytic_S : AnalyticAt ℝ S 0 := by
  have h := (analytic_block vacuumIndex vacuumIndex).sub
    (((analytic_block vacuumIndex VacuumSchur.complementIndex).mul analytic_D_inverse).mul
      (analytic_block VacuumSchur.complementIndex vacuumIndex))
  simpa only [S, A, B, C, D, Pi.sub_def, Pi.mul_def] using! h

theorem S_axis_zero (t : ℝ) : S (t,0)=0 := by
  simp only [S, A_axis_zero, B_axis_zero, C_axis_zero, zero_mul, sub_zero]

theorem block_decomposition (z : Joint) :
    (increment z).submatrix VacuumSchur.basisEquiv VacuumSchur.basisEquiv = fromBlocks (A z) (B z) (C z) (D z) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem increment_isUnit_iff (z : Joint) (hD : IsUnit (D z)) : IsUnit (increment z) ↔ IsUnit (S z) := by
  let := hD.invertible
  rw [← Matrix.isUnit_submatrix_equiv VacuumSchur.basisEquiv VacuumSchur.basisEquiv, block_decomposition]
  simpa only [S, Matrix.invOf_eq_nonsing_inv] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := A z) (B := B z) (C := C z) (D := D z))

/-- The zero-tick momentum derivative of the normalized increment. -/
def kinetic8 (p : Momentum) : M := p 0 • alpha8 0+p 1 • alpha8 1+p 2 • alpha8 2

theorem direction_deriv (j : Fin 3) (p : Momentum) :
    HasDerivAt (fun s : ℝ => WilsonSplit.directionSymbol j (s*p j)) (-(p j • alpha8 j)) 0 := by
  have hc := (Real.hasDerivAt_cos ((0 : ℝ)*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j))
  have hs := (Real.hasDerivAt_sin ((0 : ℝ)*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j))
  have h := (hc.smul_const VacuumSplit.beta8).sub (hs.smul_const (alpha8 j))
  simpa only [direction_eq, Pi.sub_def, zero_mul, Real.sin_zero, Real.cos_zero,
    neg_zero, one_mul, zero_smul, zero_sub, Function.comp_def, id_eq] using! h

theorem generator_deriv (p : Momentum) :
    HasDerivAt (fun s : ℝ => VacuumIteration.generator (fun j => s*p j))
      ((-Complex.I) • kinetic8 p) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) WilsonSplit.onsiteHamiltonian).sub
    (direction_deriv 0 p)).sub (direction_deriv 1 p)).sub (direction_deriv 2 p)
  have hc := h.const_smul (-Complex.I)
  simpa only [VacuumIteration.generator, ← WilsonSplit.generator_identity, Fin.sum_univ_three,
    sub_add_eq_sub_sub, Pi.sub_def, Pi.smul_def, zero_sub, sub_neg_eq_add, zero_add, kinetic8] using! hc

theorem block_deriv_zero_tick (r c : Fin 4 → Sites) (p : Momentum) :
    HasDerivAt (fun s : ℝ => (increment (0,fun j => s*p j)).submatrix r c)
      (((-Complex.I) • kinetic8 p).submatrix r c) 0 := by
  have h := (VacuumSchur.submatrixCLM r c).hasFDerivAt.comp_hasDerivAt 0 (generator_deriv p)
  have he : (VacuumSchur.submatrixCLM r c : M → Spin)=(fun X : M => X.submatrix r c) :=
    LinearMap.coe_toContinuousLinearMap' (VacuumSchur.submatrixLinear r c)
  rw [he] at h
  simpa only [Function.comp_def, increment_zero] using! h

/-- The four-component isotropic symbol at the extended zero tick. -/
def kinetic (p : Momentum) : Spin := Dirac.H alpha beta p 0

theorem compress_kinetic (p : Momentum) : compress (kinetic8 p)=kinetic p := by
  change compress (p 0 • alpha8 0+p 1 • alpha8 1+p 2 • alpha8 2)=_
  have hs (a : ℝ) (X : M) : compress (a • X)=a • compress X := rfl
  simp only [compress_add, hs, compress_alpha8, kinetic, Dirac.H, zero_smul, add_zero]

theorem S_momentum_deriv (p : Momentum) :
    HasDerivAt (fun s : ℝ => S (0,fun j => s*p j)) ((-Complex.I) • kinetic p) 0 := by
  have hA := block_deriv_zero_tick vacuumIndex vacuumIndex p
  have hB := block_deriv_zero_tick vacuumIndex VacuumSchur.complementIndex p
  have hC := block_deriv_zero_tick VacuumSchur.complementIndex vacuumIndex p
  change HasDerivAt (fun s : ℝ => A (0,fun j => s*p j))
    (compress ((-Complex.I) • kinetic8 p)) 0 at hA
  change HasDerivAt (fun s : ℝ => B (0,fun j => s*p j)) _ 0 at hB
  change HasDerivAt (fun s : ℝ => C (0,fun j => s*p j)) _ 0 at hC
  have hpath : HasDerivAt (fun s : ℝ => ((0 : ℝ), fun j : Fin 3 => s*p j)) (0,p) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const p)
    simpa only [id_eq, one_smul, Pi.smul_def, smul_eq_mul] using! h
  have hi := analytic_D_inverse.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hpath (by ext <;> simp)
  change HasDerivAt (fun s : ℝ => (D (0,fun j => s*p j))⁻¹) _ 0 at hi
  have h := hA.sub ((hB.mul hi).mul hC)
  simpa only [S, Pi.sub_def, Pi.mul_def, zero_mul, ← Pi.zero_def,
    B_axis_zero, C_axis_zero, mul_zero, zero_mul, add_zero, sub_zero,
    compress_smul, compress_kinetic] using! h

end PMAction.NormalizedSchur
