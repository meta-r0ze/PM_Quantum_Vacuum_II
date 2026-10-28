import PMAction.WilsonSplit

noncomputable section
namespace PMAction.WilsonSplit
open Matrix ConcreteFermion

set_option maxHeartbeats 2000000 in
/-- The directional matrix is exactly the two-neighbor Fourier symbol. -/
theorem directionSymbol_phase (j : Fin 3) (q : ℝ) :
    directionSymbol j q =
      ((Real.cos q : ℂ)+Complex.I*(Real.sin q : ℂ)) • SplitUpdate.coefficient j +
      ((Real.cos q : ℂ)-Complex.I*(Real.sin q : ℂ)) • (SplitUpdate.coefficient j)ᴴ := by
  ext x y
  cases x with
  | inl a => cases y with
    | inl b => fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [directionSymbol, SplitUpdate.coefficient, LocalUnitary.coefficient,
          beta, alpha, conjTranspose_apply, map_ofNat] <;> ring_nf <;> norm_num [Complex.I_sq, map_ofNat]
    | inr b => simp [directionSymbol, SplitUpdate.coefficient, conjTranspose_apply]
  | inr a => cases y with
    | inl b => simp [directionSymbol, SplitUpdate.coefficient, conjTranspose_apply]
    | inr b => fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [directionSymbol, SplitUpdate.coefficient, LocalUnitary.coefficient,
          beta, alpha, conjTranspose_apply, map_ofNat] <;> ring_nf <;> norm_num [Complex.I_sq, map_ofNat]

end PMAction.WilsonSplit
