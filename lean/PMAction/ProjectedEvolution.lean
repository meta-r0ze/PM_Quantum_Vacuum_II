import PMAction.VacuumErrorRate

/-! A unitary comparison estimate for approximate invariant sectors. Unlike a
generic exponential norm estimate, its constant does not grow with the norm of
the ambient Hamiltonian; this is essential when heavy energies diverge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ProjectedEvolution
open Matrix ConcreteFermion Set
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

def evolution (H : M) (t : ℝ) : M := NormedSpace.exp (t • ((-Complex.I) • H))

lemma unitary (H : M) (hH : H.IsHermitian) (t : ℝ) : evolution H t ∈ unitary M := by
  have he : t • ((-Complex.I) • H)=(-Complex.I*(t : ℂ)) • H := by
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,mul_comm]
  rw [evolution,he]
  exact VacuumSplit.exp_unitary H hH t

lemma deriv (H : M) (t : ℝ) :
    HasDerivAt (evolution H) (evolution H t*((-Complex.I) • H)) t :=
  VacuumErrorRate.exp_deriv _ t

lemma generator_commutes (H : M) (t : ℝ) :
    evolution H t*((-Complex.I) • H)=((-Complex.I) • H)*evolution H t :=
  ((Commute.refl ((-Complex.I) • H)).smul_left t).exp_left.eq

/-- Stable approximate intertwining. P need not be a projector or invertible.
Only the generator defect matters, even for unbounded families of heavy modes. -/
theorem error (A B P : M) (hA : A.IsHermitian) (hB : B.IsHermitian) (T : ℝ) :
    ‖evolution A T*P-P*evolution B T‖ ≤ |T| *‖A*P-P*B‖ := by
  let f (s : ℝ) := evolution A s*P*evolution B (T-s)
  let d (s : ℝ) := evolution A s*((-Complex.I) • (A*P-P*B))*evolution B (T-s)
  have hd (s : ℝ) : HasDerivAt f (d s) s := by
    have hi := (hasDerivAt_const s T).sub (hasDerivAt_id s)
    have hg := (deriv B (T-s)).scomp s hi
    have hh := ((deriv A s).mul_const P).mul hg
    convert hh using 1
    · funext t; rfl
    · dsimp [d,Function.comp_def]
      rw [generator_commutes B (T-s)]
      simp only [smul_sub,sub_mul,mul_sub,
        zero_sub,neg_smul,one_smul]
      noncomm_ring
  have hb (s : ℝ) : ‖d s‖ ≤ ‖A*P-P*B‖ := by
    dsimp [d]
    rw [CStarRing.norm_mul_mem_unitary _ (unitary B hB (T-s)),
      CStarRing.norm_mem_unitary_mul _ (unitary A hA s),norm_smul]
    simp
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ (univ : Set ℝ)) => (hd s).differentiableAt)
    (fun s (_ : s ∈ (univ : Set ℝ)) => by rw [(hd s).deriv]; exact hb s)
    convex_univ (mem_univ 0) (mem_univ T)
  simpa [f,evolution,Real.norm_eq_abs,mul_comm] using hh

end PMAction.ProjectedEvolution
