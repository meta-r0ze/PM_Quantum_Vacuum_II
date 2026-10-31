import PMAction.ProjectedEvolution
import PMAction.VacuumTangent

/-!
# Joint spatial/time refinement on the actual vacuum sector

The starting sector is the already identified zero-wall kernel, not a changing
or fitted eigenbasis. Momentum and elapsed time are fixed. The refinement rule
is a sufficient modelling input; this is not an interacting, quantum or full
real-space field limit, nor a derivation of a physical microscopic clock.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.JointSpaceTime
open Matrix ConcreteFermion Filter Topology
open scoped Matrix.Norms.L2Operator
local notation "M" => Matrix Sites Sites ℂ

def continuum (p : Fin 3 → ℝ) : M :=
  p 0 • VacuumTangent.alpha8 0 + p 1 • VacuumTangent.alpha8 1 + p 2 • VacuumTangent.alpha8 2

/-- On the existing four vacuum coordinates the limit is exactly the massless
Clifford Hamiltonian, rather than a new dispersion ansatz. -/
theorem continuum_compression (p : Fin 3 → ℝ) :
    VacuumTangent.compress (continuum p)=Dirac.H alpha beta p 0 := by
  have hr (r : ℝ) (A : M) : VacuumTangent.compress (r • A)=r • VacuumTangent.compress A := rfl
  simp [continuum,VacuumTangent.compress_add,hr,VacuumTangent.compress_alpha8,Dirac.H]

def curve (p : Fin 3 → ℝ) (a : ℝ) : M :=
  hamiltonian (fun j => a*p j) (DomainWallSpectrum.wilson (fun j => a*p j))

def scaled (p : Fin 3 → ℝ) (a : ℝ) : M := a⁻¹ • curve p a

/-- Exact decomposition before any spatial approximation. -/
lemma decomposition (k : Fin 3 → ℝ) (δ : ℝ) :
    hamiltonian k δ=VacuumSplit.wall+
      (Real.sin (k 0)) • VacuumTangent.alpha8 0+
      (Real.sin (k 1)) • VacuumTangent.alpha8 1+
      (Real.sin (k 2)) • VacuumTangent.alpha8 2+δ • VacuumSplit.beta8 := by
  ext x y
  cases x <;> cases y <;>
    simp [hamiltonian,DomainWallSpectrum.H,DomainWallSpectrum.momentum,
      VacuumSplit.wall,VacuumTangent.alpha8,VacuumSplit.beta8,Fin.sum_univ_three]

lemma curve_zero (p : Fin 3 → ℝ) : curve p 0=VacuumSplit.wall := by
  simp [curve,DomainWallSpectrum.wilson,VacuumSplit.wall]
  rfl

/-- The actual Wilson Hamiltonian has the massless kinetic tangent. -/
theorem curve_deriv (p : Fin 3 → ℝ) : HasDerivAt (curve p) (continuum p) 0 := by
  have hs (j : Fin 3) : HasDerivAt (fun a : ℝ => Real.sin (a*p j)) (p j) 0 := by
    have h := (Real.hasDerivAt_sin (0*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j))
    apply hasDerivAt_iff_tendsto_slope.mpr
    simpa [slope_fun_def,Function.comp_def,Pi.sub_apply] using h.tendsto_slope
  have hc (j : Fin 3) : HasDerivAt (fun a : ℝ => 1-Real.cos (a*p j)) 0 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub
      ((Real.hasDerivAt_cos (0*p j)).comp 0 ((hasDerivAt_id 0).mul_const (p j)))
    apply hasDerivAt_iff_tendsto_slope.mpr
    simpa [slope_fun_def,Function.comp_def,Pi.sub_apply] using h.tendsto_slope
  have hw : HasDerivAt (fun a => DomainWallSpectrum.wilson (fun j => a*p j)) 0 0 := by
    have h := ((hc 0).add (hc 1)).add (hc 2)
    apply hasDerivAt_iff_tendsto_slope.mpr
    simpa only [slope_fun_def,DomainWallSpectrum.wilson,Fin.sum_univ_three,Pi.add_apply,zero_add] using
      h.tendsto_slope
  have hd := ((((hasDerivAt_const 0 VacuumSplit.wall).add
    ((hs 0).smul_const (VacuumTangent.alpha8 0))).add
    ((hs 1).smul_const (VacuumTangent.alpha8 1))).add
    ((hs 2).smul_const (VacuumTangent.alpha8 2))).add (hw.smul_const VacuumSplit.beta8)
  have hf : curve p = fun a => VacuumSplit.wall+
      (Real.sin (a*p 0)) • VacuumTangent.alpha8 0+
      (Real.sin (a*p 1)) • VacuumTangent.alpha8 1+
      (Real.sin (a*p 2)) • VacuumTangent.alpha8 2+
      DomainWallSpectrum.wilson (fun j => a*p j) • VacuumSplit.beta8 := by
    funext a
    exact decomposition _ _
  rw [hf]
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [slope_fun_def,continuum,zero_smul,zero_add,add_zero,Pi.add_apply] using hd.tendsto_slope

lemma continuum_hermitian (p : Fin 3 → ℝ) : (continuum p).IsHermitian := by
  have hh (j : Fin 3) : (VacuumTangent.alpha8 j).IsHermitian := by
    simp [IsHermitian,VacuumTangent.alpha8,fromBlocks_conjTranspose,(alpha_hermitian j).eq]
  exact (((hh 0).smul (IsSelfAdjoint.all (p 0))).add
    ((hh 1).smul (IsSelfAdjoint.all (p 1)))).add ((hh 2).smul (IsSelfAdjoint.all (p 2)))

lemma scaled_hermitian (p : Fin 3 → ℝ) (a : ℝ) : (scaled p a).IsHermitian :=
  (hamiltonian_hermitian _ _).smul (IsSelfAdjoint.all a⁻¹)

/-- The kinetic limit preserves the canonical wall-kernel sector. -/
lemma continuum_commutes (p : Fin 3 → ℝ) :
    continuum p*VacuumSplit.vacuumProjector=VacuumSplit.vacuumProjector*continuum p := by
  have hc (j : Fin 3) : VacuumTangent.alpha8 j*VacuumSplit.vacuumProjector=
      VacuumSplit.vacuumProjector*VacuumTangent.alpha8 j := by
    have hp := alpha_gamma j
    simp only [VacuumTangent.alpha8,VacuumSplit.vacuumProjector,fromBlocks_multiply,
      mul_zero,zero_mul,zero_add,add_zero,DomainWallSpectrum.plus,DomainWallSpectrum.minus,
      mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_sub,sub_mul,mul_one,one_mul,hp,
      sub_self,smul_zero]
  simp only [continuum,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hc]

/-- The heavy wall term disappears on the original vacuum image. Its projected
scaled-generator defect tends to zero; no uniform bound on the full scaled
Hamiltonian is assumed. -/
theorem projected_generator_limit (p : Fin 3 → ℝ) :
    Tendsto (fun a => scaled p a*VacuumSplit.vacuumProjector-
      VacuumSplit.vacuumProjector*continuum p) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hd := ((curve_deriv p).mul_const VacuumSplit.vacuumProjector).tendsto_slope_zero
  simp only [zero_add,curve_zero,VacuumSplit.wall_projector,sub_zero] at hd
  have hh := hd.sub_const (continuum p*VacuumSplit.vacuumProjector)
  simpa only [scaled,smul_mul_assoc,sub_self,continuum_commutes] using hh

lemma exact_scaled (p : Fin 3 → ℝ) (a T : ℝ) :
    VacuumIteration.exactStep (fun j => a*p j) (T/a)=ProjectedEvolution.evolution (scaled p a) T := by
  unfold VacuumIteration.exactStep VacuumIteration.generator ProjectedEvolution.evolution scaled curve
  congr 1
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  push_cast
  congr 1
  ring

/-- An explicit error bound for simultaneous spatial and temporal refinement.
The first term is the uniform split error and the second the projected generator
defect. The lattice elapsed time is T/a, rather than T. -/
theorem error (p : Fin 3 → ℝ) (a T : ℝ) (n : ℕ) :
    ‖VacuumSplit.momentumUpdate (fun j => a*p j)
        (IterationError.mesh (T/a) n)^(n+1)*VacuumSplit.vacuumProjector-
      VacuumSplit.vacuumProjector*ProjectedEvolution.evolution (continuum p) T‖ ≤
      (2*VacuumErrorRate.speedBound^2)*(T/a)^2/((n+1 : ℕ) : ℝ)*‖VacuumSplit.vacuumProjector‖+
      |T| *‖scaled p a*VacuumSplit.vacuumProjector-VacuumSplit.vacuumProjector*continuum p‖ := by
  have ht := VacuumErrorRate.fixed_time_error (fun j => a*p j) (T/a) n
  have hs := ProjectedEvolution.error (scaled p a) (continuum p) VacuumSplit.vacuumProjector
    (scaled_hermitian p a) (continuum_hermitian p) T
  rw [← exact_scaled] at hs
  have hm := (norm_mul_le
    (VacuumSplit.momentumUpdate (fun j => a*p j) (IterationError.mesh (T/a) n)^(n+1)-
      VacuumIteration.exactStep (fun j => a*p j) (T/a)) VacuumSplit.vacuumProjector).trans
    (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  rw [Matrix.sub_mul] at hm
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hm hs)

/-- Fixed continuum momentum and time: the actual corrected split converges on
the canonical vacuum sector whenever a→0 and a²N→∞ (in inverse form). Both
refinements are explicit inputs; no eigenbasis or phase convention is fitted. -/
theorem joint_limit (p : Fin 3 → ℝ) (T : ℝ) (a : ℕ → ℝ) (n : ℕ → ℕ)
    (ha : ∀ r, 0<a r) (ha0 : Tendsto a atTop (𝓝 0))
    (hscale : Tendsto (fun r => 1/((a r)^2*((n r+1 : ℕ) : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun r => VacuumSplit.momentumUpdate (fun j => a r*p j)
      (IterationError.mesh (T/a r) (n r))^(n r+1)*VacuumSplit.vacuumProjector)
      atTop (𝓝 (VacuumSplit.vacuumProjector*ProjectedEvolution.evolution (continuum p) T)) := by
  have hap : Tendsto a atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨ha0,Eventually.of_forall fun r => (ha r).ne'⟩
  have hd := ((projected_generator_limit p).comp hap).norm
  have hfirst := hscale.const_mul
    ((2*VacuumErrorRate.speedBound^2)*T^2*‖VacuumSplit.vacuumProjector‖)
  have hsecond := hd.const_mul |T|
  simp only [norm_zero,mul_zero] at hfirst hsecond
  have hb := hfirst.add hsecond
  simp only [zero_add] at hb
  have heq (r : ℕ) :
      (2*VacuumErrorRate.speedBound^2)*(T/a r)^2/((n r+1 : ℕ) : ℝ)*‖VacuumSplit.vacuumProjector‖ =
      ((2*VacuumErrorRate.speedBound^2)*T^2*‖VacuumSplit.vacuumProjector‖)*
        (1/((a r)^2*((n r+1 : ℕ) : ℝ))) := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r => ?_) hb
  simpa only [heq,Function.comp_def] using error p (a r) T (n r)

lemma continuum_evolution_commutes (p : Fin 3 → ℝ) (T : ℝ) :
    VacuumSplit.vacuumProjector*ProjectedEvolution.evolution (continuum p) T=
      ProjectedEvolution.evolution (continuum p) T*VacuumSplit.vacuumProjector := by
  have hc : Commute VacuumSplit.vacuumProjector (continuum p) := (continuum_commutes p).symm
  exact ((hc.smul_right (-Complex.I)).smul_right T).exp_right.eq

/-- Every fixed initial state in the original zero-wall kernel has the joint
massless evolution limit. This is state evolution, not just an eigenvalue limit. -/
theorem kernel_state_limit (p : Fin 3 → ℝ) (T : ℝ) (a : ℕ → ℝ) (n : ℕ → ℕ)
    (ha : ∀ r, 0<a r) (ha0 : Tendsto a atTop (𝓝 0))
    (hscale : Tendsto (fun r => 1/((a r)^2*((n r+1 : ℕ) : ℝ))) atTop (𝓝 0))
    (ψ : Sites → ℂ) (hψ : VacuumSplit.wall*ᵥψ=0) :
    Tendsto (fun r => VacuumSplit.momentumUpdate (fun j => a r*p j)
      (IterationError.mesh (T/a r) (n r))^(n r+1) *ᵥ ψ) atTop
      (𝓝 (ProjectedEvolution.evolution (continuum p) T *ᵥ ψ)) := by
  have hc : Continuous (fun A : M => A *ᵥ ψ) :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have hh := hc.continuousAt.tendsto.comp (joint_limit p T a n ha ha0 hscale)
  have hp := VacuumSplit.projector_fixes_kernel ψ hψ
  simpa only [Function.comp_def,continuum_evolution_commutes,← mulVec_mulVec,hp] using hh

/-- One concrete simultaneous refinement: a=1/(r+1), N=(r+1)³. The polynomial
index is N−1 without natural subtraction, so every step count is positive. -/
def refinements (r : ℕ) : ℕ := r^3+3*r^2+3*r

theorem refinement_count (r : ℕ) : refinements r+1=(r+1)^3 := by
  unfold refinements
  ring

theorem explicit_limit (p : Fin 3 → ℝ) (T : ℝ) :
    Tendsto (fun r : ℕ => VacuumSplit.momentumUpdate (fun j => (1/((r+1 : ℕ) : ℝ))*p j)
      (IterationError.mesh (T/(1/((r+1 : ℕ) : ℝ))) (refinements r))^(refinements r+1)*
      VacuumSplit.vacuumProjector) atTop
      (𝓝 (VacuumSplit.vacuumProjector*ProjectedEvolution.evolution (continuum p) T)) := by
  have ha0 : Tendsto (fun r : ℕ => 1/((r+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact (IterationError.mesh_tends_zero 1).congr' (Eventually.of_forall fun _ => rfl)
  apply joint_limit p T _ refinements (fun _ => by positivity) ha0
  convert ha0 using 1
  funext r
  rw [refinement_count]
  push_cast
  field_simp

end PMAction.JointSpaceTime
