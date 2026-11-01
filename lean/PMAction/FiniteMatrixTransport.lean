import PMAction.TransportExistence
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! Transport on actual finite label types and time-dependent rectangular
intertwining. Reindexing is a coordinate equivalence, not an added physical gate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.FiniteMatrixTransport
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-- The transport existence theorem on any finite carrier label type. -/
theorem exists_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ → Matrix ι ι ℂ) (hB : Continuous B) (hskew : ∀ t, star (B t) = -B t) :
    ∃ T : ℝ → Matrix ι ι ℂ, T 0=1 ∧
      (∀ t, HasDerivAt T (T t*B t) t) ∧ ∀ t, T t ∈ unitary _ := by
  let f := Matrix.reindexAlgEquiv ℝ ℂ (Fintype.equivFin ι)
  let e := f.toLinearEquiv.toContinuousLinearEquiv
  have hs (Z : Matrix ι ι ℂ) : f (star Z)=star (f Z) := by ext i j; rfl
  have hfc : Continuous f := e.continuous
  obtain ⟨T,h0,hd,hu⟩ := TransportExistence.exists_transport (fun t => f (B t)) (hfc.comp hB)
    (fun t => by rw [← hs,hskew,map_neg])
  refine ⟨fun t => f.symm (T t),?_,fun t => ?_,fun t => ?_⟩
  · change f.symm (T 0)=1
    rw [h0,map_one]
  · have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t)
    convert h using 1
    · rfl
    · change f.symm (T t)*B t=f.symm (T t*f (B t))
      rw [map_mul,AlgEquiv.symm_apply_apply]
  · constructor
    · apply f.injective
      change f (star (f.symm (T t))*f.symm (T t))=f 1
      rw [map_mul,hs,AlgEquiv.apply_symm_apply,map_one]
      exact (hu t).1
    · apply f.injective
      change f (f.symm (T t)*star (f.symm (T t)))=f 1
      rw [map_mul,hs,AlgEquiv.apply_symm_apply,map_one]
      exact (hu t).2

/-- Product rule for rectangular matrices in the operator norm. -/
lemma rectangular_deriv {a b d : Type*} [Fintype a] [Fintype b] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq d]
    {F : ℝ → Matrix a b ℂ} {G : ℝ → Matrix b d ℂ}
    {F' : Matrix a b ℂ} {G' : Matrix b d ℂ} {s : ℝ}
    (hF : HasDerivAt F F' s) (hG : HasDerivAt G G' s) :
    HasDerivAt (fun t => F t*G t) (F'*G s+F s*G') s := by
  have hm : IsBoundedBilinearMap ℝ (fun p : Matrix a b ℂ × Matrix b d ℂ => p.1*p.2) :=
    { add_left := fun _ _ _ => Matrix.add_mul _ _ _
      smul_left := fun _ _ _ => Matrix.smul_mul _ _ _
      add_right := fun _ _ _ => Matrix.mul_add _ _ _
      smul_right := fun _ _ _ => Matrix.mul_smul _ _ _
      bound := ⟨1,by norm_num,fun A B => by
        simpa only [one_mul] using (show ‖A*B‖ ≤ ‖A‖*‖B‖ from Matrix.l2_opNNNorm_mul A B)⟩ }
  have hh := (hm.hasFDerivAt (F s,G s)).comp_hasDerivAt s (hF.prodMk hG)
  simpa only [Function.comp_def,IsBoundedBilinearMap.deriv_apply,add_comm] using hh

/-- Time-dependent transport preserves a constant representation intertwiner.
This covers the full native carrier dynamics, including unobserved modes. -/
theorem intertwining {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (E : Matrix a b ℂ) {A : ℝ → Matrix a a ℂ} {B : ℝ → Matrix b b ℂ}
    (hAB : ∀ t, A t*E=E*B t) (hB : ∀ t, star (B t) = -B t)
    (T : ℝ → Matrix a a ℂ) (U : ℝ → Matrix b b ℂ)
    (hT0 : T 0=1) (hU0 : U 0=1)
    (hTd : ∀ t, HasDerivAt T (T t*A t) t) (hUd : ∀ t, HasDerivAt U (U t*B t) t)
    (hUu : ∀ t, U t ∈ unitary _) (t : ℝ) : T t*E=E*U t := by
  have hd (s : ℝ) : HasDerivAt (fun s => T s*E*star (U s)) 0 s := by
    have h := rectangular_deriv (rectangular_deriv (hTd s) (hasDerivAt_const s E)) (hUd s).star
    simp only [Matrix.mul_zero,add_zero] at h
    convert h using 1
    rw [star_mul,hB] 
    rw [Matrix.mul_assoc (T s) (A s) E,hAB]
    simp only [Matrix.mul_assoc,Matrix.mul_neg,Matrix.neg_mul,add_neg_cancel]

  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simp only [hT0,hU0,star_one,Matrix.one_mul,Matrix.mul_one] at hc
  have hu := (Unitary.mem_iff.mp (hUu t)).1
  calc T t*E=(T t*E)*(star (U t)*U t) := by rw [hu,Matrix.mul_one]
       _ = E*U t := by rw [← Matrix.mul_assoc,hc]

/-- Unitary intertwining also gives exact readout for every native state. -/
theorem readout {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (E : Matrix a b ℂ) (T : Matrix a a ℂ) (U : Matrix b b ℂ)
    (h : T*E=E*U) (hT : T ∈ unitary _) (hU : U ∈ unitary _) : Eᴴ*T=U*Eᴴ := by
  have hh := congrArg Matrix.conjTranspose h
  have ht : Tᴴ*T=1 := (Unitary.mem_iff.mp hT).1
  have hu : U*Uᴴ=1 := (Unitary.mem_iff.mp hU).2
  calc Eᴴ*T = (U*Uᴴ)*Eᴴ*T := by rw [hu,Matrix.one_mul]
       _ = U*(Eᴴ*Tᴴ)*T := by rw [conjTranspose_mul,conjTranspose_mul] at hh; rw [hh]; simp only [Matrix.mul_assoc]
       _ = U*Eᴴ := by simp only [Matrix.mul_assoc,ht,Matrix.mul_one]

end PMAction.FiniteMatrixTransport
