import PMAction.RootReferencePreparation

/-!
# Uniform sampling does not supply a prepared reference

Two distinct interpretations are tested separately. A uniform incoherent
carrier mixture is fixed by every closed unitary carrier update. A coherent
constant-amplitude carrier state is fixed by every reconstructed involution
phase and their finite words. Neither supplies the known basis reference
under those respective contracts. This does not identify either interpretation
with the physical vacuum, exclude open preparation, or conflate sampling and coherence.
-/
noncomputable section
namespace PMAction.ReferenceSourceBoundary
open Matrix CommonResponse RootReferencePreparation
abbrev C := ActualRootRepair.C

def uniformMixture : Matrix C C ℂ := (1/8 : ℂ) • 1

def referenceProjector : Matrix C C ℂ :=
  vecMulVec (Pi.single recordLabel 1) (star (Pi.single recordLabel 1))

theorem mixture_trace : uniformMixture.trace = 1 := by
  simp [uniformMixture, trace_smul, trace_one, CarrierEvents.carrier_card]

/-- Arbitrary closed coherent controls do not purify a maximally mixed carrier source. -/
theorem mixture_invariant (U : Matrix C C ℂ) (hu : U ∈ unitary (Matrix C C ℂ)) :
    U * uniformMixture * Uᴴ = uniformMixture := by
  have hr : U*Uᴴ=1 := hu.2
  rw [uniformMixture, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hr]

/-- In the stated incoherent-source model, closed unitary control cannot increase
this diagonal reference weight. Measurement/conditioning is not included. -/
theorem reference_weight (U : Matrix C C ℂ) (hu : U ∈ unitary (Matrix C C ℂ)) :
    (U * uniformMixture * Uᴴ) recordLabel recordLabel = 1/8 := by
  rw [mixture_invariant U hu]
  simp [uniformMixture]

theorem mixture_ne_reference : uniformMixture ≠ referenceProjector := by
  intro h
  have hh := congrFun (congrFun h seedLabel) seedLabel
  norm_num [uniformMixture, referenceProjector, vecMulVec, distinct] at hh

theorem no_closed_mixed_source (U : Matrix C C ℂ) (hu : U ∈ unitary (Matrix C C ℂ)) :
    U * uniformMixture * Uᴴ ≠ referenceProjector := by
  rw [mixture_invariant U hu]
  exact mixture_ne_reference

open scoped Matrix.Norms.Operator in
/-- Every root-derived phase fixes the coherent uniform vector exactly.
Its phase is not a newly selectable relative phase between carrier labels. -/
theorem phase_fixes_uniform (e : Equiv.Perm C) (he : Function.Involutive e) (p t : ℝ) :
    RootTransferPhase.phase e p t *ᵥ (fun _ : C => (1 : ℂ)) = fun _ => 1 := by
  have hp : e.permMatrix ℂ *ᵥ (fun _ : C => (1 : ℂ)) = fun _ => 1 := by
    rw [Matrix.permMatrix_mulVec]
    rfl
  have hplus : InvolutionSpectral.plus (e.permMatrix ℂ) *ᵥ (fun _ : C => (1 : ℂ)) =
      fun _ => 1 := by
    rw [InvolutionSpectral.plus, smul_mulVec, add_mulVec, one_mulVec, hp]
    ext i
    norm_num
  have hminus : InvolutionSpectral.minus (e.permMatrix ℂ) *ᵥ (fun _ : C => (1 : ℂ)) = 0 := by
    rw [InvolutionSpectral.minus, smul_mulVec, sub_mulVec, one_mulVec, hp, sub_self, smul_zero]
  rw [RootTransferPhase.phase_formula e he, add_mulVec, smul_mulVec, hplus, hminus]
  simp

/-- The finite-word result also allows any other gates fixing this same vector. -/
theorem word_fixes_uniform (gates : List (Matrix C C ℂ))
    (hg : ∀ A ∈ gates, A *ᵥ (fun _ : C => (1 : ℂ)) = fun _ => 1) :
    gates.prod *ᵥ (fun _ : C => (1 : ℂ)) = fun _ => 1 := by
  induction gates with
  | nil => simp
  | cons A gates ih =>
    rw [List.prod_cons, ← mulVec_mulVec, ih (fun B hb => hg B (by simp [hb]))]
    exact hg A (by simp)

/-- Constant amplitudes cannot become a single prepared carrier through such
closed words, whatever nonzero common normalization is used. -/
theorem no_uniform_coherent_preparation (gates : List (Matrix C C ℂ))
    (hg : ∀ A ∈ gates, A *ᵥ (fun _ : C => (1 : ℂ)) = fun _ => 1)
    (s : ℂ) (hs : s ≠ 0) :
    gates.prod *ᵥ (fun _ : C => s) ≠ ActualRootRepair.pack 0 reference := by
  have he : (fun _ : C => s) = s • (fun _ : C => (1 : ℂ)) := by ext i; simp
  rw [he, Matrix.mulVec_smul, word_fixes_uniform gates hg, reference_basis]
  intro h
  have hh := congrFun h seedLabel
  simp [distinct] at hh
  exact hs hh

end PMAction.ReferenceSourceBoundary
