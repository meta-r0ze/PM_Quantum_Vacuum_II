import PMAction.SignedSpectrum

/-! Occurrence counts for both signs, with the light zero handled separately. -/
noncomputable section
namespace PMAction.SignedSpectrum
open Matrix Polynomial ConcreteFermion

lemma light_energy_square (k : Fin 3 → ℝ) (δ : ℝ) :
    (lightEnergy k δ)^2=DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ)^2 :=
  Real.sq_sqrt (add_nonneg (kinetic_nonneg k) (sq_nonneg _))

lemma heavy_energy_square (k : Fin 3 → ℝ) (δ : ℝ) :
    (heavyEnergy k δ)^2=DomainWallSpectrum.kineticNorm k+(DetuningMass.lightMass δ+1)^2 :=
  Real.sq_sqrt (add_nonneg (kinetic_nonneg k) (sq_nonneg _))

theorem heavy_pair_multiplicity (k : Fin 3 → ℝ) (δ : ℝ) :
    (hamiltonian k δ).charpoly.rootMultiplicity (heavyEnergy k δ : ℂ)=2 ∧
    (hamiltonian k δ).charpoly.rootMultiplicity (-(heavyEnergy k δ : ℂ))=2 := by
  have hp : 0 < heavyEnergy k δ := lt_of_le_of_lt (energy_order k δ).1 (energy_order k δ).2
  constructor
  · exact signed_multiplicity k δ _ (ne_of_gt hp) (Or.inr (heavy_energy_square k δ))
  · have h := signed_multiplicity k δ (-heavyEnergy k δ) (neg_ne_zero.mpr (ne_of_gt hp))
      (Or.inr (by simpa only [neg_sq] using heavy_energy_square k δ))
    simpa only [Complex.ofReal_neg] using h

theorem light_pair_multiplicity (k : Fin 3 → ℝ) (δ : ℝ) (h : lightEnergy k δ ≠ 0) :
    (hamiltonian k δ).charpoly.rootMultiplicity (lightEnergy k δ : ℂ)=2 ∧
    (hamiltonian k δ).charpoly.rootMultiplicity (-(lightEnergy k δ : ℂ))=2 := by
  constructor
  · exact signed_multiplicity k δ _ h (Or.inl (light_energy_square k δ))
  · have hh := signed_multiplicity k δ (-lightEnergy k δ) (neg_ne_zero.mpr h)
      (Or.inl (by simpa only [neg_sq] using light_energy_square k δ))
    simpa only [Complex.ofReal_neg] using hh

theorem light_zero_iff (k : Fin 3 → ℝ) (δ : ℝ) :
    lightEnergy k δ=0 ↔ DomainWallSpectrum.kineticNorm k=0 ∧ δ=0 := by
  constructor
  · intro h
    have hs := light_energy_square k δ
    rw [h] at hs
    have hm := (DetuningMass.mass_le δ).1
    have hk := kinetic_nonneg k
    have hz : DetuningMass.lightMass δ=0 := by nlinarith [sq_nonneg (DetuningMass.lightMass δ)]
    have hd := DetuningMass.mass_relation δ
    rw [hz] at hd
    constructor <;> nlinarith
  · rintro ⟨hs,rfl⟩
    simp [lightEnergy, hs, DetuningMass.light_mass_zero]

theorem origin_zero_multiplicity : (hamiltonian 0 0).charpoly.rootMultiplicity 0=4 := by
  rw [origin_charpoly]
  have hf : (X^4*(X-1)^2*(X+1)^2 : ℂ[X]) = ((X-1)^2*(X+1)^2)*(X-C 0)^4 := by
    simp; ring
  rw [hf, rootMultiplicity_mul_X_sub_C_pow (by
    exact mul_ne_zero (pow_ne_zero 2 (by simpa using (monic_X_sub_C (1 : ℂ)).ne_zero))
      (pow_ne_zero 2 (by simpa using (monic_X_add_C (1 : ℂ)).ne_zero)))]
  have hz : (((X-1)^2*(X+1)^2 : ℂ[X])).rootMultiplicity 0=0 :=
    rootMultiplicity_eq_zero (by norm_num [IsRoot])
  rw [hz]

end PMAction.SignedSpectrum
