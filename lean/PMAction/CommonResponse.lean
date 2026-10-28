import PMAction.CarrierResponse

/-!
# One readout, one toll: the common gauge, scalar and fermion response

`CarrierResponse` derived the gauge response from the actual carrier events: a coherent
comparison of a transported branch with its reference raises a flag with probability
`(1 − Re U_aa)/2`, each flag costs the primitive toll, and refreshed phase tests give the
cosine action and its continuum limit. That readout was stated for basis carriers. Here it is
stated for an arbitrary normalized amplitude, which is what scalar and fermion fields carry.

* `stateFlag U φ = ‖φ − Uφ‖²/4`: the flag probability for amplitude `φ` transported by `U`.
* `state_flag_formula`: for unitary `U` and `‖φ‖ = 1`, `stateFlag U φ = (1 − Re⟨φ, Uφ⟩)/2`. With
  `φ` a basis carrier this is `InterferenceReadout.flag_formula`.
* Gauge: `gauge_case` recovers `(1 − cos θ)/2` for a phase holonomy on one carrier.
* Fermion: `wilson_form`, `stateFlag U ψ = Re⟨ψ, (2 − U − U†)ψ⟩/4`, the Wilson hopping form.
* Scalar: `linkFlag U φ φ' = ‖φ' − Uφ‖²/4`, the gauge-covariant difference between neighbours;
  `link_on_diagonal` shows it reduces to `stateFlag` when the neighbour holds the same amplitude.
* `common_normalization`: in all three sectors one repair event per flag at the common toll
  gives cost `toll·m·‖(compared) − U(transported)‖²/4`. The prefactor `toll·m/4` is shared, so
  the relative normalization of the gauge, scalar and fermion quadratic responses is fixed by the
  single event law rather than chosen sector by sector.

Remaining inputs, unchanged from `CarrierResponse`: the repair length `m`, the preparation of the
reference branch, and the squared-amplitude readout itself (not a Born-rule derivation).
-/

noncomputable section
namespace PMAction.CommonResponse
open Matrix Finset InterferenceReadout
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared norm as a real number. -/
def nsq (x : ι → ℂ) : ℝ := (star x ⬝ᵥ x).re

def stateFlag (U : Matrix ι ι ℂ) (φ : ι → ℂ) : ℝ := nsq (φ - U *ᵥ φ) / 4

def linkFlag (U : Matrix ι ι ℂ) (φ φ' : ι → ℂ) : ℝ := nsq (φ' - U *ᵥ φ) / 4

lemma unitary_nsq (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (φ : ι → ℂ) :
    star (U *ᵥ φ) ⬝ᵥ (U *ᵥ φ) = star φ ⬝ᵥ φ := by
  have h1 : Uᴴ * U = 1 := hu.1
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1, one_mulVec]

omit [DecidableEq ι] in
lemma cross_re (U : Matrix ι ι ℂ) (φ : ι → ℂ) :
    (star (U *ᵥ φ) ⬝ᵥ φ).re = (star φ ⬝ᵥ (U *ᵥ φ)).re := by
  have : star (U *ᵥ φ) ⬝ᵥ φ = star (star φ ⬝ᵥ (U *ᵥ φ)) := by
    simp [dotProduct, star_sum, mul_comm]
  rw [this, Complex.star_def, Complex.conj_re]

theorem state_flag_formula (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (φ : ι → ℂ)
    (hφ : nsq φ = 1) :
    stateFlag U φ = (1 - (star φ ⬝ᵥ (U *ᵥ φ)).re) / 2 := by
  unfold stateFlag nsq at *
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, unitary_nsq U hu]
  simp only [Complex.sub_re]
  rw [cross_re, hφ]
  ring

theorem wilson_form (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (ψ : ι → ℂ) :
    stateFlag U ψ = (star ψ ⬝ᵥ ((2 - U - Uᴴ) *ᵥ ψ)).re / 4 := by
  unfold stateFlag nsq
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, unitary_nsq U hu]
  rw [sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub]
  have h2 : (2 : Matrix ι ι ℂ) *ᵥ ψ = (2 : ℂ) • ψ := by
    rw [show (2 : Matrix ι ι ℂ) = (2 : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [smul_one_eq_diagonal]; rfl, smul_mulVec, one_mulVec]
  have hH : (star ψ ⬝ᵥ (Uᴴ *ᵥ ψ)).re = (star ψ ⬝ᵥ (U *ᵥ ψ)).re := by
    rw [dotProduct_mulVec, ← star_mulVec, ← cross_re U ψ]
  rw [h2, dotProduct_smul]
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re]
  rw [cross_re, hH]
  norm_num
  ring

omit [DecidableEq ι] in
theorem link_on_diagonal (U : Matrix ι ι ℂ) (φ : ι → ℂ) : linkFlag U φ φ = stateFlag U φ := rfl

/-- The gauge case: a phase holonomy on one carrier. -/
theorem gauge_case (θ : ℝ) : stateFlag (phase θ) (fun _ => 1) = (1 - Real.cos θ) / 2 := by
  have hu : phase θ ∈ unitary (Matrix Unit Unit ℂ) := phase_unitary θ
  rw [state_flag_formula _ hu _ (by simp [nsq, dotProduct])]
  simp [phase, dotProduct, mulVec, Complex.exp_ofReal_mul_I_re]

/-- One repair event per flag at the common toll, `m` events per repair. -/
def responseCost (toll : ℝ) (m : ℕ) (q : ℝ) : ℝ := toll * m * q

theorem common_normalization (toll : ℝ) (m : ℕ) (θ : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (φ φ' : κ → ℂ) :
    responseCost toll m (stateFlag (phase θ) (fun _ => 1)) =
        toll * m / 4 * nsq ((fun _ => (1 : ℂ)) - phase θ *ᵥ (fun _ => 1)) ∧
      responseCost toll m (linkFlag U φ φ') = toll * m / 4 * nsq (φ' - U *ᵥ φ) ∧
      responseCost toll m (stateFlag U φ) = toll * m / 4 * nsq (φ - U *ᵥ φ) ∧
      responseCost toll m (stateFlag (phase θ) (fun _ => 1)) = CarrierResponse.repairCost toll m (phase θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [responseCost, stateFlag]; ring
  · simp only [responseCost, linkFlag]; ring
  · simp only [responseCost, stateFlag]; ring
  · rw [CarrierResponse.phase_repair_cost, responseCost, gauge_case]; ring

/-- On a basis carrier the state readout is the carrier readout of `InterferenceReadout`. -/
theorem basis_case (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (a : ι) :
    stateFlag U (Pi.single a 1) = flagProbability U a := by
  rw [state_flag_formula U hu _ (by simp [nsq, dotProduct, Pi.single_apply]), flag_formula U hu a]
  simp [dotProduct, mulVec, Pi.single_apply]

/-- The whole chain on Paper I's actual carriers: averaging the common response of the E8 root
reflection (`SubstrateReflection`, `CarrierEvents.reflect`) over the eight minimal vectors of any
glue class gives exactly `toll·m/4`, the cost `CarrierResponse.reflection_repair_cost`. -/
theorem carrier_chain (c : Fin 3) (toll : ℝ) (m : ℕ) :
    (∑ v : CarrierEvents.Carrier c,
        responseCost toll m (stateFlag ((CarrierEvents.reflect c).permMatrix ℂ) (Pi.single v 1))) /
      Fintype.card (CarrierEvents.Carrier c) = toll * m / 4 := by
  have hu := CarrierResponse.perm_unitary (CarrierEvents.reflect c)
  simp_rw [responseCost, basis_case _ hu]
  rw [← Finset.mul_sum, mul_div_assoc]
  have h := CarrierResponse.reflection_flag c
  unfold meanFlag at h
  rw [h]; ring

end PMAction.CommonResponse
