import PMAction.GaugeContinuum
import Mathlib.Algebra.Star.Unitary

/-! A phase-sensitive binary readout and its operational cost.
The squared-amplitude readout is explicit; it is not a derivation of the Born rule. -/
noncomputable section
namespace PMAction.InterferenceReadout
open Matrix Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Minus-port amplitude after comparing the transported and reference branches. -/
def flagAmplitude (U : Matrix ι ι ℂ) (a b : ι) : ℂ := (1/2 : ℂ)*((1 : Matrix ι ι ℂ) b a-U b a)
def flagProbability (U : Matrix ι ι ℂ) (a : ι) : ℝ := ∑ b, Complex.normSq (flagAmplitude U a b)

lemma column_population (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (a : ι) :
    (∑ b, Complex.normSq (U b a))=1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (M a a).re) hu.1
  simpa [mul_apply, conjTranspose_apply, Complex.mul_re, Complex.normSq_apply, pow_two] using h

lemma flag_norm (U : Matrix ι ι ℂ) (a b : ι) :
    Complex.normSq (flagAmplitude U a b) =
      (Complex.normSq (U b a)+(if b=a then 1-2*(U b a).re else 0))/4 := by
  by_cases h : b=a
  · subst b
    norm_num [flagAmplitude, Complex.normSq_mul, Complex.normSq_apply]
    ring
  · norm_num [flagAmplitude, h, Complex.normSq_mul]
    ring

/-- The outcome probability follows from the actual two-branch amplitudes. -/
theorem flag_formula (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (a : ι) :
    flagProbability U a = (1-(U a a).re)/2 := by
  simp only [flagProbability, flag_norm]
  rw [← sum_div, sum_add_distrib, column_population U hu a]
  simp
  ring

lemma flag_nonneg (U : Matrix ι ι ℂ) (a : ι) : 0 ≤ flagProbability U a :=
  sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

lemma neg_unitary (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) :
    -U ∈ unitary (Matrix ι ι ℂ) := by
  constructor
  · change (-U)ᴴ*(-U)=1
    simpa only [conjTranspose_neg, neg_mul_neg, star_eq_conjTranspose] using hu.1
  · change (-U)*(-U)ᴴ=1
    simpa only [conjTranspose_neg, neg_mul_neg, star_eq_conjTranspose] using hu.2

theorem binary_normalized (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (a : ι) :
    flagProbability U a+flagProbability (-U) a=1 := by
  rw [flag_formula U hu a, flag_formula (-U) (neg_unitary U hu) a]
  simp
  ring

theorem flag_bounds (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) (a : ι) :
    0 ≤ flagProbability U a ∧ flagProbability U a ≤ 1 := by
  have hn := flag_nonneg (-U) a
  have he := binary_normalized U hu a
  exact ⟨flag_nonneg U a, by linarith⟩

def meanFlag (U : Matrix ι ι ℂ) : ℝ := (∑ a, flagProbability U a)/Fintype.card ι

/-- Uniform carrier sampling produces a normalized trace score with a derived factor 1/2. -/
theorem mean_trace [Nonempty ι] (U : Matrix ι ι ℂ) (hu : U ∈ unitary (Matrix ι ι ℂ)) :
    meanFlag U = (1-U.trace.re/Fintype.card ι)/2 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have ht : U.trace.re=∑ a, (U a a).re := by
    exact map_sum Complex.reAddGroupHom _ _
  simp only [meanFlag, flag_formula U hu]
  rw [← sum_div, sum_sub_distrib, sum_const, ht]
  simp only [card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- A phase holonomy on one carrier, with an explicit coherent reference branch. -/
def phase (θ : ℝ) : Matrix Unit Unit ℂ := fun _ _ => Complex.exp ((θ : ℂ)*Complex.I)

lemma phase_unitary (θ : ℝ) : phase θ ∈ unitary (Matrix Unit Unit ℂ) := by
  have hnorm := Complex.norm_exp_ofReal_mul_I θ
  have h : star (Complex.exp ((θ : ℂ)*Complex.I))*Complex.exp ((θ : ℂ)*Complex.I)=1 := by
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simpa [phase, mul_apply, conjTranspose_apply, mul_comm] using h

theorem phase_probability (θ : ℝ) : meanFlag (phase θ)=(1-Real.cos θ)/2 := by
  rw [mean_trace (phase θ) (phase_unitary θ)]
  simp [phase, trace, Complex.exp_ofReal_mul_I_re]

/-- One repair event is charged its primitive toll when the flag occurs. -/
def phaseCost (toll θ : ℝ) : ℝ := toll*meanFlag (phase θ)

theorem phase_cost (toll θ : ℝ) : phaseCost toll θ=(toll/2)*(1-Real.cos θ) := by
  rw [phaseCost, phase_probability]
  ring

/-- Equal occupation probabilities alone miss a phase distinction this readout detects. -/
theorem phase_readout_matters : meanFlag (phase 0)=0 ∧ meanFlag (phase Real.pi)=1 ∧
    Complex.normSq (phase 0 () ())=Complex.normSq (phase Real.pi () ()) := by
  simp [phase_probability, phase]

/-- One such test per refresh determines the lattice coefficient within this contract. -/
theorem refresh_cost (toll θ : ℝ) (W : ℕ) :
    (∑ _ : Fin W, phaseCost toll θ)=(toll*W/2)*(1-Real.cos θ) := by
  simp only [phase_cost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The existing controlled D4 cosine limit now carries the explicit test toll and count. -/
theorem operational_density_limit (toll g : ℝ) (W : ℕ) (F : Fin 4 → Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = -F ν μ) :
    Filter.Tendsto (fun h : ℝ => GaugeContinuum.density h g (toll*W/2) F)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds ((toll*W*g^2/4)*(∑ μ, ∑ ν, F μ ν^2))) := by
  convert GaugeContinuum.density_limit g (toll*W/2) F hF using 1 <;> congr 1 <;> ring

end PMAction.InterferenceReadout
