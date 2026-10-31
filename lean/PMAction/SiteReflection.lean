import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

/-!
# Reflection positivity for an action that splits across a site reflection

`D4Reflection.one_side` shows that no D₄ triangle crosses the site-reflection plane, so PM's
lattice action splits as `S = S₊ + θS₊`. Here is the measure-theoretic consequence.

Configurations are `(p, u, d)`: links in the plane, above it and below it. The reference measure
is a product `μP ⊗ μQ ⊗ μQ` (product Haar on links). The action is `A(p, u) + A(p, d)`, and the
reflection swaps `u` and `d`. For an observable `F(p, u)` of the upper half, `θF(p, u, d) = conj F(p, d)`.

* `reflection_identity`: `∫ F · θF · e^{−S} = ∫_p |G p|²`, where `G p = ∫_u F(p, u) e^{−A(p, u)}`.
* `reflection_positive`: hence `∫ F · θF · e^{−S}` is real and nonnegative. This is
  Osterwalder–Schrader reflection positivity for the lattice measure.

Hypotheses: measurable, bounded `F`; measurable `A` bounded below; probability reference measures.
**Scope.** This module proves the abstract measure-theoretic identity. The concrete
finite shared-directed-link bridge is proved in `FiniteReflection`, `FiniteD4Reflection`
and `D4ActionReflection`: geometric link reindexing, product Haar factorization, the exact
D₄ action split, and normalized Gibbs reflection positivity. Opposite directed links
are independent in that model; `ReciprocalReflection` proves the reciprocal-link
bridge and gauge invariance for one explicitly constructed physical measure.
A transfer matrix, nonnegative Hamiltonian and quantum continuum limit remain open.
-/

noncomputable section
namespace PMAction.SiteReflection
open MeasureTheory Complex

variable {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]

/-- The weighted upper-half observable. -/
def half (F : P × Q → ℂ) (A : P × Q → ℝ) (x : P × Q) : ℂ := F x * (Real.exp (-A x) : ℂ)

/-- Its integral over the upper links, at fixed plane links. -/
def G (μQ : Measure Q) (F : P × Q → ℂ) (A : P × Q → ℝ) (p : P) : ℂ :=
  ∫ u, half F A (p, u) ∂μQ

/-- The reflected expectation's integrand, `F · θF · e^{−(S₊ + θS₊)}`. -/
def integrand (F : P × Q → ℂ) (A : P × Q → ℝ) (ω : P × (Q × Q)) : ℂ :=
  F (ω.1, ω.2.1) * starRingEnd ℂ (F (ω.1, ω.2.2)) *
    (Real.exp (-(A (ω.1, ω.2.1) + A (ω.1, ω.2.2))) : ℂ)

omit [MeasurableSpace P] [MeasurableSpace Q] in
lemma integrand_eq (F : P × Q → ℂ) (A : P × Q → ℝ) (ω : P × (Q × Q)) :
    integrand F A ω = half F A (ω.1, ω.2.1) * starRingEnd ℂ (half F A (ω.1, ω.2.2)) := by
  simp only [integrand, half, map_mul, Complex.conj_ofReal, neg_add, Real.exp_add,
    Complex.ofReal_mul]
  ring

/-- **The reflection identity.** -/
theorem reflection_identity (μP : Measure P) (μQ : Measure Q) [IsProbabilityMeasure μP]
    [IsProbabilityMeasure μQ] (F : P × Q → ℂ) (A : P × Q → ℝ) (hF : Measurable F)
    (hA : Measurable A) {B M : ℝ} (hFb : ∀ x, ‖F x‖ ≤ B) (hAb : ∀ x, -M ≤ A x) :
    ∫ ω, integrand F A ω ∂(μP.prod (μQ.prod μQ)) =
      ((∫ p, Complex.normSq (G μQ F A p) ∂μP : ℝ) : ℂ) := by
  have hmeas : Measurable (integrand F A) := by
    unfold integrand
    fun_prop
  have hbound : ∀ ω, ‖integrand F A ω‖ ≤ B * B * Real.exp (2 * M) := by
    intro ω
    simp only [integrand, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 := hFb (ω.1, ω.2.1)
    have h2 := hFb (ω.1, ω.2.2)
    have h3 : Real.exp (-(A (ω.1, ω.2.1) + A (ω.1, ω.2.2))) ≤ Real.exp (2 * M) :=
      Real.exp_le_exp.mpr (by linarith [hAb (ω.1, ω.2.1), hAb (ω.1, ω.2.2)])
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hB0) h3 (Real.exp_pos _).le
      (mul_nonneg hB0 hB0)
  have hint : Integrable (integrand F A) (μP.prod (μQ.prod μQ)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)
  rw [integral_prod _ hint, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  simp_rw [integrand_eq]
  rw [integral_prod_mul (fun u => half F A (p, u)) (fun d => starRingEnd ℂ (half F A (p, d))),
    integral_conj, Complex.mul_conj]
  rfl

/-- **Reflection positivity.** -/
theorem reflection_positive (μP : Measure P) (μQ : Measure Q) [IsProbabilityMeasure μP]
    [IsProbabilityMeasure μQ] (F : P × Q → ℂ) (A : P × Q → ℝ) (hF : Measurable F)
    (hA : Measurable A) {B M : ℝ} (hFb : ∀ x, ‖F x‖ ≤ B) (hAb : ∀ x, -M ≤ A x) :
    (∫ ω, integrand F A ω ∂(μP.prod (μQ.prod μQ))).im = 0 ∧
      0 ≤ (∫ ω, integrand F A ω ∂(μP.prod (μQ.prod μQ))).re := by
  rw [reflection_identity μP μQ F A hF hA hFb hAb, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg fun p => Complex.normSq_nonneg _⟩

/-- The Osterwalder–Schrader pairing of two upper-half observables. -/
def pairing (F F' : P × Q → ℂ) (A : P × Q → ℝ) (ω : P × (Q × Q)) : ℂ :=
  F (ω.1, ω.2.1) * starRingEnd ℂ (F' (ω.1, ω.2.2)) *
    (Real.exp (-(A (ω.1, ω.2.1) + A (ω.1, ω.2.2))) : ℂ)

/-- **The OS inner product is the `L²` inner product of the plane functions.** For observables
`F`, `F'` of the upper half, `∫ F · θF' · e^{−S} = ∫_p G_F(p) · conj G_{F'}(p)`. So the
Osterwalder–Schrader form is Hermitian and positive semidefinite, and `F ↦ G_F` maps it
isometrically into `L²(μP)`: the physical Hilbert space is the closure of the `G_F`. -/
theorem os_inner_product (μP : Measure P) (μQ : Measure Q) [IsProbabilityMeasure μP]
    [IsProbabilityMeasure μQ] (F F' : P × Q → ℂ) (A : P × Q → ℝ) (hF : Measurable F)
    (hF' : Measurable F') (hA : Measurable A) {B M : ℝ} (hFb : ∀ x, ‖F x‖ ≤ B)
    (hFb' : ∀ x, ‖F' x‖ ≤ B) (hAb : ∀ x, -M ≤ A x) :
    ∫ ω, pairing F F' A ω ∂(μP.prod (μQ.prod μQ)) =
      ∫ p, G μQ F A p * starRingEnd ℂ (G μQ F' A p) ∂μP := by
  have hmeas : Measurable (pairing F F' A) := by
    unfold pairing
    fun_prop
  have hbound : ∀ ω, ‖pairing F F' A ω‖ ≤ B * B * Real.exp (2 * M) := by
    intro ω
    simp only [pairing, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 := hFb (ω.1, ω.2.1)
    have h2 := hFb' (ω.1, ω.2.2)
    have h3 : Real.exp (-(A (ω.1, ω.2.1) + A (ω.1, ω.2.2))) ≤ Real.exp (2 * M) :=
      Real.exp_le_exp.mpr (by linarith [hAb (ω.1, ω.2.1), hAb (ω.1, ω.2.2)])
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hB0) h3 (Real.exp_pos _).le
      (mul_nonneg hB0 hB0)
  have hint : Integrable (pairing F F' A) (μP.prod (μQ.prod μQ)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : ∀ ud : Q × Q, pairing F F' A (p, ud) =
      half F A (p, ud.1) * starRingEnd ℂ (half F' A (p, ud.2)) := by
    intro ud
    simp only [pairing, half, map_mul, Complex.conj_ofReal, neg_add, Real.exp_add,
      Complex.ofReal_mul]
    ring
  simp only [e]
  rw [integral_prod_mul (fun u => half F A (p, u)) (fun d => starRingEnd ℂ (half F' A (p, d))),
    integral_conj]
  rfl

end PMAction.SiteReflection
