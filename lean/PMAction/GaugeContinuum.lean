import PMAction.D4Gauge
import PMAction.Gauge
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Controlled finite-spacing error for the actual Abelian D4 triangle action.
The phase model is a constant field's geometric triangle flux. No exact finite-
spacing truncation, non-Abelian BCH bound or value of beta is inferred. -/
noncomputable section
namespace PMAction.GaugeContinuum
open Finset Filter
open scoped Topology

def scaledWilson (h a : ℝ) : ℝ := (1-Real.cos (h^2*a))/h^4

/-- A quantitative small-phase error, not an exact finite-spacing equality. -/
theorem scaled_error {h a : ℝ} (hh : h ≠ 0) (ha : |h^2*a| ≤ 1) :
    |scaledWilson h a-a^2/2| ≤ |h|^4*|a|^4*(5/96) := by
  have heq : scaledWilson h a-a^2/2 =
      (1-Real.cos (h^2*a)-(h^2*a)^2/2)/h^4 := by
    unfold scaledWilson
    field_simp
  rw [heq, abs_div, abs_pow]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hh) 4)).mpr
  have hb := Real.cos_bound ha
  have habs : |1-Real.cos (h^2*a)-(h^2*a)^2/2| =
      |Real.cos (h^2*a)-(1-(h^2*a)^2/2)| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [habs]
  calc
    _ ≤ |h^2*a|^4*(5/96) := hb
    _ = (|h|^4*|a|^4*(5/96))*|h|^4 := by rw [abs_mul, abs_pow, mul_pow]; ring

/-- An exact nonsingular expression away from zero spacing. -/
theorem scaled_sinc {h : ℝ} (hh : h ≠ 0) (a : ℝ) :
    scaledWilson h a = a^2/2*(Real.sinc (h^2*a/2))^2 := by
  by_cases ha : a = 0
  · simp [ha, scaledWilson]
  have hx : h^2*a/2 ≠ 0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ hh) ha) (by norm_num)
  rw [Real.sinc_of_ne_zero hx]
  unfold scaledWilson
  rw [show h^2*a = 2*(h^2*a/2) by ring, Real.cos_two_mul_eq_one_sub]
  field_simp
  ring

/-- Controlled continuum limit of the cosine, not just its formal polynomial. -/
theorem scaled_limit (a : ℝ) :
    Tendsto (fun h : ℝ => scaledWilson h a) (𝓝[≠] 0) (𝓝 (a^2/2)) := by
  have hc : Continuous (fun h : ℝ => a^2/2*(Real.sinc (h^2*a/2))^2) := by fun_prop
  have ht' : Tendsto (fun h : ℝ => a^2/2*(Real.sinc (h^2*a/2))^2)
      (𝓝[≠] 0) (𝓝 (a^2/2))  := by
    simpa using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (scaled_sinc (by simpa using hh) a).symm

def flux (F : Fin 4 → Fin 4 → ℝ) (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) : ℝ :=
  ∑ μ, ∑ ν, F μ ν * D4Gauge.area p μ ν

/-- Sixfold triangle representation and cell volume two give denominator 12.
The constant-field phase is h² times g/4 times the area contraction. -/
def density (h g β : ℝ) (F : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (β/12)*∑ p ∈ D4Gauge.tri, scaledWilson h (g/4*flux F p)

lemma quadratic_sum (g : ℝ) (F : Fin 4 → Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = -F ν μ) :
    (∑ p ∈ D4Gauge.tri, (g/4*flux F p)^2/2) =
      ((g/4)^2/2)*(192*∑ μ, ∑ ν, F μ ν^2) := by
  calc
    _ = ((g/4)^2/2)*(∑ p ∈ D4Gauge.tri, (flux F p)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by simp only [flux]; rw [D4Gauge.flux_sum F hF]

/-- The Abelian constant-field triangle action converges to the geometric
quadratic density. Non-Abelian/path-order and nonconstant-field errors are separate. -/
theorem density_limit (g β : ℝ) (F : Fin 4 → Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = -F ν μ) :
    Tendsto (fun h : ℝ => density h g β F) (𝓝[≠] 0)
      (𝓝 ((β*g^2/2)*(∑ μ, ∑ ν, F μ ν^2))) := by
  have ht := (tendsto_finsetSum D4Gauge.tri (fun p _ => scaled_limit (g/4*flux F p)))
  have hc := (tendsto_const_nhds (x := β/12)).mul ht
  have heq : (β/12)*(∑ p ∈ D4Gauge.tri, (g/4*flux F p)^2/2) =
      (β*g^2/2)*(∑ μ, ∑ ν, F μ ν^2) := by
    rw [quadratic_sum g F hF]
    ring
  rw [heq] at hc
  exact hc

/-- Canonical Maxwell coefficient follows with the existing normalization;
its value is a conditional choice of beta, not a derivation of the coupling. -/
theorem maxwell_limit (g : ℝ) (hg : g ≠ 0) (F : Fin 4 → Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = -F ν μ) :
    Tendsto (fun h : ℝ => density h g (1/(2*g^2)) F) (𝓝[≠] 0)
      (𝓝 ((1/4 : ℝ)*(∑ μ, ∑ ν, F μ ν^2))) := by
  have hc : ((1/(2*g^2))*g^2/2 : ℝ) = 1/4 := by field_simp; norm_num
  have ht := density_limit g (1/(2*g^2)) F hF
  simpa only [hc] using ht

end PMAction.GaugeContinuum
