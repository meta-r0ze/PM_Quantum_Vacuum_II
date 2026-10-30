import PMAction.ConcreteFermion
import PMAction.DetuningMass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Spatial continuum of the actual sine-momentum Hamiltonian

For `hamiltonian k (wilson k)`, every energy lies on a light or heavy branch (`branches`).
At lattice momentum `k = a p` (spacing `a`, continuum momentum `p`):

* `light_continuum`: on the light branch
  `|E²/a² − |p|²| ≤ (3/4) a² Σ pⱼ⁴ + a⁶ |p|⁸/16` whenever `|a pⱼ| ≤ 1`;
* `light_tendsto`: hence `E(a)²/a² → |p|²` as `a → 0⁺`, i.e. the light branch has the massless
  relativistic dispersion with unit speed;
* `heavy_decouples`: the heavy branch has `E²/a² ≥ 1/a²` and leaves the spectrum.

On the torus of `RealSpaceFourier`, `kOf c = 2πc/(n+1) = a·(2πc/L)` with `a = L/(n+1)`.
The statement is about the Hamiltonian dispersion; the time discretization is the separate
`PathError` bound. No physical light mass is produced here: the light-branch Wilson mass is at
most `a⁴|p|⁴/4` in lattice units and vanishes in the limit.
-/

noncomputable section
namespace PMAction.SpatialContinuum
open Matrix ConcreteFermion DomainWallSpectrum

/-- **Every energy is on the light or the heavy branch** (the actual sine-momentum Hamiltonian). -/
theorem branches (k : Fin 3 → ℝ) (E : ℝ) (v : Sites → ℂ) (hv : v ≠ 0)
    (he : hamiltonian k (wilson k) *ᵥ v = E • v) :
    E ^ 2 = kineticNorm k + (DetuningMass.lightMass (wilson k)) ^ 2 ∨
      E ^ 2 = kineticNorm k + (DetuningMass.lightMass (wilson k) + 1) ^ 2 := by
  have hk := kinetic_relations alpha beta gamma k clifford alpha_gamma
  exact energy_branches (momentum alpha k) beta gamma (wilson k) (kineticNorm k) E
    beta_square gamma_square beta_gamma hk.1 hk.2.1 hk.2.2 v hv he

lemma sin_sq_close (x : ℝ) (hx : |x| ≤ 1) : |Real.sin x ^ 2 - x ^ 2| ≤ 3 / 4 * x ^ 4 := by
  have hb := Real.sin_bound hx
  have ha : |x| ^ 4 ≤ |x| ^ 3 := by
    have := pow_le_pow_of_le_one (abs_nonneg x) hx (show 3 ≤ 4 by norm_num); exact this
  have h1 : |Real.sin x - x| ≤ |x| ^ 3 / 4 := by
    have : |Real.sin x - x| ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
      have := abs_sub_le (Real.sin x) (x - x ^ 3 / 6) x
      simpa [abs_div, abs_pow] using this
    rw [abs_div, abs_pow] at this
    norm_num at this
    nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
  have h2 : |Real.sin x + x| ≤ 9 / 4 * |x| := by
    have : |Real.sin x + x| ≤ |Real.sin x - x| + 2 * |x| := by
      have := abs_add_le (Real.sin x - x) (2 * x)
      rw [show Real.sin x - x + 2 * x = Real.sin x + x by ring, abs_mul] at this
      simpa using this
    have h3 : |x| ^ 3 ≤ |x| := by
      have := pow_le_pow_of_le_one (abs_nonneg x) hx (show 1 ≤ 3 by norm_num); simpa using this
    linarith
  have hprod : |Real.sin x ^ 2 - x ^ 2| = |Real.sin x - x| * |Real.sin x + x| := by
    rw [← abs_mul]; congr 1; ring
  rw [hprod]
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  rw [hx4]
  calc |Real.sin x - x| * |Real.sin x + x| ≤ (|x| ^ 3 / 4) * (9 / 4 * |x|) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 9 / 16 * |x| ^ 4 := by ring
    _ ≤ 3 / 4 * |x| ^ 4 := by nlinarith [pow_nonneg (abs_nonneg x) 4]

lemma wilson_le (k : Fin 3 → ℝ) : wilson k ≤ (∑ j, k j ^ 2) / 2 := by
  unfold wilson
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun j _ => by
    have := Real.one_sub_sq_div_two_le_cos (x := k j); linarith

/-- Squared Euclidean norm. -/
def psq (p : Fin 3 → ℝ) : ℝ := ∑ j, p j ^ 2

/-- **The light branch has the massless continuum dispersion.** At lattice momentum `k = a p`
with `|a pⱼ| ≤ 1`, a light-branch energy satisfies
`|E²/a² − |p|²| ≤ (3/4) a² Σ pⱼ⁴ + a⁶ |p|⁸ / 16`. -/
theorem light_continuum (p : Fin 3 → ℝ) (a : ℝ) (ha : 0 < a) (hsmall : ∀ j, |a * p j| ≤ 1)
    (E : ℝ) (hlight : E ^ 2 = kineticNorm (fun j => a * p j) +
      (DetuningMass.lightMass (wilson (fun j => a * p j))) ^ 2) :
    |E ^ 2 / a ^ 2 - psq p| ≤ 3 / 4 * a ^ 2 * ∑ j, p j ^ 4 + a ^ 6 * psq p ^ 4 / 16 := by
  set k : Fin 3 → ℝ := fun j => a * p j
  set w := wilson k
  set lm := DetuningMass.lightMass w
  have ha2 : 0 < a ^ 2 := by positivity
  have hw0 : 0 ≤ w := (wilson_bounds k).1
  have hwle : w ≤ a ^ 2 * psq p / 2 := by
    have := wilson_le k
    simp only [k, mul_pow, ← Finset.mul_sum] at this
    simpa [psq] using this
  have hlm := DetuningMass.mass_le w
  have hlm2 : lm ^ 2 ≤ (a ^ 2 * psq p / 2) ^ 4 := by
    have h1 : lm ^ 2 ≤ (w ^ 2) ^ 2 := by nlinarith [hlm.1, hlm.2]
    have h2 : (w ^ 2) ^ 2 ≤ (a ^ 2 * psq p / 2) ^ 4 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ hw0 hwle 4
    linarith
  have hkin : |kineticNorm k - a ^ 2 * psq p| ≤ 3 / 4 * a ^ 4 * ∑ j, p j ^ 4 := by
    unfold kineticNorm psq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have := sin_sq_close (a * p j) (hsmall j)
    simp only [k]
    calc |Real.sin (a * p j) ^ 2 - a ^ 2 * p j ^ 2| = |Real.sin (a * p j) ^ 2 - (a * p j) ^ 2| := by ring_nf
      _ ≤ 3 / 4 * (a * p j) ^ 4 := this
      _ = 3 / 4 * a ^ 4 * p j ^ 4 := by ring
  have heq : E ^ 2 / a ^ 2 - psq p = (kineticNorm k - a ^ 2 * psq p) / a ^ 2 + lm ^ 2 / a ^ 2 := by
    rw [hlight]; field_simp; ring
  rw [heq]
  have hlm0 : 0 ≤ lm ^ 2 / a ^ 2 := by positivity
  calc |(kineticNorm k - a ^ 2 * psq p) / a ^ 2 + lm ^ 2 / a ^ 2|
      ≤ |(kineticNorm k - a ^ 2 * psq p) / a ^ 2| + |lm ^ 2 / a ^ 2| := abs_add_le _ _
    _ ≤ 3 / 4 * a ^ 2 * ∑ j, p j ^ 4 + a ^ 6 * psq p ^ 4 / 16 := by
      rw [abs_div, abs_of_pos ha2, abs_of_nonneg hlm0]
      have e1 : |kineticNorm k - a ^ 2 * psq p| / a ^ 2 ≤ 3 / 4 * a ^ 2 * ∑ j, p j ^ 4 := by
        rw [div_le_iff₀ ha2]; nlinarith [hkin]
      have e2 : lm ^ 2 / a ^ 2 ≤ a ^ 6 * psq p ^ 4 / 16 := by
        rw [div_le_iff₀ ha2]; nlinarith [hlm2]
      linarith

/-- **The heavy branch decouples**: its energies satisfy `E²/a² ≥ 1/a²`. -/
theorem heavy_decouples (k : Fin 3 → ℝ) (a : ℝ) (ha : 0 < a) (E : ℝ)
    (hheavy : E ^ 2 = kineticNorm k + (DetuningMass.lightMass (wilson k) + 1) ^ 2) :
    1 / a ^ 2 ≤ E ^ 2 / a ^ 2 := by
  have h0 := (DetuningMass.mass_le (wilson k)).1
  have hk := kinetic_nonnegative k
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-- **Controlled limit of the light branch.**  For a fixed continuum momentum `p`, any choice of
light-branch energies at lattice momentum `a p` satisfies `E(a)²/a² → |p|²` as `a → 0⁺`. -/
theorem light_tendsto (p : Fin 3 → ℝ) (E : ℝ → ℝ)
    (hE : ∀ a : ℝ, 0 < a → E a ^ 2 = kineticNorm (fun j => a * p j) +
      (DetuningMass.lightMass (wilson (fun j => a * p j))) ^ 2) :
    Filter.Tendsto (fun a => E a ^ 2 / a ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (psq p)) := by
  set P := ∑ j, |p j| + 1
  have hP : 0 < P := by positivity
  have hpj : ∀ j, |p j| ≤ P := fun j => by
    have := Finset.single_le_sum (f := fun j => |p j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    simp only [P]; linarith
  set B : ℝ → ℝ := fun a => 3 / 4 * a ^ 2 * ∑ j, p j ^ 4 + a ^ 6 * psq p ^ 4 / 16
  have hB : Filter.Tendsto B (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous B := by fun_prop
    have := hc.tendsto 0
    simp only [B, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      zero_div, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hB
  have hsm : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < a ∧ a < 1 / P := by
    have h1 : Set.Ioo (0 : ℝ) (1 / P) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [h1] with a ha using ha
  filter_upwards [hsm] with a ha
  rw [Real.norm_eq_abs]
  refine light_continuum p a ha.1 (fun j => ?_) (E a) (hE a ha.1)
  rw [abs_mul, abs_of_pos ha.1]
  calc a * |p j| ≤ a * P := mul_le_mul_of_nonneg_left (hpj j) ha.1.le
    _ ≤ 1 / P * P := by gcongr; exact ha.2.le
    _ = 1 := by field_simp

end PMAction.SpatialContinuum
