import PMAction.D4Gauge
import Mathlib.Tactic

/-!
# The D₄ roots are isotropic through fourth order

The 24 D₄ roots `±eᵢ ± eⱼ` (the vertices of the 24-cell) are the link directions of PM's lattice.
Their moments match those of a rotation-invariant distribution through degree four:

* `odd_moments`: first and third moments vanish (central symmetry; higher odd moments are not
  stated here).
* `second_moment`: `Σ k_μ k_ν = 12 δ_{μν}`.
* `fourth_moment`: `Σ k_μ k_ν k_ρ k_σ = 4 (δ_{μν}δ_{ρσ} + δ_{μρ}δ_{νσ} + δ_{μσ}δ_{νρ})`, the isotropic
  form.
* `quartic_isotropic`: hence `Σ_k (k·w)⁴ = 12 |w|⁴` for every `w`, so the quartic directional
  moment is invariant under every orthogonal map (`quartic_rotation_invariant`).
* `hypercubic_not_isotropic`: the hypercubic directions `±eᵢ` fail this: `Σ (k·w)⁴ = 2 Σ wᵢ⁴`,
  which is not a function of `|w|` alone.

These are identities for root-direction moments. They do not by themselves prove
rotation invariance of discretization corrections to the D₄ triangle gauge action:
the corrections also depend on the triangle/link scheme and field derivatives.
Indeed midpoint links admit rotated smooth U(1) fields with different O(h²) errors
(see `LEAN-AUDIT-YANG-MILLS.md`). Neither a full gauge-action correction formula nor
O(4) restoration in the quantum continuum limit is proved here.
-/

namespace PMAction.D4Isotropy
open D4Gauge

theorem odd_moments :
    (∀ μ : Fin 4, ∑ k ∈ roots, vec k μ = 0) ∧
      ∀ μ ν ρ : Fin 4, ∑ k ∈ roots, vec k μ * vec k ν * vec k ρ = 0 := by
  constructor <;> decide +kernel

theorem second_moment : ∀ μ ν : Fin 4, ∑ k ∈ roots, vec k μ * vec k ν = if μ = ν then 12 else 0 := by
  decide +kernel

/-- Kronecker delta on `Fin 4`, as an integer. -/
def δ (μ ν : Fin 4) : ℤ := if μ = ν then 1 else 0

theorem fourth_moment : ∀ μ ν ρ σ : Fin 4,
    ∑ k ∈ roots, vec k μ * vec k ν * vec k ρ * vec k σ =
      4 * (δ μ ν * δ ρ σ + δ μ ρ * δ ν σ + δ μ σ * δ ν ρ) := by
  decide +kernel

lemma pow4_sum (a : Fin 4 → ℝ) :
    (∑ μ, a μ) ^ 4 = ∑ μ, ∑ ν, ∑ ρ, ∑ σ, a μ * a ν * a ρ * a σ := by
  simp only [Fin.sum_univ_four]
  ring

/-- **The quartic directional moment is isotropic.** -/
theorem quartic_isotropic (w : Fin 4 → ℝ) :
    ∑ k ∈ roots, (∑ μ, (vec k μ : ℝ) * w μ) ^ 4 = 12 * (∑ μ, w μ ^ 2) ^ 2 := by
  have hm : ∀ μ ν ρ σ : Fin 4,
      ∑ k ∈ roots, (vec k μ : ℝ) * vec k ν * vec k ρ * vec k σ =
        4 * ((δ μ ν * δ ρ σ + δ μ ρ * δ ν σ + δ μ σ * δ ν ρ : ℤ) : ℝ) := by
    intro μ ν ρ σ
    have := congrArg (fun z : ℤ => (z : ℝ)) (fourth_moment μ ν ρ σ)
    push_cast at this ⊢
    exact this
  calc ∑ k ∈ roots, (∑ μ, (vec k μ : ℝ) * w μ) ^ 4
      = ∑ k ∈ roots, ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
          ((vec k μ : ℝ) * vec k ν * vec k ρ * vec k σ) * (w μ * w ν * w ρ * w σ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow4_sum]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
          Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => by ring
    _ = ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
          (∑ k ∈ roots, (vec k μ : ℝ) * vec k ν * vec k ρ * vec k σ) * (w μ * w ν * w ρ * w σ) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.sum_comm]
    _ = 12 * (∑ μ, w μ ^ 2) ^ 2 := by
        simp only [hm, δ, Fin.sum_univ_four]
        norm_num
        ring

/-- **Rotation invariance of the quartic moment.** -/
theorem quartic_rotation_invariant (w w' : Fin 4 → ℝ) (h : ∑ μ, w' μ ^ 2 = ∑ μ, w μ ^ 2) :
    ∑ k ∈ roots, (∑ μ, (vec k μ : ℝ) * w' μ) ^ 4 = ∑ k ∈ roots, (∑ μ, (vec k μ : ℝ) * w μ) ^ 4 := by
  rw [quartic_isotropic, quartic_isotropic, h]

/-- The hypercubic directions `±eᵢ`. -/
def cube : Finset (Fin 4 → ℤ) :=
  (Finset.univ : Finset (Fin 4)).image (fun i => Pi.single i 1) ∪
    (Finset.univ : Finset (Fin 4)).image (fun i => Pi.single i (-1))

/-- **The hypercubic quartic moment is not isotropic.** An isotropic moment scales as `|w|⁴`.
Along `e₀` (`|w|⁴ = 1`) the hypercubic moment is `2`, so along `e₀ + e₁` (`|w|⁴ = 4`) isotropy
would give `8`. It is `4`. -/
theorem hypercubic_not_isotropic :
    ∑ v ∈ cube, (v 0) ^ 4 = 2 ∧ ∑ v ∈ cube, (v 0 + v 1) ^ 4 = 4 := by
  decide +kernel

end PMAction.D4Isotropy
