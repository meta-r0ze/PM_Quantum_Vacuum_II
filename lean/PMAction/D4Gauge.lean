import Mathlib.Tactic

/-!
# Minimal loops of the D₄ coordinate sector and the gauge-action normalization

The coordinate sector forced in Paper I is D₄. Its nearest-neighbour graph has triangles
(`Gauge.d4_triangle_certificate`), so the minimal Wilson loop is a triangle, not a square.

* `roots_card`, `tri_card`: 24 roots; 192 ordered root pairs with inner product one, i.e.
  32 nearest-neighbour triangles per site.
* `area_isotropic`: the triangle area tensor summed over a site is exactly
  `96 (δ_{μρ}δ_{νσ} − δ_{μσ}δ_{νρ})`. The minimal-loop action is isotropic: no preferred
  axis or plane, without adding squares or any other loops.
* `flux_sum`: hence `Σ_p (F·B_p)² = 192 Σ F²` for every antisymmetric `F`.
* `normalization`: with half-parallelogram triangle flux and the D₄ cell volume 2
  (`cartan_det`), the per-volume triangle action `β Σ (1 − cos θ)` has continuum limit equal
  to the canonical Maxwell density exactly when `β = 1/(2g²)`.

The normalization theorem matches the quadratic coefficient; the actual cosine
limit is proved in GaugeContinuum. Neither result fixes `β`.
-/

namespace PMAction.D4Gauge

/-- Box coordinates `{-1,0,1}⁴` encoded by `Fin 3`. -/
def vec (k : Fin 4 → Fin 3) : Fin 4 → ℤ := fun i => (k i : ℤ) - 1

def dot (a b : Fin 4 → ℤ) : ℤ := ∑ i, a i * b i

/-- The 24 roots: integer vectors of squared length two. -/
def roots : Finset (Fin 4 → Fin 3) := Finset.univ.filter fun k => dot (vec k) (vec k) = 2

/-- Ordered root pairs with inner product one: `0, a, b` is a nearest-neighbour triangle. -/
def tri : Finset ((Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :=
  (roots ×ˢ roots).filter fun p => dot (vec p.1) (vec p.2) = 1

def area (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) (μ ν : Fin 4) : ℤ :=
  vec p.1 μ * vec p.2 ν - vec p.1 ν * vec p.2 μ

theorem roots_card : roots.card = 24 := by decide +kernel
theorem tri_card : tri.card = 192 := by decide +kernel

/-- Isotropy of the triangle area tensor. -/
theorem area_isotropic : ∀ μ ν ρ σ : Fin 4,
    (∑ p ∈ tri, area p μ ν * area p ρ σ) =
      96 * ((if μ = ρ ∧ ν = σ then 1 else 0) - (if μ = σ ∧ ν = ρ then 1 else 0)) := by
  decide +kernel


lemma swap4 {X : Type*} (s : Finset X) (h : X → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ x ∈ s, ∑ a, ∑ b, ∑ c, ∑ d, h x a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x ∈ s, h x a b c d := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

lemma sq_expand (f : Fin 4 → Fin 4 → ℝ) :
    (∑ μ, ∑ ν, f μ ν)^2 = ∑ μ, ∑ ρ, ∑ ν, ∑ σ, f μ ν * f ρ σ := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_mul_sum]

lemma delta_reduce (F : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    (∑ ρ, ∑ σ, F ρ σ * (96 * ((if μ = ρ ∧ ν = σ then 1 else 0) -
      (if μ = σ ∧ ν = ρ then 1 else 0)))) = 96 * (F μ ν - F ν μ) := by
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_four] <;> ring

/-- Squared flux through the 192 ordered triangles at a site, for any antisymmetric field
strength: `Σ_p (Σ_{μν} F_{μν} B^p_{μν})² = 192 Σ_{μν} F_{μν}²`. -/
theorem flux_sum (F : Fin 4 → Fin 4 → ℝ) (hF : ∀ μ ν, F μ ν = -F ν μ) :
    (∑ p ∈ tri, (∑ μ, ∑ ν, F μ ν * area p μ ν)^2) = 192 * ∑ μ, ∑ ν, (F μ ν)^2 := by
  have hT : ∀ μ ν ρ σ : Fin 4, (∑ p ∈ tri, (area p μ ν : ℝ) * area p ρ σ) =
      96 * ((if μ = ρ ∧ ν = σ then 1 else 0) - (if μ = σ ∧ ν = ρ then 1 else 0)) := by
    intro μ ν ρ σ
    have h := area_isotropic μ ν ρ σ
    have h' : ((∑ p ∈ tri, area p μ ν * area p ρ σ : ℤ) : ℝ) =
        ((96 * ((if μ = ρ ∧ ν = σ then 1 else 0) - (if μ = σ ∧ ν = ρ then 1 else 0)) : ℤ) : ℝ) := by
      rw [h]
    push_cast at h'
    simpa [apply_ite (fun z : ℤ => (z : ℝ))] using h'
  simp_rw [sq_expand]
  rw [swap4]
  have inner : ∀ μ ρ ν σ, (∑ p ∈ tri, F μ ν * area p μ ν * (F ρ σ * area p ρ σ)) =
      F μ ν * (F ρ σ * (96 * ((if μ = ρ ∧ ν = σ then 1 else 0) -
        (if μ = σ ∧ ν = ρ then 1 else 0)))) := by
    intro μ ρ ν σ
    rw [← hT, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [inner]
  have reorder : ∀ μ, (∑ ρ, ∑ ν, ∑ σ, F μ ν * (F ρ σ * (96 * ((if μ = ρ ∧ ν = σ then 1 else 0) -
        (if μ = σ ∧ ν = ρ then 1 else 0))))) = ∑ ν, F μ ν * (96 * (F μ ν - F ν μ)) := by
    intro μ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← delta_reduce F μ ν, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
  simp_rw [reorder]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hF ν μ]; ring

/-- Continuum normalization of the minimal-loop action, given the flux sum `Φ = Σ F²`.
Each unoriented triangle appears as six ordered pairs across its three vertices, a
triangle's flux is half its parallelogram's (`θ = (g/4) Σ F B`), and the D₄ cell has
volume `2` (`cartan_det`). Then `β · (1/6) Σ_p θ_p²/2` per volume equals the canonical
Maxwell density `¼ Φ` exactly when `β = 1/(2g²)`. -/
theorem normalization (Φ g β : ℝ) (hg : g ≠ 0) (hΦ : 0 < Φ) :
    β * ((1/6) * ((g/4)^2 * (192 * Φ)) / 2) / 2 = (1/4) * Φ ↔ β = 1/(2*g^2) := by
  constructor
  · intro he
    have hg2 : 0 < g^2 := by positivity
    field_simp at he ⊢
    nlinarith [hΦ, hg2]
  · rintro rfl; field_simp; ring

theorem cartan_det :
    Matrix.det (!![2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] : Matrix (Fin 4) (Fin 4) ℤ) = 4 := by
  decide +kernel

end PMAction.D4Gauge
