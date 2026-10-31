import PMAction.LinkConsistency

/-! Compact-region error control for the D₄ gauge density. The uniform constant
is derived from the explicit triangle remainder and compactness, under a common
local C¹,¹ derivative bound (within distance two of each point of the region) and
continuous derivative. No gauge regularity or link law
is selected by persistence here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.UniformGaugeAction
open Matrix VaryingFields Set Filter Topology
open scoped Matrix.Norms.L2Operator

section General
variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R]

theorem bound_continuous (A : E → E →L[ℝ] R) (DA : E → E →L[ℝ] (E →L[ℝ] R))
    (hA : Continuous A) (hDA : Continuous DA) (L : ℝ) (a b : E) :
    Continuous (fun x => triangleBound A DA x L a b) := by
  unfold triangleBound
  fun_prop

/-- A common spatial bound follows from compactness of the local Taylor data. -/
theorem triangle_uniform [CompleteSpace R] {A : E → E →L[ℝ] R}
    {DA : E → E →L[ℝ] (E →L[ℝ] R)} {s : Set E} (hs : IsCompact s)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L : ℝ} (hL0 : 0 ≤ L) (a b : E)
    (hL : ∀ x ∈ s, ∀ y, ‖y-x‖ ≤ ‖a‖+‖b‖ → ‖DA y-DA x‖ ≤ L*‖y-x‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖triangle A x a b h-(1+(h^2/2) • curvature A DA x a b)‖ ≤ C*h^3 := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  obtain ⟨B,hB⟩ := hs.bddAbove_image (bound_continuous A DA hAc hDA L a b).continuousOn
  refine ⟨max B 0,le_max_right _ _,fun x hx h hh h1 => ?_⟩
  have hb := (triangle_expand_explicit hA hL0 a b (hL x hx)).2 h hh h1
  have hc : triangleBound A DA x L a b ≤ max B 0 :=
    (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  exact hb.trans (mul_le_mul_of_nonneg_right hc (by positivity))
end General

abbrev V := Fin 4 → ℝ
variable {N : ℕ}

/-- The quadratic coefficient of a single triangle, in half-curvature form. -/
def triangleTarget (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x a b : V) : ℝ :=
  (∑ i, ∑ j, ‖((1/2 : ℝ) • curvature A DA x a b) i j‖^2)/2

/-- The unitary Wilson identity preserves the extra h-power uniformly. -/
theorem wilson_uniform {P : V → ℝ → Matrix (Fin N) (Fin N) ℂ}
    {G : V → Matrix (Fin N) (Fin N) ℂ} {s : Set V} (hs : IsCompact s)
    (hG : Continuous G) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 → star (P x h)*P x h=1)
    (he : ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 → ‖(P x h-1)-h^2 • G x‖ ≤ K*h^3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (1-P x h)).re/h^4-(∑ i, ∑ j, ‖G x i j‖^2)/2| ≤ C*h := by
  obtain ⟨B,hB⟩ := hs.bddAbove_image hG.norm.continuousOn
  let M := max B 0
  refine ⟨(N : ℝ)^2*(K*(2*M+K))/2,by dsimp [M]; positivity,fun x hx h hh h1 => ?_⟩
  have hM : ‖G x‖ ≤ M := (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hb := LinkConsistency.wilson_of_expansion (P x h) (G x) (hP x hx h hh h1) hK hh h1
    (he x hx h hh h1)
  refine hb.trans ?_
  gcongr

/-- Uniform control for midpoint-link triangles, with their actual Taylor data. -/
theorem triangle_wilson_uniform {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V}
    (hs : IsCompact s) (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    {L : ℝ} (hL0 : 0 ≤ L) (hskew : ∀ y v, star (A y v) = -A y v) (a b : V)
    (hL : ∀ x ∈ s, ∀ y, ‖y-x‖ ≤ ‖a‖+‖b‖ → ‖DA y-DA x‖ ≤ L*‖y-x‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (1-triangle A x a b h)).re/h^4-triangleTarget A DA x a b| ≤ C*h := by
  obtain ⟨K,hK,hb⟩ := triangle_uniform hs hA hDA hL0 a b hL
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hc : Continuous (fun x => (1/2 : ℝ) • curvature A DA x a b) := by
    unfold curvature
    fun_prop
  apply wilson_uniform (P := fun x h => triangle A x a b h) hs hc hK
  · intro x hx h hh h1
    exact (Unitary.mem_iff.mp (triangle_unitary hskew x a b h)).1
  · intro x hx h hh h1
    have heq : (triangle A x a b h-1)-h^2 • ((1/2 : ℝ) • curvature A DA x a b)=
        triangle A x a b h-(1+(h^2/2) • curvature A DA x a b) := by
      rw [smul_smul]
      module
    rw [heq]
    exact hb x hx h hh.le h1

/-- D₄ sum of the triangle quadratic coefficients. -/
def quadraticDensity (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x : V) (β : ℝ) : ℝ :=
  (β/12)*∑ p ∈ D4Gauge.tri, triangleTarget A DA x (rv p.1) (rv p.2)

def yangMillsDensity (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x : V) (β : ℝ) : ℝ :=
  (β/2)*∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖^2

theorem quadratic_uniform {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V}
    (hs : IsCompact s) (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x ∈ s, ∀ y, ‖y-x‖ ≤ 2 → ‖DA y-DA x‖ ≤ L*‖y-x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |d4Density A x β h-quadraticDensity A DA x β| ≤ C*h := by
  have hp (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :=
    triangle_wilson_uniform hs hA hDA hL0 hskew (rv p.1) (rv p.2)
      (fun x hx y hy => hL x hx y (hy.trans (rv_pair p)))
  choose C hC hb using hp
  refine ⟨|β|/12*∑ p ∈ D4Gauge.tri, C p,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => hC p),fun x hx h hh h1 => ?_⟩
  rw [d4Density,quadraticDensity,← mul_sub,← Finset.sum_sub_distrib,abs_mul]
  have hs : |∑ p ∈ D4Gauge.tri,
      ((trace (1-triangle A x (rv p.1) (rv p.2) h)).re/h^4-
        triangleTarget A DA x (rv p.1) (rv p.2))| ≤ (∑ p ∈ D4Gauge.tri, C p)*h := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hb p x hx h hh h1)
  rw [show |β/12|=|β|/12 by rw [abs_div]; norm_num]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

lemma limit_of_bound (f : ℝ → ℝ) (q C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ h : ℝ, 0 < h → h ≤ 1 → |f h-q| ≤ C*h) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 q) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε/(C+1)),by positivity,fun h hh hd => ?_⟩
  have hpos : 0 < h := hh
  rw [Real.dist_eq,sub_zero,abs_of_pos hpos] at hd
  rw [Real.dist_eq]
  have h1 : h ≤ 1 := (hd.trans_le (min_le_left _ _)).le
  have h2 : h < ε/(C+1) := hd.trans_le (min_le_right _ _)
  calc
    _ ≤ C*h := hb h hh h1
    _ ≤ (C+1)*h := by nlinarith [Set.mem_Ioi.mp hh]
    _ < (C+1)*(ε/(C+1)) := by gcongr
    _ = ε := by field_simp

/-- The previously pointwise Yang–Mills estimate is uniform over the compact
region. A common C¹,¹ bound is retained; compactness supplies the common constant. -/
theorem yang_mills_uniform {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V}
    (hs : IsCompact s) (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x ∈ s, ∀ y, ‖y-x‖ ≤ 2 → ‖DA y-DA x‖ ≤ L*‖y-x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |d4Density A x β h-yangMillsDensity A DA x β| ≤ C*h := by
  obtain ⟨C,hC,hb⟩ := quadratic_uniform hs hA hDA hL0 hL hskew β
  refine ⟨C,hC,fun x hx h hh h1 => ?_⟩
  have hnew := limit_of_bound (fun h => d4Density A x β h) (quadraticDensity A DA x β) C hC
    (hb x hx)
  have hold := d4_yang_mills_tendsto_loc hA hL0 (hL x hx) hskew β
  have heq : quadraticDensity A DA x β=yangMillsDensity A DA x β :=
    tendsto_nhds_unique hnew hold
  rw [← heq]
  exact hb x hx h hh h1

end PMAction.UniformGaugeAction
