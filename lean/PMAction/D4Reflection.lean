import PMAction.D4Gauge
import Mathlib.Tactic

/-!
# Site reflection of the D₄ lattice: no triangle crosses the plane

The geometric half of Osterwalder–Seiler reflection positivity (`YANG-MILLS-STATUS.md`, item 2)
needs a reflection that maps PM's lattice to itself and splits its action into two reflected
halves. The site reflection `θ : x₀ ↦ −x₀` does both.

* `reflect_root`, `reflect_tri`: `θ` maps D₄ roots to roots and nearest-neighbour triangles to
  triangles (it preserves the dot product).
* `no_crossing_pair`: no triangle `0, a, b` has `a₀ = 1` and `b₀ = −1` (their dot product would be
  at most `0`, not `1`).
* `one_side`: hence every triangle based at a site with integer `x₀` has all three vertices in
  `{x₀ ≥ 0}` or all in `{x₀ ≤ 0}`. The D₄ triangle action splits as `S₊ + θS₊`, with triangles in
  the plane `x₀ = 0` shared, exactly as for the hypercubic Wilson action.

This is the combinatorial input to `SiteReflection.reflection_positive`.
-/

namespace PMAction.D4Reflection
open D4Gauge

/-- The site reflection on index vectors (`Fin 3` encodes `−1, 0, 1`). -/
def θ (k : Fin 4 → Fin 3) : Fin 4 → Fin 3 := fun i => if i = 0 then Fin.rev (k i) else k i

theorem vec_reflect (k : Fin 4 → Fin 3) (i : Fin 4) :
    vec (θ k) i = if i = 0 then -vec k i else vec k i := by
  revert k i; decide +kernel

/-- The reflection preserves the dot product. -/
theorem dot_reflect (a b : Fin 4 → Fin 3) : dot (vec (θ a)) (vec (θ b)) = dot (vec a) (vec b) := by
  simp only [dot, Fin.sum_univ_four, vec_reflect]
  simp

theorem reflect_root : ∀ k ∈ roots, θ k ∈ roots := by
  intro k hk
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  rw [dot_reflect, hk]

theorem reflect_tri : ∀ p ∈ tri, (θ p.1, θ p.2) ∈ tri := by
  intro p hp
  simp only [tri, Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨⟨reflect_root _ hp.1.1, reflect_root _ hp.1.2⟩, by rw [dot_reflect]; exact hp.2⟩

/-- Shape of a root: coordinates in `[−1, 1]`, and if the 0-coordinate is nonzero, exactly one
other coordinate is nonzero. -/
theorem root_shape : ∀ k ∈ roots, (∀ i, |vec k i| ≤ 1) ∧
    (vec k 0 ≠ 0 → |vec k 1| + |vec k 2| + |vec k 3| = 1) := by decide +kernel

lemma prod_le_abs (x y : ℤ) (hy : |y| ≤ 1) : x * y ≤ |x| := by
  calc x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul _ _
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = |x| := mul_one _

theorem no_crossing_pair : ∀ p ∈ tri, ¬ (vec p.1 0 = 1 ∧ vec p.2 0 = -1) ∧
    ¬ (vec p.1 0 = -1 ∧ vec p.2 0 = 1) := by
  intro p hp
  simp only [tri, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨ha, hb⟩, hd⟩ := hp
  obtain ⟨_, hsa⟩ := root_shape _ ha
  obtain ⟨hbb, _⟩ := root_shape _ hb
  simp only [dot, Fin.sum_univ_four] at hd
  have h1 := prod_le_abs (vec p.1 1) (vec p.2 1) (hbb 1)
  have h2 := prod_le_abs (vec p.1 2) (vec p.2 2) (hbb 2)
  have h3 := prod_le_abs (vec p.1 3) (vec p.2 3) (hbb 3)
  constructor
  · rintro ⟨e1, e2⟩
    have hs := hsa (by rw [e1]; norm_num)
    rw [e1, e2] at hd
    linarith
  · rintro ⟨e1, e2⟩
    have hs := hsa (by rw [e1]; norm_num)
    rw [e1, e2] at hd
    linarith

theorem coord_range : ∀ k ∈ roots, -1 ≤ vec k 0 ∧ vec k 0 ≤ 1 := fun k hk =>
  abs_le.mp ((root_shape k hk).1 0)

/-- **Every triangle lies on one side of the plane.** -/
theorem one_side (x0 : ℤ) : ∀ p ∈ tri,
    (0 ≤ x0 ∧ 0 ≤ x0 + vec p.1 0 ∧ 0 ≤ x0 + vec p.2 0) ∨
      (x0 ≤ 0 ∧ x0 + vec p.1 0 ≤ 0 ∧ x0 + vec p.2 0 ≤ 0) := by
  intro p hp
  have hr := Finset.mem_filter.mp hp
  have h1 := coord_range p.1 (Finset.mem_product.mp hr.1).1
  have h2 := coord_range p.2 (Finset.mem_product.mp hr.1).2
  have hc := no_crossing_pair p hp
  rcases lt_trichotomy x0 0 with h | h | h
  · right
    refine ⟨h.le, ?_, ?_⟩
    · by_contra hn
      have : vec p.1 0 = 1 ∧ x0 = -1 := by omega
      have : vec p.2 0 = -1 ∨ x0 + vec p.2 0 ≤ 0 := by omega
      rcases this with h3 | h3
      · exact hc.1 ⟨by omega, h3⟩
      · omega
    · by_contra hn
      have : vec p.2 0 = 1 ∧ x0 = -1 := by omega
      by_cases h3 : vec p.1 0 = -1
      · exact hc.2 ⟨h3, by omega⟩
      · omega
  · subst h
    by_cases h3 : vec p.1 0 = -1
    · right; refine ⟨le_rfl, by omega, ?_⟩
      by_contra hn
      exact hc.2 ⟨h3, by omega⟩
    · by_cases h4 : vec p.2 0 = -1
      · right; refine ⟨le_rfl, ?_, by omega⟩
        by_contra hn
        exact hc.1 ⟨by omega, h4⟩
      · left; omega
  · left
    refine ⟨h.le, by omega, by omega⟩

end PMAction.D4Reflection
