import PMAction.WeakField

/-!
# The spatial metric from the directional link response

Paper II §7 supplies only the time–time readout. The spatial part is a **directional**
response: along axis `j` the link has the local index `n_j = ν/(ν−K_j)` and clock speed
`c_j = (ν−K_j)/ν`, so the optical spatial metric is diagonal, `g_ij = n_j² δ_ij` (equal
to `δ_ij / c_j²`). This module derives:

* `spatialMetric` — the diagonal metric from the same capacity ledger as `WeakField`.
* `spatialMetric_diagonal`, `spatialMetric_self` — it is diagonal with the directional
  index squared.
* `spatialMetric_from_index` — `g_ij = n_i² δ_ij`, using `n = 1/c_loc`.
* `spatialMetric_isotropic` — if the load is axis-independent, the spatial metric is
  proportional to the identity. Isotropy is a *consequence of an axis-independent
  substrate load*, not an assumption.

The identification of `g_ij = n_j² δ_ij` as the physical spatial metric is the proposed
optical-metric reading; the off-diagonal/cross-axis response (shear) is not derived.
-/

noncomputable section
namespace PMAction.SpatialResponse
open PMAction.WeakField

/-- Directional optical spatial metric from the capacity ledger: `g_ij = δ_ij / c_i²`. -/
def spatialMetric (nu : ℝ) (K : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = j then 1 / (clockSpeed nu (K i)) ^ 2 else 0

theorem spatialMetric_diagonal (nu : ℝ) (K : Fin 3 → ℝ) (i j : Fin 3) (h : i ≠ j) :
    spatialMetric nu K i j = 0 := by
  simp [spatialMetric, h]

theorem spatialMetric_self (nu : ℝ) (K : Fin 3 → ℝ) (i : Fin 3) :
    spatialMetric nu K i i = 1 / (clockSpeed nu (K i)) ^ 2 := by
  simp [spatialMetric]

/-- The local index is the reciprocal clock speed, so `g_ij = n_i² δ_ij`. -/
theorem localIndex_eq_inv_clock (nu K : ℝ) (hnu : nu ≠ 0) (h : nu - K ≠ 0) :
    localIndex nu K = 1 / clockSpeed nu K := by
  unfold localIndex clockSpeed
  field_simp

theorem spatialMetric_from_index (nu : ℝ) (K : Fin 3 → ℝ) (hnu : nu ≠ 0)
    (h : ∀ j, nu - K j ≠ 0) (i j : Fin 3) :
    spatialMetric nu K i j = if i = j then (localIndex nu (K i)) ^ 2 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [spatialMetric_self, ite_eq_left rfl, localIndex_eq_inv_clock nu (K i) hnu (h i)]
    ring
  · simp [spatialMetric, hij]

/-- **Isotropy from an axis-independent load.** If every axis has the same load `c`, the
spatial metric is proportional to the identity — the substrate's cubic symmetry at
equal directional load, not an assumed isotropic metric. -/
theorem spatialMetric_isotropic (nu : ℝ) (c : ℝ) (K : Fin 3 → ℝ)
    (hK : ∀ j, K j = c) (i j : Fin 3) :
    spatialMetric nu K i j = (if i = j then 1 / (clockSpeed nu c) ^ 2 else 0) := by
  by_cases hij : i = j
  · subst hij; simp [spatialMetric, hK]
  · simp [spatialMetric, hij]

end PMAction.SpatialResponse
