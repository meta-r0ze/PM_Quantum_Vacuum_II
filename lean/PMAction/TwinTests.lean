import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# What persists: keep, reinterpret, or gap the walk's twins?

* **Reinterpret as physical channels** (`twin_anticommutes`). For any one-coin nearest-
  neighbour update — any site matrix `M` and arbitrary link factors on both hops — the twin
  map `ψ_x ↦ (−1)^x ψ_x` turns solutions into solutions up to a global sign per tick. The
  twin therefore couples identically to every gauge background: one lattice field cannot
  supply channels with different charges, such as a generation's mixed hypercharges.
* **Gap the twins** (`Wp_trace`, `Wp_det`, `light_point`, `twin_point`). Stream channel 0,
  mix, stream channel 1, mix. Each channel still hops once per tick; the extra cost is one
  site-local mixing. With `a = μ − r`, `b = r` the `k = 0` species has gap `μ`, while the
  would-be twin at `k = π` has `tr = −2 cos(2r − μ)`: quasi-energy `π ± (2r − μ)`, heavy for
  `r` of order one. This is a unitary, local analogue of a Wilson term.
-/

noncomputable section
namespace PMAction.TwinTests
open Matrix Complex

/-! ## Test of "twins are physical channels": they carry identical charge -/

/-- A one-coin nearest-neighbour update in an arbitrary background: any site matrix `M`,
arbitrary link factors `L x`, `R x` on the two hops. -/
def gaugedStep (M : Matrix (Fin 2) (Fin 2) ℂ) (L R : ℤ → ℂ) (ψ : ℤ → Fin 2 → ℂ) :
    ℤ → Fin 2 → ℂ := fun x =>
  ![L x * (M *ᵥ ψ (x - 1)) 0, R x * (M *ᵥ ψ (x + 1)) 1]

/-- The twin map `ψ_x ↦ (−1)^x ψ_x`. -/
def twin (ψ : ℤ → Fin 2 → ℂ) : ℤ → Fin 2 → ℂ := fun x => ((-1 : ℂ) ^ x) • ψ x

lemma sign_pred (x : ℤ) : (-1 : ℂ) ^ (x - 1) = -((-1 : ℂ) ^ x) := by
  rw [zpow_sub₀ (by norm_num), zpow_one]; ring
lemma sign_succ (x : ℤ) : (-1 : ℂ) ^ (x + 1) = -((-1 : ℂ) ^ x) := by
  rw [zpow_add₀ (by norm_num), zpow_one]; ring

/-- In every background, the twin of a solution is a solution up to the global sign `−1`
per tick: twins couple identically to every link field, so they share every charge. -/
theorem twin_anticommutes (M : Matrix (Fin 2) (Fin 2) ℂ) (L R : ℤ → ℂ)
    (ψ : ℤ → Fin 2 → ℂ) :
    gaugedStep M L R (twin ψ) = -twin (gaugedStep M L R ψ) := by
  funext x i
  fin_cases i <;> simp [gaugedStep, twin, Matrix.mulVec_neg, Matrix.mulVec_smul, sign_pred, sign_succ] <;> ring

/-! ## Test of "gap the twins": a two-coin update with partial streams -/

def C (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Stream channel 0 right, mix, stream channel 1 left, mix. Each channel still hops once
per tick; the extra cost is one site-local mixing. -/
def Wp (a b k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  C b * !![1, 0; 0, exp ((k : ℂ) * I)] * C a * !![exp (-(k : ℂ) * I), 0; 0, 1]

theorem Wp_trace (a b k : ℝ) :
    (Wp a b k).trace =
      2 * (Real.cos a * Real.cos b * Real.cos k - Real.sin a * Real.sin b) := by
  simp [Wp, C, trace_fin_two, Fin.sum_univ_two]
  have hef : cexp ((k:ℂ) * I) * cexp (-((k:ℂ) * I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : cexp ((k:ℂ) * I) + cexp (-((k:ℂ) * I)) = 2 * Complex.cos k := by
    rw [Complex.cos]; ring_nf
  linear_combination (Complex.cos b * Complex.cos a) * h2 +
    (-(Complex.sin b * Complex.sin a)) * hef

theorem Wp_det (a b k : ℝ) : (Wp a b k).det = 1 := by
  have hC : ∀ t : ℝ, (C t).det = 1 := by
    intro t
    simp only [C, det_fin_two_of]
    have : ((Real.cos t : ℂ)) * (Real.cos t : ℂ) - -(Real.sin t : ℂ) * (Real.sin t : ℂ) =
      ((Real.sin t ^ 2 + Real.cos t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Real.sin_sq_add_cos_sq]; simp
  simp only [Wp, det_mul, hC, det_fin_two_of]
  simp only [one_mul, mul_one, mul_zero, sub_zero]
  rw [← Complex.exp_add]; simp

/-- Wilson-like tuning `a = μ − r`, `b = r`: the `k = 0` species has gap `μ` while the
would-be twin at `k = π` sits at quasi-energy `π ± (2r − μ)`. -/
theorem light_point (μ r : ℝ) : (Wp (μ - r) r 0).trace = 2 * Real.cos μ := by
  have h : Real.cos (μ - r) * Real.cos r - Real.sin (μ - r) * Real.sin r = Real.cos μ := by
    rw [← Real.cos_add]; ring_nf
  rw [Wp_trace, Real.cos_zero, ← h]; push_cast; ring

theorem twin_point (μ r : ℝ) :
    (Wp (μ - r) r Real.pi).trace = -2 * Real.cos (2*r - μ) := by
  have h : Real.cos r * Real.cos (μ - r) + Real.sin r * Real.sin (μ - r) =
      Real.cos (2*r - μ) := by
    rw [← Real.cos_sub]; ring_nf
  rw [Wp_trace, Real.cos_pi, ← h]; push_cast; ring

end PMAction.TwinTests
