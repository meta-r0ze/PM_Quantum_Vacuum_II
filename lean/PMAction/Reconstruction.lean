import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# What persists: survival weights carry a unitary quantum evolution

A persistent closed system is described by survival weights `T x y ≥ 0` for one tick from state
`x` to state `y`, with a stationary distribution `π > 0`.

* **Quiescence** (zero net flux, PM's quiescent steady state): no net flow between any two states,
  `π x T x y = π y T y x` (detailed balance). `quiescent_symmetric`: the symmetrized transfer matrix
  `S x y = √π x · T x y / √π y` is symmetric.
* **Operator hypothesis**: `S` is injective. Injectivity of the statistical transfer
  operator is an additional premise, not proved from bijectivity of a realized update. `two_tick_positive`: the two-tick
  transfer matrix `S²` is positive definite — reflection positivity at two ticks.
* `energies`: then `S² vᵢ = e^{−Eᵢ} vᵢ` in an orthonormal eigenbasis, with real energies
  `Eᵢ = −log λᵢ`: `S² = e^{−H}` for a self-adjoint `H`.
* `phase_evolution_unitary`: evolving amplitudes by `e^{−i Eᵢ t}` preserves `Σ |cᵢ|²` for every
  real `t`.

So survival weights, `e^{−S}`, of a quiescent, distinction-preserving system are the Euclidean
form of a unitary evolution `e^{−iHt}` (the finite-dimensional core of Osterwalder–Schrader
reconstruction), with the tick doubled.

* `bijective_update_unitary`: the realized deterministic update itself is unitary already —
  Conservation (a bijection) preserves `Σ |cᵢ|²` for any amplitudes. Unitarity of the dynamics comes
  from Conservation; the survival weights select among histories and are a separate, statistical
  layer.
-/

noncomputable section
namespace PMAction.Reconstruction
open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Symmetrized transfer matrix. -/
def sym (π : X → ℝ) (T : Matrix X X ℝ) : Matrix X X ℝ :=
  fun x y => Real.sqrt (π x) * T x y / Real.sqrt (π y)

omit [Fintype X] [DecidableEq X] in
/-- **Quiescence gives a symmetric transfer matrix.** -/
theorem quiescent_symmetric (π : X → ℝ) (hπ : ∀ x, 0 < π x) (T : Matrix X X ℝ)
    (hdb : ∀ x y, π x * T x y = π y * T y x) : (sym π T).IsSymm := by
  ext x y
  simp only [transpose_apply, sym]
  have hx := Real.sqrt_pos.mpr (hπ x)
  have hy := Real.sqrt_pos.mpr (hπ y)
  have hx2 := Real.sq_sqrt (hπ x).le
  have hy2 := Real.sq_sqrt (hπ y).le
  rw [div_eq_div_iff hx.ne' hy.ne']
  have e1 : √(π y) * T y x * √(π y) = π y * T y x := by
    rw [show √(π y) * T y x * √(π y) = √(π y) ^ 2 * T y x by ring, hy2]
  have e2 : √(π x) * T x y * √(π x) = π x * T x y := by
    rw [show √(π x) * T x y * √(π x) = √(π x) ^ 2 * T x y by ring, hx2]
  rw [e1, e2]; exact (hdb x y).symm

omit [DecidableEq X] in
/-- **Symmetry and injectivity give positive definiteness at two ticks.** -/
theorem two_tick_positive (S : Matrix X X ℝ) (hS : S.IsSymm)
    (hinj : Function.Injective S.mulVec) : (S * S).PosDef := by
  have h := PosDef.conjTranspose_mul_self S hinj
  rwa [conjTranspose_eq_transpose_of_trivial, hS.eq] at h

/-- **Real energies.** -/
theorem energies (A : Matrix X X ℝ) (hA : A.PosDef) :
    ∃ E : X → ℝ, ∀ i, A *ᵥ ⇑(hA.1.eigenvectorBasis i) =
      Real.exp (-E i) • ⇑(hA.1.eigenvectorBasis i) := by
  refine ⟨fun i => -Real.log (hA.1.eigenvalues i), fun i => ?_⟩
  rw [neg_neg, Real.exp_log (hA.eigenvalues_pos i)]
  exact hA.1.mulVec_eigenvectorBasis i

omit [DecidableEq X] in
/-- **Unitary phase evolution.** -/
theorem phase_evolution_unitary (E : X → ℝ) (t : ℝ) (c : X → ℂ) :
    ∑ i, ‖Complex.exp (-(E i * t : ℝ) * Complex.I) * c i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

omit [DecidableEq X] in
/-- **Conservation alone makes the realized update unitary.** A bijective update `f` (no two
states merged in this finite-state model) moves supplied amplitudes by `c ↦ c ∘ f⁻¹`, which preserves `Σ |c|²`. -/
theorem bijective_update_unitary (f : X ≃ X) (c : X → ℂ) :
    ∑ x, ‖c (f.symm x)‖ ^ 2 = ∑ x, ‖c x‖ ^ 2 :=
  Equiv.sum_comp f.symm (fun x => ‖c x‖ ^ 2)

end PMAction.Reconstruction
