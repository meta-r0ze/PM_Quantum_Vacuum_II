import Mathlib.Analysis.Complex.Circle

/-!
# Protocol: no global phase reference forces a connection

Under Closure there is no global phase reference: each node's phase frame can be rotated
independently, `ψₓ ↦ gₓ ψₓ` with `|gₓ| = 1`. A transport term between neighbours is
`conj(ψₓ) u ψᵧ`.

* `fixed_transport_vanishes`: if a fixed coefficient `u` makes the term invariant under all
  independent local rotations, then `u = 0` — no information is transported.
* `connection_transport_invariant`: if instead `u` is a link variable that transforms as
  `u ↦ gₓ u conj(gᵧ)`, the term is invariant for every local rotation.

So transport without a global reference requires a link variable with this transformation law: a
connection (`Gauge.plaquette_covariant` then gives the loop observables).
-/

namespace PMAction.Protocol
open Complex ComplexConjugate

theorem fixed_transport_vanishes (u : ℂ)
    (h : ∀ gx gy : ℂ, ‖gx‖ = 1 → ‖gy‖ = 1 → ∀ ψx ψy : ℂ,
      conj (gx * ψx) * u * (gy * ψy) = conj ψx * u * ψy) : u = 0 := by
  have := h 1 (-1) (by simp) (by simp) 1 1
  simp at this
  linear_combination (-1 / 2 : ℂ) * this

theorem connection_transport_invariant (gx gy u ψx ψy : ℂ) (hx : ‖gx‖ = 1) (hy : ‖gy‖ = 1) :
    conj (gx * ψx) * (gx * u * conj gy) * (gy * ψy) = conj ψx * u * ψy := by
  have hx' : conj gx * gx = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hx]; simp
  have hy' : conj gy * gy = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hy]; simp
  simp only [map_mul]
  linear_combination (conj ψx * u * ψy) * ((conj gy * gy) * hx' + hy')
end PMAction.Protocol
