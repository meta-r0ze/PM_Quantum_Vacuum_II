import Mathlib.Tactic

/-!
# One-loop running coefficients

The one-loop coefficient `b₀` in `μ dα⁻¹/dμ = b₀/(2π)` is a property of the gauge dynamics, so it is
stated here with the action and consumed by Paper III's running tests.

**Spin decomposition (Nielsen–Hughes).** A species of spin `s` contributes
`(-1)^{2s} ((2s)² - 1/3)` per unit of its group index: `(2s)²` is the spin (paramagnetic) response
and `1/3` the orbital (diamagnetic) one, and the sign is the statistics.

* `spin_terms`: vector `11/3`, Weyl fermion `-2/3`, complex scalar `-1/3`.
* `b0_formula`: with `C_A = N` for the gauge field and index `1/2` for fundamental matter,
  `b₀ = (11/3)N - (2/3)n_f - (1/6)n_s` (`n_f` Dirac flavours, `n_s` complex scalars).
* `qcd_values`: for `SU(3)` with no scalars, `b₀ = 9, 25/3, 23/3, 7` at `3, 4, 5, 6` flavours.
* `gauge_part`: the gauge contribution is `(11/3) C_A`; `11` for colour and `22/3` for `SU(2)`.
* `asymptotic_freedom_iff`: `SU(3)` with Dirac flavours only has `b₀ > 0` iff `n_f ≤ 16`.
* `bContent`, `bContent_formula`: the same rule for arbitrary content, given the gauge index and the
  summed Weyl and complex-scalar indices; `b0_eq_content` recovers `b0`.

Open (substrate): the two inputs of the decomposition, the spin response `(2s)²` and the orbital
`1/3`, are the standard continuum results; deriving them from the substrate's response is not done
here. A natural target is the `1/3` as an average over the three spatial directions.
-/

namespace PMAction.RunningCoefficients

/-- The contribution of a species with `2s = twoS`, per unit group index. -/
def spinTerm (twoS : ℕ) : ℚ := (-1) ^ twoS * ((twoS : ℚ) ^ 2 - 1/3)

theorem spin_terms : spinTerm 2 = 11/3 ∧ spinTerm 1 = -2/3 ∧ spinTerm 0 = -1/3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [spinTerm]

/-- `SU(N)` with `nf` Dirac flavours (two Weyl each) and `ns` complex scalars, fundamental. -/
def b0 (N nf ns : ℕ) : ℚ := spinTerm 2 * N + spinTerm 1 * (2 * nf) * (1/2) + spinTerm 0 * ns * (1/2)

theorem b0_formula (N nf ns : ℕ) : b0 N nf ns = 11/3 * N - 2/3 * nf - 1/6 * ns := by
  simp only [b0, spin_terms]; ring

theorem qcd_values : b0 3 3 0 = 9 ∧ b0 3 4 0 = 25/3 ∧ b0 3 5 0 = 23/3 ∧ b0 3 6 0 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [b0_formula] <;> norm_num

theorem gauge_part (cA : ℚ) : spinTerm 2 * cA = 11/3 * cA := by rw [spin_terms.1]

theorem asymptotic_freedom_iff (nf : ℕ) : 0 < b0 3 nf 0 ↔ nf ≤ 16 := by
  rw [b0_formula]
  constructor
  · intro h; by_contra hc; push Not at hc
    have : (17 : ℚ) ≤ nf := by exact_mod_cast hc
    norm_num at h; linarith
  · intro h
    have : (nf : ℚ) ≤ 16 := by exact_mod_cast h
    norm_num; linarith

/-- The coefficient for any content: gauge index `cA`, total Weyl index `weyl` and total
complex-scalar index `scalar`. -/
def bContent (cA weyl scalar : ℚ) : ℚ := spinTerm 2 * cA + spinTerm 1 * weyl + spinTerm 0 * scalar

theorem bContent_formula (cA weyl scalar : ℚ) :
    bContent cA weyl scalar = 11/3 * cA - 2/3 * weyl - 1/3 * scalar := by
  simp only [bContent, spin_terms]; ring

theorem b0_eq_content (N nf ns : ℕ) : b0 N nf ns = bContent N nf (ns / 2) := by
  rw [b0_formula, bContent_formula]; ring

end PMAction.RunningCoefficients
