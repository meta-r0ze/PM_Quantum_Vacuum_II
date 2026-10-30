import PMAction.ReferenceSampling

/-!
# Summed reference reads in the event-priced D₄ action

`ReferenceSampling` prices a refresh by the *mean* flag over its `r` reference states (one
sampled read). If instead every reference state is read at each refresh, the flags add.
This is the summed read.

* `sum_flag`: the summed flag is `r` times the mean flag, i.e. `Re tr(Eᴴ(1 − P)E)/2`.
* `sum_density_eq`: the summed-read density is `r` times the mean-read density.
* `sum_limit`: for cubically consistent links of a `C^{1,1}` `u(N)` connection it converges to
  `(toll·m·W/4) Σ_{μν} ‖F_{μν} E‖²_F`. The multiplicity `r` of the reference drops out.
* `sum_canonical_iff`: with `‖F E‖²_F = κ_R g² Σ (F^a)²`, the limit is the canonical
  Yang–Mills density exactly when `g² = 1/(κ_R·toll·m·W)`.

Which read (mean or summed) a sector performs is a premise of the readout contract.
-/

noncomputable section
namespace PMAction.SummedReference
open Matrix VaryingFields LinkConsistency CommonResponse ReferenceSampling
open scoped Matrix.Norms.L2Operator

variable {N r : ℕ}

/-- Summed readout flag over the reference states. -/
def sumFlag (E : Matrix (Fin N) (Fin r) ℂ) (P : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ k, stateFlag P (fun i => E i k)

theorem sum_flag (E : Matrix (Fin N) (Fin r) ℂ) (P : Matrix (Fin N) (Fin N) ℂ) :
    sumFlag E P = r * refFlag E P := by
  unfold sumFlag refFlag
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · have : (r : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

theorem sum_flag_trace (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (hr : 0 < r) :
    sumFlag E P = (trace (Eᴴ * (1 - P) * E)).re / 2 := by
  rw [sum_flag, ref_flag E hE P hP]
  have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/-- Summed-read event-priced D₄ density. -/
def sumDensity (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (toll : ℝ) (m : ℕ) (W h : ℝ) : ℝ :=
  (1 / 12) * ∑ p ∈ D4Gauge.tri,
    W * responseCost toll m (sumFlag E (holonomy U x (rv p.1) (rv p.2) h)) / h ^ 4

theorem sum_density_eq (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (toll : ℝ) (m : ℕ) (W h : ℝ) :
    sumDensity U x E toll m W h = r * refDensity U x E toll m W h := by
  unfold sumDensity refDensity
  simp only [sum_flag, responseCost, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Summed-read continuum limit.** -/
theorem sum_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (hr : 0 < r) (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => sumDensity U x E toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / 4) *
        ∑ μ, ∑ ν, ∑ i, ∑ k,
          ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)) := by
  have h := (ref_limit hA hL0 hL hskew U hU hK hc E hE toll m W).const_mul (r : ℝ)
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : (r : ℝ) * (toll * m * W / (2 * r) / 2) = toll * m * W / 4 := by
    field_simp; ring
  simp only [← mul_assoc, e] at h
  simpa only [sum_density_eq] using h

/-- **Canonical normalization for a summed-read sector.** -/
theorem sum_canonical_iff {toll κ W g : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m)
    (hκ : 0 < κ) (hW : 0 < W) (hg : g ≠ 0) :
    (toll * m * W / 4) * (κ * g ^ 2) = 1 / 4 ↔ g ^ 2 = 1 / (κ * toll * m * W) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hg2 : 0 < g ^ 2 := by positivity
  constructor
  · intro h; field_simp; field_simp at h; linarith
  · intro h; rw [h]; field_simp

end PMAction.SummedReference
