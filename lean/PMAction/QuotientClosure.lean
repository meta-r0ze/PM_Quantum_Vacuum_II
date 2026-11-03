import PMAction.GeometricGauge
import Mathlib.MeasureTheory.Measure.Map

/-!
# Closure of gauge invariance under arbitrary edge-identification quotients

`GaugeInvariance` and `GeometricGauge` prove gauge invariance on the full geometric
edge space; `ReciprocalLinks`/`ReciprocalReflection` prove it for the reciprocal
orientation. The one case the audit marked as *not covered* is an arbitrary
edge-identification quotient. It is closed by a general pushforward fact: a
gauge-invariant law descends along **any** measurable quotient map that intertwines
the gauge action.

* `map_invariant_of_intertwining`: if `f` preserves `μ` and `π ∘ f = fQ ∘ π`, then
  `(μ.map π).map fQ = μ.map π`. A concrete quotient only has to supply `π` and the
  induced `fQ`; invariance follows automatically.
* `gibbs_quotient_invariant`: applied to the actual geometric gauge action and
  Gibbs law, so any edge-identification quotient with an induced action inherits
  gauge invariance.

This does not assert that a specific quotient is physically admissible; it removes
the need to re-prove invariance for each one.
-/

noncomputable section
namespace PMAction.QuotientClosure
open MeasureTheory

/-- **Pushforward closure of invariance.** -/
theorem map_invariant_of_intertwining {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    {μ : Measure Ω} {f : Ω → Ω} {fQ : Q → Q} (hf : MeasurePreserving f μ μ)
    (π : Ω → Q) (hπ : Measurable π) (hfQ : Measurable fQ)
    (hint : ∀ x, π (f x) = fQ (π x)) :
    (μ.map π).map fQ = μ.map π := by
  rw [Measure.map_map hfQ hπ]
  have hcomp : fQ ∘ π = π ∘ f := funext fun x => (hint x).symm
  rw [hcomp, ← Measure.map_map hπ hf.measurable, hf.map_eq]

/-- **Gauge invariance of any edge-identification quotient Gibbs law.** For the
geometric gauge action `act g` and any measurable quotient `π` with induced action
`fQ` satisfying `π (act g ω) = fQ (π ω)`, the pushed-forward geometric Gibbs law is
`fQ`-invariant. -/
theorem gibbs_quotient_invariant {N : ℕ} {X : Finset FiniteD4Reflection.Vertex}
    (g : FiniteD4Reflection.Vertex → GeometricGauge.G N) (β : ℝ)
    {Q : Type*} [MeasurableSpace Q] (π : GeometricGauge.Config N X → Q)
    (hπ : Measurable π) (fQ : Q → Q) (hfQ : Measurable fQ)
    (hint : ∀ ω, π (GeometricGauge.act g ω) = fQ (π ω)) :
    (Measure.map π (LatticeGibbs.gibbs
        (Measure.pi fun _ : FiniteD4Reflection.Edge X => UnitaryHaar.haar N) β
        (FiniteD4Reflection.action X))).map fQ
      = Measure.map π (LatticeGibbs.gibbs
        (Measure.pi fun _ : FiniteD4Reflection.Edge X => UnitaryHaar.haar N) β
        (FiniteD4Reflection.action X)) :=
  map_invariant_of_intertwining (GeometricGauge.gibbs_preserving g β) π hπ hfQ hint

end PMAction.QuotientClosure
