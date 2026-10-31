import PMAction.LatticeSiteAction
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A literal C² interface to the compact-Lipschitz connection hypotheses.
The analytic lemma is elaborated for a generic normed codomain before specializing
it to matrix-valued one-forms, avoiding the nested matrix-norm instance diamond. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ConnectionRegularity
open Set

/-- C² supplies the derivative, its continuity, and its Lipschitz bound on every
compact set. No global derivative bound is required. -/
theorem c2_data {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧ Continuous (fderiv ℝ f) ∧
    ∀ S : Set E, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x-y‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  refine ⟨fun x => (hf.differentiable (by norm_num) x).hasFDerivAt, hd.continuous, ?_⟩
  intro S hS
  obtain ⟨K,hK⟩ := hd.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  refine ⟨K, K.2, fun x hx y hy => ?_⟩
  simpa only [dist_eq_norm] using hK.dist_le_mul x hx y hy

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
abbrev V := Fin 4 → ℝ

/-- The existing site-action limit with a literal C² hypothesis. Transport is
still an explicit input here; its existence is supplied separately. -/
theorem d4_yang_mills_action_c2 {N : ℕ}
    {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ} {S : Set V}
    (hSb : Bornology.IsBounded S) (hSm : MeasurableSet S)
    (hSf : MeasureTheory.volume (frontier S) = 0) (hA : ContDiff ℝ 2 A)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y+s • v) v) s) (β : ℝ) :
    Tendsto (fun n => LatticeSiteAction.siteAction T β S n) atTop
      (𝓝 (∫ y in S, UniformGaugeAction.yangMillsDensity A (fderiv ℝ A) y β)) := by
  obtain ⟨hd,hc,hL⟩ := c2_data hA
  exact LatticeSiteAction.d4_yang_mills_action hSb hSm hSf hd hc hL hskew T hT0 hTd β

end PMAction.ConnectionRegularity
