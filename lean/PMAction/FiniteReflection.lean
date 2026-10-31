import PMAction.SiteReflection
import Mathlib.MeasureTheory.Constructions.Pi

/-! Reindex a finite, site-reflected link set into plane, upper and reflected
upper links. Product measure factorization is proved, not assumed. The geometric
D₄ model must still supply the edge involution and its support/action identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.FiniteReflection
open MeasureTheory
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev Plane (w : E → ℤ) := {e // w e=0}
abbrev Upper (w : E → ℤ) := {e // 0<w e}

/-- The reflected lower links are indexed by the very same type as upper links. -/
def splitIndex (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (_hfix : ∀ e, w e=0 → θ e=e) :
    E ≃ Plane w ⊕ (Upper w ⊕ Upper w) where
  toFun e := if h0 : w e=0 then .inl ⟨e,h0⟩ else
    if hp : 0<w e then .inr (.inl ⟨e,hp⟩) else
      .inr (.inr ⟨θ e,by rw [hw]; omega⟩)
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val (fun e => θ e.1))
  left_inv e := by
    have ht := hθ e
    dsimp
    split_ifs <;> simp_all
  right_inv i := by
    rcases i with p | u | d
    · have hp := p.2
      simp [hp]
    · have hu := u.2
      simp [show w u.1 ≠ 0 by omega,hu]
    · have hd := d.2
      have hneg : w (θ d.1)<0 := by rw [hw]; omega
      have ht := hθ d.1
      simp [show w (θ d.1) ≠ 0 by omega,show ¬0<w (θ d.1) by omega,ht]

variable {G : Type*} [MeasurableSpace G]

/-- A genuine measurable equivalence of the shared-link configuration spaces. -/
def split (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (hfix : ∀ e, w e=0 → θ e=e) :
    (E → G) ≃ᵐ (Plane w → G) × ((Upper w → G) × (Upper w → G)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) (splitIndex θ hθ w hw hfix)).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Upper w ⊕ Upper w => G))))

omit [Fintype E] [DecidableEq E] in
lemma split_apply (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (hfix : ∀ e, w e=0 → θ e=e) (ω : E → G) :
    split θ hθ w hw hfix ω =
      ((fun p : Plane w => ω p.1),((fun u : Upper w => ω u.1),(fun u : Upper w => ω (θ u.1)))) := by
  let e := splitIndex θ hθ w hw hfix
  have hc (i : Plane w ⊕ (Upper w ⊕ Upper w)) :
      (MeasurableEquiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) e ω) i=ω (e.symm i) := by
    change (Equiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) e ω) i=ω (e.symm i)
    rw [Equiv.piCongrLeft_apply]
    simp
  apply Prod.ext
  · funext p
    change (MeasurableEquiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) e ω) (.inl p)=ω p.1
    rw [hc]
    rfl
  · apply Prod.ext
    · funext u
      change (MeasurableEquiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) e ω) (.inr (.inl u))=ω u.1
      rw [hc]
      rfl
    · funext u
      change (MeasurableEquiv.piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G) e ω) (.inr (.inr u))=ω (θ u.1)
      rw [hc]
      rfl

omit [Fintype E] [DecidableEq E] in
/-- Geometric reflection swaps the two half-configurations and fixes the plane. -/
theorem split_reflect (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (hfix : ∀ e, w e=0 → θ e=e) (ω : E → G) :
    split θ hθ w hw hfix (fun e => ω (θ e)) =
      ((split θ hθ w hw hfix ω).1,((split θ hθ w hw hfix ω).2.2,(split θ hθ w hw hfix ω).2.1)) := by
  simp only [split_apply]
  apply Prod.ext
  · funext p
    change ω (θ p.1)=ω p.1
    rw [hfix p.1 p.2]
  · apply Prod.ext
    · rfl
    · funext u
      change ω (θ (θ u.1))=ω u.1
      rw [hθ u.1]

omit [Fintype E] [DecidableEq E] in
/-- Agreement of plane and upper coordinates is exactly the information read
by every nonnegative-height edge. -/
theorem agree_nonnegative (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (hfix : ∀ e, w e=0 → θ e=e) (ω η : E → G)
    (hp : (split θ hθ w hw hfix ω).1=(split θ hθ w hw hfix η).1)
    (hu : (split θ hθ w hw hfix ω).2.1=(split θ hθ w hw hfix η).2.1) :
    ∀ e, 0 ≤ w e → ω e=η e := by
  rw [split_apply,split_apply] at hp hu
  intro e he
  by_cases h0 : w e=0
  · exact congrFun hp ⟨e,h0⟩
  · exact congrFun hu ⟨e,by omega⟩

omit [DecidableEq E] in
/-- The product law on actual links becomes the plane/upper/lower product law.
No independence of triangles is introduced: the indices are shared link indices. -/
theorem measure_preserving (ν : Measure G) [IsProbabilityMeasure ν]
    (θ : E ≃ E) (hθ : Function.Involutive θ) (w : E → ℤ)
    (hw : ∀ e, w (θ e) = -w e) (hfix : ∀ e, w e=0 → θ e=e) :
    MeasurePreserving (split (G := G) θ hθ w hw hfix) (Measure.pi fun _ : E => ν)
      ((Measure.pi fun _ : Plane w => ν).prod
        ((Measure.pi fun _ : Upper w => ν).prod (Measure.pi fun _ : Upper w => ν))) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => ν) (splitIndex θ hθ w hw hfix)
  have h2 := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => G)).symm
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Plane w ⊕ (Upper w ⊕ Upper w) => ν))
  have h3 := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Upper w ⊕ Upper w => G)).symm
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Upper w ⊕ Upper w => ν))
  exact ((MeasurePreserving.id (Measure.pi fun _ : Plane w => ν)).prod h3).comp (h2.comp h1)

end PMAction.FiniteReflection
