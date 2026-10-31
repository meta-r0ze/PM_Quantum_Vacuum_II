import PMAction.TransportExistence
import PMAction.GaugeTransport

/-! Operational refinement bridge: a single-hop update family that composes
exactly under subdivision and has a differentiable infinitesimal response obeys
the transport ODE. Conservation forces that response to be skew-Hermitian.
These are conditional tests for a microscopic implementation, not a selection of
that implementation or a claim that causality alone supplies subdivision. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.CompositionalTransport
open Matrix GaugeTransport Filter Topology
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}
abbrev V := Fin 4 → ℝ
local notation "M" => Matrix (Fin N) (Fin N) ℂ

/-- Exact straight-edge subdivision of a link family. -/
def Composes (U : V → V → ℝ → M) : Prop :=
  ∀ y v s t, U y v (s+t)=U y v s*U (y+s • v) v t

/-- Composition plus the response at zero length determines the differential law
at every length. The ODE is a conclusion, not a premise. -/
theorem ode_of_composes {U : V → V → ℝ → M} {A : V → V →L[ℝ] M}
    (hcomp : Composes U) (hgen : ∀ y v, HasDerivAt (U y v) (A y v) 0) :
    ∀ y v s, HasDerivAt (U y v) (U y v s*A (y+s • v) v) s := by
  unfold Composes at hcomp
  intro y v s
  have hd := (hgen (y+s • v) v).const_mul (U y v s)
  have hh : HasDerivAt (fun t => U y v (s+t)) (U y v s*A (y+s • v) v) 0 := by
    simpa only [← hcomp] using hd
  have hh' : HasDerivAt (fun t => U y v (s+t)) (U y v s*A (y+s • v) v) (s-s) := by
    simpa only [sub_self] using hh
  simpa only [add_sub_cancel] using hh'.comp_sub_const s s

/-- Infinitesimal norm conservation forces skew-Hermiticity. -/
theorem skew_of_unitary_tangent {U : ℝ → M} {A : M} (h0 : U 0=1)
    (hu : ∀ t, U t ∈ unitary M) (hd : HasDerivAt U A 0) : star A = -A := by
  have hh := hd.mul hd.star
  have he : (fun t => U t*star (U t)) = fun _ => (1:M) :=
    funext fun t => (Unitary.mem_iff.mp (hu t)).2
  change HasDerivAt (fun t => U t*star (U t)) (A*star (U 0)+U 0*star A) 0 at hh
  rw [he] at hh
  have hz := hh.unique (hasDerivAt_const 0 (1:M))
  simp only [h0,star_one,mul_one,one_mul] at hz
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hz

/-- Links extracted from compositional updates themselves compose. -/
theorem extract_composes (S : ∀ (v : V) (h : ℝ), HopUpdate N v h)
    (hcomp : ∀ v s t ψ, (S v (s+t)).T ψ=(S v s).T ((S v t).T ψ)) :
    Composes (fun y v h => extract (S v h) y) := by
  intro y v s t
  refine (extract_unique (S v (s+t))
    (fun z => extract (S v s) z*extract (S v t) (z+s • v)) ?_ y).symm
  intro ψ z
  rw [hcomp,extract_spec,extract_spec,← mulVec_mulVec]
  have he : z+s • v+t • v=z+(s+t) • v := by module
  rw [he]

/-- For a conserving update family, exact subdivision and a C² infinitesimal
response suffice for the classical Yang–Mills site-action limit of its own links.
The theorem does not assume a transport solution, unitarity, skewness or cubic
consistency. Native E8 realization and the subdivision/refinement hypotheses
still require independent justification. -/
theorem update_to_yang_mills_c2
    (S : ∀ (v : V) (h : ℝ), HopUpdate N v h)
    (hcon : ∀ v h, Conserving (S v h))
    (h0 : ∀ y v, extract (S v 0) y=1)
    (hcomp : ∀ v s t ψ, (S v (s+t)).T ψ=(S v s).T ((S v t).T ψ))
    (A : V → V →L[ℝ] M) (hA : ContDiff ℝ 2 A)
    (hgen : ∀ y v, HasDerivAt (fun h => extract (S v h) y) (A y v) 0)
    {R : Set V} (hRb : Bornology.IsBounded R) (hRm : MeasurableSet R)
    (hRf : MeasureTheory.volume (frontier R)=0) (β : ℝ) :
    Tendsto (fun n => LatticeSiteAction.siteAction (fun y v h => extract (S v h) y) β R n) atTop
      (𝓝 (∫ y in R, UniformGaugeAction.yangMillsDensity A (fderiv ℝ A) y β)) := by
  have hskew (y v : V) : star (A y v) = -A y v :=
    skew_of_unitary_tangent (h0 y v) (fun h => extract_unitary (S v h) (hcon v h) y) (hgen y v)
  exact ConnectionRegularity.d4_yang_mills_action_c2 hRb hRm hRf hA hskew
    (fun y v h => extract (S v h) y) h0 (ode_of_composes (extract_composes S hcomp) hgen) β

/-- The same operational contracts also force reciprocal extracted links. -/
theorem update_reciprocal (S : ∀ (v : V) (h : ℝ), HopUpdate N v h)
    (hcon : ∀ v h, Conserving (S v h)) (h0 : ∀ y v, extract (S v 0) y=1)
    (hcomp : ∀ v s t ψ, (S v (s+t)).T ψ=(S v s).T ((S v t).T ψ))
    (A : V → V →L[ℝ] M)
    (hgen : ∀ y v, HasDerivAt (fun h => extract (S v h) y) (A y v) 0)
    (y v : V) (h : ℝ) : extract (S (-v) h) (y+h • v)=star (extract (S v h) y) := by
  have hskew (z w : V) : star (A z w) = -A z w :=
    skew_of_unitary_tangent (h0 z w) (fun t => extract_unitary (S w t) (hcon w t) z) (hgen z w)
  exact TransportExistence.connection_reciprocal hskew (fun z w t => extract (S w t) z)
    h0 (ode_of_composes (extract_composes S hcomp) hgen)
    (fun z w t => extract_unitary (S w t) (hcon w t) z) y v h

/-! The implemented single-hop premises do not supply exact refinement. This is
an abstract-hop countermodel, not a countermodel to every PM postulate or to a
specific native E8 implementation. -/

def jumpLinks (y v : V) (h : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  if h=0 then 1 else LinkConsistency.flipLinks y v h

lemma jump_unitary (y v : V) (h : ℝ) : jumpLinks y v h ∈ unitary _ := by
  by_cases hh : h=0
  · simp only [jumpLinks,ite_eq_left hh]
    exact (unitary _).one_mem
  · simpa only [jumpLinks,ite_eq_right hh] using LinkConsistency.flip_unitary y v h

lemma jump_reciprocal (y v : V) (h : ℝ) :
    jumpLinks (y+h • v) (-v) h=star (jumpLinks y v h) := by
  by_cases hh : h=0 <;> simp [jumpLinks,LinkConsistency.flipLinks,hh]

lemma jump_not_composes : ¬Composes jumpLinks := by
  intro hc
  have he := congrArg (fun Z : Matrix (Fin 1) (Fin 1) ℂ => Z 0 0)
    (hc 0 0 1 1)
  norm_num [jumpLinks,LinkConsistency.flipLinks] at he

/-- Local conservation, identity at zero length and reciprocal links still do
not force subdivision consistency in the existing abstract hop model. -/
theorem refinement_is_extra :
    ∃ S : ∀ (v : V) (h : ℝ), HopUpdate 1 v h,
      (∀ v h, Conserving (S v h)) ∧
      (∀ y v, extract (S v 0) y=1) ∧
      ¬Composes (fun y v h => extract (S v h) y) := by
  let S := fun (v : V) (h : ℝ) => ofLinks v h (fun y => jumpLinks y v h)
  have he (y v : V) (h : ℝ) : extract (S v h) y=jumpLinks y v h := ofLinks_extract _ _
  refine ⟨S,fun v h => ofLinks_conserving _ (fun y => jump_unitary y v h),?_,?_⟩
  · intro y v
    simp [he,jumpLinks]
  · simpa only [he] using jump_not_composes

end PMAction.CompositionalTransport
