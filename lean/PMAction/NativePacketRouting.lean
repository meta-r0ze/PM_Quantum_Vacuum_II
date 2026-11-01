import PMAction.NativePacketLinks
import PMAction.CompositionalTransport

/-! Finite native packet routing. Internal controls are actual carrier root
words, not arbitrary unitary matrices. Spatial routing is the supplied neighbour
permutation. The four coordinate-odd amplitudes are a packet subsystem, not an
additional payload index independent of the existing vacuum spinor coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NativePacketRouting
open Matrix CarrierEvents CarrierParity NativePacketLinks
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Row-to-input lookup of one native packet hop. -/
def lookup (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c) : Equiv.Perm (X × Carrier c) where
  toFun q := (e q.1,((p q.1 : Equiv.Perm (Carrier c))⁻¹) q.2)
  invFun q := (e⁻¹ q.1,(p (e⁻¹ q.1) : Equiv.Perm (Carrier c)) q.2)
  left_inv q := by rcases q with ⟨x,v⟩; simp
  right_inv q := by rcases q with ⟨x,v⟩; simp

def update (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c) := (lookup c e p).permMatrix ℂ

def field (c : Fin 3) (ψ : X → Fin 4 → ℂ) : X × Carrier c → ℂ :=
  fun q => (embedding c *ᵥ ψ q.1) q.2

def readout (c : Fin 3) (ψ : X × Carrier c → ℂ) : X → Fin 4 → ℂ :=
  fun x => (embedding c)ᴴ *ᵥ (fun v => ψ (x,v))

/-- The state count is exactly the old finite carrier array size. -/
theorem register_count (c : Fin 3) (A : Type*) [Fintype A] :
    Fintype.card (X × Carrier c → A)=(Fintype.card A)^(8*Fintype.card X) := by
  simp [carrier_card,mul_comm]

omit [DecidableEq X] in
/-- Every additive register-content observation is conserved. -/
theorem registers_conserved (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c)
    {A B : Type*} [AddCommMonoid B] (s : X × Carrier c → A) (f : A → B) :
    (∑ q, f (s (lookup c e p q)))=∑ q, f (s q) := Equiv.sum_comp (lookup c e p) (fun q => f (s q))

omit [Fintype X] [DecidableEq X] in
/-- Only the designated source site is read. -/
theorem single_source (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c) (x : X) (v : Carrier c) :
    (lookup c e p (x,v)).1=e x := rfl

/-- The packet transport law follows from the native label permutation. -/
theorem field_step (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c) (ψ : X → Fin 4 → ℂ) :
    update c e p *ᵥ field c ψ = field c (GaugeRecordLinks.transport e (fun x => link c (p x)) ψ) := by
  rw [update,permMatrix_mulVec]
  ext ⟨x,v⟩
  change (embedding c *ᵥ ψ (e x)) (((p x : Equiv.Perm (Carrier c))⁻¹) v)=
    (embedding c *ᵥ (link c (p x) *ᵥ ψ (e x))) v
  have hh := congrFun (packet_step c (p x) (ψ (e x))) v
  simpa only [physical,permMatrix_mulVec,Function.comp_apply] using hh

/-- No unobserved carrier amplitude feeds the packet readout. -/
theorem readout_step (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c)
    (ψ : X × Carrier c → ℂ) :
    readout c (update c e p *ᵥ ψ)=
      GaugeRecordLinks.transport e (fun x => link c (p x)) (readout c ψ) := by
  funext x
  have hh := NativePacketLinks.readout_step c (p x) (fun v => ψ (e x,v))
  simpa only [readout,update,permMatrix_mulVec,lookup,Equiv.coe_fn_mk,
    GaugeRecordLinks.transport,physical,Function.comp_def] using hh

omit [Fintype X] [DecidableEq X] in
lemma recover (c : Fin 3) (ψ : X → Fin 4 → ℂ) : readout c (field c ψ)=ψ := by
  funext x
  exact CarrierParity.recover c (ψ x)

/-- Composition on the native finite state space agrees with extracted links. -/
theorem update_compose (c : Fin 3) (e f : Equiv.Perm X) (p q : X → Action c) :
    update c e p * update c f q=
      update c (e.trans f) (fun x => p x*q (e x)) := by
  unfold update
  rw [← permMatrix_mul]
  congr 1
  apply Equiv.ext
  rintro ⟨x,v⟩
  simp [lookup,Equiv.Perm.mul_apply]

omit [DecidableEq X] in
theorem packet_population (c : Fin 3) (e : Equiv.Perm X) (p : X → Action c) (ψ : X → Fin 4 → ℂ) :
    (∑ x, CommonResponse.nsq (GaugeRecordLinks.transport e (fun x => link c (p x)) ψ x))=
      ∑ x, CommonResponse.nsq (ψ x) :=
  GaugeRecordLinks.population_preserved e _ (fun x => link_unitary c (p x)) ψ

/-- A smooth all-real refinement confined to root-word links on this fixed
packet is necessarily the identity. Word composition is genuinely discrete. -/
theorem pure_permutation_refinement_trivial (c : Fin 3)
    (U : CompositionalTransport.V → CompositionalTransport.V → ℝ → Matrix (Fin 4) (Fin 4) ℂ)
    (hnative : ∀ y v h, U y v h ∈ Set.range (link c))
    (h0 : ∀ y v, U y v 0=1) (hcomp : CompositionalTransport.Composes U)
    (A : CompositionalTransport.V → CompositionalTransport.V →L[ℝ] Matrix (Fin 4) (Fin 4) ℂ)
    (hgen : ∀ y v, HasDerivAt (U y v) (A y v) 0) : ∀ y v h, U y v h=1 := by
  have hd := CompositionalTransport.ode_of_composes hcomp hgen
  intro y v h
  have hc : Continuous (U y v) := continuous_iff_continuousAt.mpr fun t => (hd y v t).continuousAt
  exact (continuous_native_constant c (U y v) hc (hnative y v) h 0).trans (h0 y v)

end PMAction.NativePacketRouting
