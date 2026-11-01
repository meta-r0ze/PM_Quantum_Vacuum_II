import PMAction.NativeCoherentLinks
import PMAction.CompositionalTransport

/-!
# The native E8 packet subsystem satisfies the operational transport contracts

`CompositionalTransport.update_to_yang_mills_c2` reduces the classical Yang–Mills limit of an
update family to four contracts: conservation, identity at zero length, exact composition under
straight-edge subdivision, and a C² infinitesimal response. `refinement_is_extra` shows that
conservation alone does not supply subdivision. Here those contracts are proved for the native
packet subsystem of `NativeCoherentLinks`: the four-coordinate odd sector of the actual eight
D₄ carrier labels (restrictions of certified E8 reflections), evolved coherently by the native
root-response cost operators weighted by smooth control one-forms.

* `transport_cocycle`: on any finite label type, transports of a skew connection compose along
  an edge, `T y v (s+t) = T y v s · T (y+s v) v t`. This is derived from the ODE, not imposed.
* `nativeHop`: the update of the full eight-label carrier field. It conserves norm at every
  site (`native_conserving`), is the identity at zero length and composes exactly
  (`native_composes`).
* `readout_hop`, `embed_hop`: the packet readout of the native update is the packet update of
  the readout, and the embedded packet is carried exactly. No unobserved carrier mode feeds the
  packet.
* `transport_unique`, `realization_unique`: the realization is unique, so the chosen
  `realized c w hw` is not a selection.
* `packetUpdate`: the packet update as a `GaugeTransport.HopUpdate`. `packet_contracts` proves all
  four contracts; its infinitesimal response is the native packet generator `packetA`.
* `native_packet_yang_mills`: so `update_to_yang_mills_c2` applies to the native packet update.

**What remains input.** The control one-forms `w` (C²) that weight the root generators, and the
admission of coherent Hermitian evolution by the response cost operators as the substrate's
dynamics (the existing amplitude/spectral contract). Pure root-word permutations cannot supply a
continuous refinement on a fixed packet (`NativePacketRouting.pure_permutation_refinement_trivial`),
so the coherent generator is necessary, not decorative. No uniqueness of the controls, gauge
group or `β` is claimed, and the subsystem is not asserted to be an independent gauge factor of the
full vacuum spinor update.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NativePacketUpdate
open Matrix CarrierEvents CarrierParity NativeCoherentLinks Filter Topology
open scoped Matrix.Norms.L2Operator

/-- **Edge cocycle.** Transports of a skew connection on a finite label type compose along an
edge. Uniqueness of the transport ODE gives it; no subdivision law is assumed. -/
theorem transport_cocycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : V → V →L[ℝ] Matrix ι ι ℂ} (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix ι ι ℂ) (h0 : ∀ y v, T y v 0 = 1)
    (hd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hu : ∀ y v s, T y v s ∈ unitary (Matrix ι ι ℂ)) (y v : V) (s t : ℝ) :
    T y v (s + t) = T y v s * T (y + s • v) v t := by
  have hF (r : ℝ) : HasDerivAt (fun r => T y v (s + r) * star (T (y + s • v) v r)) 0 r := by
    have h1 : HasDerivAt (fun r => T y v (s + r)) (T y v (s + r) * A (y + (s + r) • v) v) r :=
      (hd y v (s + r)).comp_const_add s r
    have h2 := (hd (y + s • v) v r).star
    have h := FiniteMatrixTransport.rectangular_deriv h1 h2
    have he : y + (s + r) • v = (y + s • v) + r • v := by module
    convert h using 1
    rw [he, star_mul, hskew]
    noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) t 0
  simp only [add_zero, h0, star_one, Matrix.mul_one] at hc
  have hu' := (Unitary.mem_iff.mp (hu (y + s • v) v t)).1
  calc T y v (s + t) = T y v (s + t) * (star (T (y + s • v) v t) * T (y + s • v) v t) := by
        rw [hu', Matrix.mul_one]
    _ = T y v s * T (y + s • v) v t := by rw [← Matrix.mul_assoc, hc]

variable {c : Fin 3} {w : Controls}

/-- **Uniqueness of transport.** Two unitary solutions of the same transport equation starting at
the identity agree everywhere, on any finite label type. -/
theorem transport_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℝ → Matrix ι ι ℂ}
    (hskew : ∀ t, star (B t) = -B t) {T U : ℝ → Matrix ι ι ℂ} (hT0 : T 0 = 1) (hU0 : U 0 = 1)
    (hT : ∀ t, HasDerivAt T (T t * B t) t) (hU : ∀ t, HasDerivAt U (U t * B t) t)
    (hUu : ∀ t, U t ∈ unitary (Matrix ι ι ℂ)) (t : ℝ) : T t = U t := by
  have hF (r : ℝ) : HasDerivAt (fun r => T r * star (U r)) 0 r := by
    have h := FiniteMatrixTransport.rectangular_deriv (hT r) (hU r).star
    convert h using 1
    rw [star_mul, hskew]
    noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) t 0
  simp only [hT0, hU0, star_one, Matrix.mul_one] at hc
  have hu := (Unitary.mem_iff.mp (hUu t)).1
  calc T t = T t * (star (U t) * U t) := by rw [hu, Matrix.mul_one]
    _ = U t := by rw [← Matrix.mul_assoc, hc, Matrix.one_mul]

/-- **The native realization is unique.** Any two realizations for the same controls have the
same native and packet links, so statements about the chosen `realized c w hw` hold for every
realization. -/
theorem realization_unique (r r' : Realization c w) (y v : V) (h : ℝ) :
    r.native y v h = r'.native y v h ∧ r.packet y v h = r'.packet y v h :=
  ⟨transport_unique (fun t => native_skew c w (y + t • v) v) (r.native_zero y v)
      (r'.native_zero y v) (r.native_deriv y v) (r'.native_deriv y v) (r'.native_unitary y v) h,
    transport_unique (fun t => packet_skew c w (y + t • v) v) (r.packet_zero y v)
      (r'.packet_zero y v) (r.packet_deriv y v) (r'.packet_deriv y v) (r'.packet_unitary y v) h⟩

/-! ## The native eight-label update and its packet readout -/

/-- The carrier field: amplitudes on the actual eight D₄ carrier labels at each site. -/
abbrev CarrierField (c : Fin 3) := V → Carrier c → ℂ

/-- One hop of the full native carrier update along `v` with length `h`. -/
def nativeHop (r : Realization c w) (v : V) (h : ℝ) (Ψ : CarrierField c) : CarrierField c :=
  fun y => r.native y v h *ᵥ Ψ (y + h • v)

/-- One hop of the packet update. -/
def packetHop (r : Realization c w) (v : V) (h : ℝ) (ψ : GaugeTransport.Field 4) :
    GaugeTransport.Field 4 :=
  fun y => r.packet y v h *ᵥ ψ (y + h • v)

theorem native_zero (r : Realization c w) (v : V) (Ψ : CarrierField c) : nativeHop r v 0 Ψ = Ψ := by
  funext y; simp [nativeHop, r.native_zero]

/-- **Exact subdivision of the full native update.** -/
theorem native_composes (r : Realization c w) (v : V) (s t : ℝ) (Ψ : CarrierField c) :
    nativeHop r v (s + t) Ψ = nativeHop r v s (nativeHop r v t Ψ) := by
  funext y
  simp only [nativeHop]
  rw [transport_cocycle (native_skew c w) r.native r.native_zero r.native_deriv r.native_unitary,
    ← mulVec_mulVec, show y + (s + t) • v = y + s • v + t • v by module]

/-- **Norm conservation of the full native update**, site by site. -/
theorem native_conserving (r : Realization c w) (v : V) (h : ℝ) (Ψ : CarrierField c) (y : V) :
    star (nativeHop r v h Ψ y) ⬝ᵥ nativeHop r v h Ψ y = star (Ψ (y + h • v)) ⬝ᵥ Ψ (y + h • v) := by
  simp only [nativeHop, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [← star_eq_conjTranspose, (Unitary.mem_iff.mp (r.native_unitary y v h)).1, vecMul_one]

/-- **Packet readout of the native update.** Reading the packet after a native hop equals the
packet hop of the read packet: no unobserved carrier amplitude feeds the packet. -/
theorem readout_hop (r : Realization c w) (v : V) (h : ℝ) (Ψ : CarrierField c) :
    (fun y => (embedding c)ᴴ *ᵥ nativeHop r v h Ψ y) =
      packetHop r v h (fun y => (embedding c)ᴴ *ᵥ Ψ y) := by
  funext y
  simp only [nativeHop, packetHop, mulVec_mulVec, r.observes]

/-- **The embedded packet is carried exactly by the native update.** -/
theorem embed_hop (r : Realization c w) (v : V) (h : ℝ) (ψ : GaugeTransport.Field 4) :
    nativeHop r v h (fun y => embedding c *ᵥ ψ y) = fun y => embedding c *ᵥ packetHop r v h ψ y := by
  funext y
  simp only [nativeHop, packetHop, mulVec_mulVec, r.intertwines]

/-! ## The packet update satisfies the operational contracts -/

/-- The packet update as a single-hop update on four-component fields. -/
def packetUpdate (r : Realization c w) (v : V) (h : ℝ) : GaugeTransport.HopUpdate 4 v h :=
  GaugeTransport.ofLinks v h (fun y => r.packet y v h)

theorem packetUpdate_apply (r : Realization c w) (v : V) (h : ℝ) (ψ : GaugeTransport.Field 4) :
    (packetUpdate r v h).T ψ = packetHop r v h ψ := rfl

theorem packet_extract (r : Realization c w) (v : V) (h : ℝ) (y : V) :
    GaugeTransport.extract (packetUpdate r v h) y = r.packet y v h :=
  GaugeTransport.ofLinks_extract _ y

/-- **All four contracts of `CompositionalTransport` hold for the native packet update.**
Conservation, identity at zero length, exact subdivision, and infinitesimal response equal to the
native packet generator, which is C² for C² controls. -/
theorem packet_contracts (r : Realization c w) (hw : ∀ j, ContDiff ℝ 2 (w j)) :
    (∀ v h, GaugeTransport.Conserving (packetUpdate r v h)) ∧
    (∀ y v, GaugeTransport.extract (packetUpdate r v 0) y = 1) ∧
    (∀ v s t ψ, (packetUpdate r v (s + t)).T ψ =
      (packetUpdate r v s).T ((packetUpdate r v t).T ψ)) ∧
    (∀ y v, HasDerivAt (fun h => GaugeTransport.extract (packetUpdate r v h) y)
      (packetA c w y v) 0) ∧
    ContDiff ℝ 2 (packetA c w) := by
  refine ⟨fun v h => GaugeTransport.ofLinks_conserving _ (fun y => r.packet_unitary y v h),
    fun y v => by rw [packet_extract, r.packet_zero], fun v s t ψ => ?_, fun y v => ?_,
    form_c2 _ w hw⟩
  · funext y
    simp only [packetUpdate_apply, packetHop]
    rw [transport_cocycle (packet_skew c w) r.packet r.packet_zero r.packet_deriv
      r.packet_unitary, ← mulVec_mulVec, show y + (s + t) • v = y + s • v + t • v by module]
  · simp only [packet_extract]
    simpa [r.packet_zero] using r.packet_deriv y v 0

/-- **Main theorem.** The native E8 packet subsystem, evolved by smooth native root-response
controls, satisfies every hypothesis of `CompositionalTransport.update_to_yang_mills_c2`, so its
own extracted links have the classical D₄ Yang–Mills site-action limit. The contracts are proved,
not assumed; the controls `w` remain input. -/
theorem native_packet_yang_mills (hw : ∀ j, ContDiff ℝ 2 (w j)) {S : Set V}
    (hSb : Bornology.IsBounded S) (hSm : MeasurableSet S)
    (hSf : MeasureTheory.volume (frontier S) = 0) (β : ℝ) :
    Tendsto (fun n => LatticeSiteAction.siteAction
        (fun y v h => GaugeTransport.extract (packetUpdate (realized c w hw) v h) y) β S n) atTop
      (𝓝 (∫ y in S, UniformGaugeAction.yangMillsDensity (packetA c w) (fderiv ℝ (packetA c w)) y β)) := by
  obtain ⟨hcon, h0, hcomp, hgen, hA⟩ := packet_contracts (realized c w hw) hw
  exact CompositionalTransport.update_to_yang_mills_c2 (fun v h => packetUpdate (realized c w hw) v h)
    hcon h0 hcomp (packetA c w) hA hgen hSb hSm hSf β

end PMAction.NativePacketUpdate
