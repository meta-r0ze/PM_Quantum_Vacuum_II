import PMAction.CarrierEvents
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finite

/-! A count-to-cost-to-trace bridge for actual discrete carriers.
It is a permutation result; its extension to phase readout is a separate contract. -/
noncomputable section
namespace PMAction.CarrierCost
open Matrix Finset CarrierEvents

abbrev Packet (a b : Fin 3) := Carrier a ⊕ Carrier b

theorem packet_card (a b : Fin 3) : Fintype.card (Packet a b)=16 := by
  simp [Packet, Fintype.card_sum, carrier_card]

def packetVector {a b : Fin 3} : Packet a b → (Fin 4 → ℤ) := Sum.elim vector vector

theorem packet_vector_injective {a b : Fin 3} (hab : a ≠ b) :
    Function.Injective (@packetVector a b) := by
  intro v w h
  cases v with
  | inl v => cases w with
    | inl w => exact congrArg Sum.inl (vector_injective a h)
    | inr w =>
      have hc : classLabel a=classLabel b := v.2.1.symm.trans ((congrArg PMArch.Channels.glueClass h).trans w.2.1)
      have he : a=b := Fin.ext (by simpa [classLabel] using hc)
      exact (hab he).elim
  | inr v => cases w with
    | inl w =>
      have hc : classLabel b=classLabel a := v.2.1.symm.trans ((congrArg PMArch.Channels.glueClass h).trans w.2.1)
      have he : b=a := Fin.ext (by simpa [classLabel] using hc)
      exact (hab he.symm).elim
    | inr w => exact congrArg Sum.inr (vector_injective b h)

/-- Eight minimal states are not eight independent geometric vectors in four coordinates.
A Hilbert-space amplitude basis is an additional construction, not this cardinality count. -/
theorem geometric_vectors_not_independent (c : Fin 3) :
    ¬ LinearIndependent ℚ (fun v : Carrier c => fun i : Fin 4 => (vector v i : ℚ)) := by
  intro h
  have hn := h.fintype_card_le_finrank
  simp only [carrier_card, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hn
  norm_num at hn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def changed (e : Equiv.Perm ι) : Finset ι := univ.filter (fun x => e x ≠ x)
def fixed (e : Equiv.Perm ι) : Finset ι := univ.filter (fun x => e x=x)

lemma trace_fixed (e : Equiv.Perm ι) : (e.permMatrix ℂ).trace = ((fixed e).card : ℂ) := by
  rw [trace_permutation]
  have hs : Function.fixedPoints e = (fixed e : Set ι) := by
    ext x; simp [fixed, Function.fixedPoints, Function.IsFixedPt]
  rw [hs, Set.ncard_coe_finset]

/-- Under uniform sampling, a changed-state event has normalized trace cost. -/
theorem changed_probability [Nonempty ι] (e : Equiv.Perm ι) :
    PMArch.NetCost.prob (changed e) = 1-(e.permMatrix ℂ).trace.re/Fintype.card ι := by
  have hc : (fixed e).card+(changed e).card=Fintype.card ι := by
    simpa [fixed, changed] using card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun x => e x=x)
  have hr : ((fixed e).card : ℝ)+((changed e).card : ℝ)=Fintype.card ι := by exact_mod_cast hc
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  rw [PMArch.NetCost.prob, trace_fixed]
  simp only [Complex.natCast_re]
  field_simp
  linarith

/-- The common primitive toll prices the derived event, rather than a separately chosen score. -/
theorem primitive_trace_cost [Nonempty ι] (e : Equiv.Perm ι) (toll : ℝ) :
    PMArch.NetCost.expectedCost toll (fun _ : Fin 1 => changed e) =
      toll*(1-(e.permMatrix ℂ).trace.re/Fintype.card ι) := by
  rw [PMArch.NetCost.expected_count_linear]
  simp [changed_probability]

end PMAction.CarrierCost
