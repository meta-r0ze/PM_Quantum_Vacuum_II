import PMAction.EventAccounting
import PMAction.CarrierEvents
import PMFramework.LawSelection

/-!
# The sampling law is the selected law

`EventAccounting` and `CarrierEvents` take uniform sampling as an explicit input. The framework's
Selection Principle supplies it: among candidate event laws, the one that survives selection is
the uniform law, under either the worst-case or the long-run average return cost
(`PMFramework.LawSelection.selected_uniform_worst`, `selected_uniform_average`). On each carrier
class it is also forced by symmetry, since the `D₄` Weyl reflections act transitively on the eight
minimal vectors (Paper I, `ChannelSymmetry`).

* `selected_recovers_netCost`: with the selected law, weighted event accounting is Paper I's
  `NetCost`.
* `selected_activation`, `selected_primitive_cost`: the E8 root reflection moves a carrier with
  probability `1/2` under the selected law, at cost `toll/2`.
-/

noncomputable section
namespace PMAction.SelectedSampling
open Finset PMFramework.LawSelection

theorem selected_recovers_netCost {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (toll : ℝ) {n : ℕ} (E : Fin n → Finset Ω) :
    EventAccounting.cost toll uniform E = PMArch.NetCost.expectedCost toll E :=
  EventAccounting.uniform_recovers_netCost toll E

instance (c : Fin 3) : Nonempty (CarrierEvents.Carrier c) :=
  Fintype.card_pos_iff.mp (by rw [CarrierEvents.carrier_card]; norm_num)

theorem selected_activation (c : Fin 3) :
    EventAccounting.eventMass uniform (CarrierEvents.active c) = 1 / 2 := by
  simp only [EventAccounting.eventMass, uniform, sum_const, CarrierEvents.active_card,
    CarrierEvents.carrier_card, nsmul_eq_mul]
  norm_num

theorem selected_primitive_cost (c : Fin 3) (toll : ℝ) :
    EventAccounting.cost toll uniform (fun _ : Fin 1 => CarrierEvents.active c) = toll / 2 := by
  rw [EventAccounting.weighted_linear]
  simp [selected_activation, div_eq_mul_inv]

end PMAction.SelectedSampling
