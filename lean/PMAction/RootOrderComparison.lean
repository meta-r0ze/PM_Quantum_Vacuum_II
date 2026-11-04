import PMAction.OrderComparison
import PMAction.NativeRootGenerators

/-!
# Order comparison for actual substrate root updates

The first two certified D4 simple reflections, restricted from E8, give a
nonzero comparison signal. The exact mean on the four-coordinate odd sector
is 3/8. For every prepared amplitude in that sector the native eight-carrier
comparison agrees exactly with the coordinate comparison. This supplies an
actual substrate example, not a flavour-generation identification or a claim
that a physical update must execute/repair this loop.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RootOrderComparison
open Matrix NativePacketLinks NativeRootGenerators CarrierParity

theorem coordinate_total (a : Fin 3) :
    OrderComparison.total (link a (root a 0)) (link a (root a 1)) = (3/2:ℝ) := by
  norm_num [OrderComparison.total_formula, root_link, rootMatrix, rootMatrixZ,
    Matrix.mul_apply, PMSubstrate.ChannelSymmetry.refl, PMSubstrate.ChannelSymmetry.simple,
    PMSubstrate.ChannelSymmetry.dot4, Fin.sum_univ_four, Pi.single_apply]

theorem coordinate_mean (a : Fin 3) :
    OrderComparison.total (link a (root a 0)) (link a (root a 1))/4 = (3/8:ℝ) := by
  rw [coordinate_total]
  norm_num

theorem native_flag (a : Fin 3) (ψ : Fin 4 → ℂ) :
    OrderComparison.flag (physical a (root a 0)) (physical a (root a 1)) (embedding a *ᵥ ψ) =
      OrderComparison.flag (link a (root a 0)) (link a (root a 1)) ψ :=
  OrderComparison.encoded_flag _ (isometry a) _ _ _ _ (observed a (root a 0)) (observed a (root a 1)) ψ

theorem native_loop (a : Fin 3) :
    OrderComparison.compareLoop (physical a (root a 0)) (physical a (root a 1)) ∈ unitary _ :=
  OrderComparison.loop_unitary _ _ (physical_unitary a (root a 0)) (physical_unitary a (root a 1))

end PMAction.RootOrderComparison
