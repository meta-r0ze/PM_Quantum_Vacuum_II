import PMAction.SpinorCompleteness

/-!
# The massive muon term vanishes in the stated V−A trace

The spin sum is slash(p)+m, not the massless slash alone. The mass term
vanishes because L gamma^nu L=0. This connects the massive spin-sum matrix
to the previously proved contraction, without asserting the physical
squared-amplitude-to-trace bridge or the substrate's weak interaction.
-/
noncomputable section
namespace PMAction.MassiveVATrace
open Matrix ConcreteFermion VATrace

lemma chiral_vertex_zero (ν : Fin 4) : L * g ν * L = 0 := by
  fin_cases ν <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [L, g, mul_apply, Fin.sum_univ_four]

/-- Trace with the massive second spin sum, in the existing matrix order. -/
def Wmass (a b : Fin 4 → ℂ) (m : ℂ) (μ ν : Fin 4) : ℂ :=
  (sl a * g μ * L * (sl b + m • (1 : Spin)) * g ν * L).trace

/-- Exact cancellation; it needs no small-mass approximation or mass-shell hypothesis. -/
theorem mass_cancels (a b : Fin 4 → ℂ) (m : ℂ) (μ ν : Fin 4) :
    Wmass a b m μ ν = W a b μ ν := by
  have hz : L * (g ν * L) = 0 := by
    rw [← Matrix.mul_assoc, chiral_vertex_zero]
  simp [Wmass, W, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, hz]

/-- The same factor 64 holds with the massive muon's slash-plus-mass spin sum.
This is still a trace identity, pending the physical amplitude-to-trace bridge. -/
theorem muon_trace (G m : ℂ) (p pe k kbar : Fin 4 → ℂ) :
    G^2/2 * (∑ μ, ∑ ν, η μ * η ν * Wmass k p m μ ν * W pe kbar μ ν) / 2 =
      64 * G^2 * mdot p kbar * mdot pe k := by
  simp_rw [mass_cancels]
  exact (muon_amplitude G p pe k kbar).2

end PMAction.MassiveVATrace
