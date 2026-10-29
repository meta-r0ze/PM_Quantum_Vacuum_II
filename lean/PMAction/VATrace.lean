import PMAction.WallChiralCurrent

/-!
# The V−A trace and the muon-decay amplitude, with the actual Dirac matrices

Paper V's `MuonRate` takes the spin-averaged V−A amplitude `64 G_F² (p·k̄)(p_e·k)` as input. This
module proves the trace algebra behind it with the Dirac matrices reconstructed from Paper II's
Hamiltonian (`WallChiralCurrent.diracGamma`, `γ⁵ = Γ`).

* `g_eq`: the written-out gammas are `WallChiralCurrent.diracGamma`; `L = 1 − γ⁵`.
* `clifford`: `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν}`.
* `tr4_closed`: `Tr[a̸ γ^μ b̸ γ^ν (1 − γ⁵)] = 4(a^μ b^ν + a^ν b^μ − η^{μν} a·b) ± 4i ε…`, as an
  explicit table `T`.
* `contraction`: `Σ_{μν} η_μμ η_νν Tr[a̸ γ^μ b̸ γ^ν (1−γ⁵)] Tr[c̸ γ^μ d̸ γ^ν (1−γ⁵)] = 64 (a·c)(b·d)`.
* `double_projector`: with `(1 − γ⁵)` after each vertex, as in `|ū γ^μ(1−γ⁵) u|²`, each trace
  doubles, giving `256 (a·c)(b·d)`.
* `muon_amplitude`: `(G²/2) · 256 (k·p_e)(p·k̄) = 128 G² (p·k̄)(p_e·k)`, and its average over the
  muon's two spin states is `64 G² (p·k̄)(p_e·k)`, the input of `MuonRate`.

Inputs not proved here: that the spin sums of the massless spinors give `Σ u ū = p̸` (so the
squared amplitude is this product of traces), and the identification of the vertex with the
charged current (`ChargedCurrent`, `WallChiralCurrent`). Components are covariant with the
metric `η = diag(1, −1, −1, −1)`; `a̸ = η_{μμ} a_μ γ^μ`.
-/

noncomputable section
namespace PMAction.VATrace
open Matrix ConcreteFermion

/-- Dirac gammas of the actual Hamiltonian, written out. -/
def g : Fin 4 → Spin := ![
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
  !![0,0,0,-1; 0,0,-1,0; 0,1,0,0; 1,0,0,0],
  !![0,0,0,Complex.I; 0,0,-Complex.I,0; 0,-Complex.I,0,0; Complex.I,0,0,0],
  !![0,0,-1,0; 0,0,0,1; 1,0,0,0; 0,-1,0,0]]

theorem g_eq (μ : Fin 4) : g μ = WallChiralCurrent.diracGamma μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [g, WallChiralCurrent.diracGamma, beta, alpha]

/-- Minkowski signs. -/
def η : Fin 4 → ℂ := ![1, -1, -1, -1]

set_option maxHeartbeats 4000000 in
theorem clifford (μ ν : Fin 4) :
    g μ * g ν + g ν * g μ = (2 * (if μ = ν then η μ else 0)) • (1 : Spin) := by
  fin_cases μ <;> fin_cases ν <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [g, η] <;> norm_num

/-- `1 − γ⁵`. -/
def L : Spin := !![0,0,0,0; 0,0,0,0; 0,0,2,0; 0,0,0,2]

theorem L_eq : L = 1 - gamma := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [L, gamma, one_apply] <;> norm_num

/-- Feynman slash `a̸ = η_{μμ} a_μ γ^μ`. -/
def sl (a : Fin 4 → ℂ) : Spin :=
  !![0, 0, a 0 + a 3, a 1 - Complex.I * a 2; 0, 0, a 1 + Complex.I * a 2, a 0 - a 3;
     a 0 - a 3, -a 1 + Complex.I * a 2, 0, 0; -a 1 - Complex.I * a 2, a 0 + a 3, 0, 0]

theorem sl_eq (a : Fin 4 → ℂ) : sl a = ∑ μ, (η μ * a μ) • g μ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sl, g, η, Fin.sum_univ_four] <;> ring

def mdot (a b : Fin 4 → ℂ) : ℂ := a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3

/-- The trace with one projector. -/
def tr4 (a b : Fin 4 → ℂ) (μ ν : Fin 4) : ℂ := (sl a * g μ * sl b * g ν * L).trace

/-- Its closed form. -/
def T (a b : Fin 4 → ℂ) : Fin 4 → Fin 4 → ℂ := ![
  ![4*(a 0*b 0 + a 1*b 1 + a 2*b 2 + a 3*b 3),
    4*(a 0*b 1 + a 1*b 0) - 4*Complex.I*(a 2*b 3 - a 3*b 2),
    4*(a 0*b 2 + a 2*b 0) + 4*Complex.I*(a 1*b 3 - a 3*b 1),
    4*(a 0*b 3 + a 3*b 0) - 4*Complex.I*(a 1*b 2 - a 2*b 1)],
  ![4*(a 0*b 1 + a 1*b 0) + 4*Complex.I*(a 2*b 3 - a 3*b 2),
    4*(a 0*b 0 + a 1*b 1 - a 2*b 2 - a 3*b 3),
    4*(a 1*b 2 + a 2*b 1) + 4*Complex.I*(a 0*b 3 - a 3*b 0),
    4*(a 1*b 3 + a 3*b 1) - 4*Complex.I*(a 0*b 2 - a 2*b 0)],
  ![4*(a 0*b 2 + a 2*b 0) - 4*Complex.I*(a 1*b 3 - a 3*b 1),
    4*(a 1*b 2 + a 2*b 1) - 4*Complex.I*(a 0*b 3 - a 3*b 0),
    4*(a 0*b 0 - a 1*b 1 + a 2*b 2 - a 3*b 3),
    4*(a 2*b 3 + a 3*b 2) + 4*Complex.I*(a 0*b 1 - a 1*b 0)],
  ![4*(a 0*b 3 + a 3*b 0) + 4*Complex.I*(a 1*b 2 - a 2*b 1),
    4*(a 1*b 3 + a 3*b 1) + 4*Complex.I*(a 0*b 2 - a 2*b 0),
    4*(a 2*b 3 + a 3*b 2) - 4*Complex.I*(a 0*b 1 - a 1*b 0),
    4*(a 0*b 0 - a 1*b 1 - a 2*b 2 + a 3*b 3)]]

lemma I3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
lemma I4 : Complex.I ^ 4 = 1 := Complex.I_pow_four

set_option maxHeartbeats 4000000 in
theorem tr4_closed (a b : Fin 4 → ℂ) (μ ν : Fin 4) : tr4 a b μ ν = T a b μ ν := by
  fin_cases μ <;> fin_cases ν <;>
    simp [tr4, T, trace, sl, g, L, Fin.sum_univ_four] <;>
    ring_nf <;> simp only [Complex.I_sq, I4] <;> ring

set_option maxHeartbeats 4000000 in
/-- **The contraction of two V−A traces.** -/
theorem contraction (a b c d : Fin 4 → ℂ) :
    ∑ μ, ∑ ν, η μ * η ν * tr4 a b μ ν * tr4 c d μ ν = 64 * mdot a c * mdot b d := by
  simp only [tr4_closed]
  simp [Fin.sum_univ_four, T, η, mdot]
  ring_nf
  simp only [Complex.I_sq]
  ring

set_option maxHeartbeats 4000000 in
/-- Moving the second projector through `b̸ γ^ν` and using `(1−γ⁵)² = 2(1−γ⁵)`. -/
theorem projector_twice (b : Fin 4 → ℂ) (ν : Fin 4) :
    L * sl b * g ν * L = (2 : ℂ) • (sl b * g ν * L) := by
  fin_cases ν <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [L, sl, g, mul_apply, Fin.sum_univ_four] <;> ring

/-- The trace with a projector after each vertex. -/
def W (a b : Fin 4 → ℂ) (μ ν : Fin 4) : ℂ := (sl a * g μ * L * sl b * g ν * L).trace

theorem double_projector (a b : Fin 4 → ℂ) (μ ν : Fin 4) : W a b μ ν = 2 * tr4 a b μ ν := by
  have h : sl a * g μ * L * sl b * g ν * L = (2 : ℂ) • (sl a * g μ * sl b * g ν * L) := by
    have e := congrArg (fun X => sl a * g μ * X) (projector_twice b ν)
    simp only [Matrix.mul_smul] at e
    simpa [Matrix.mul_assoc] using e
  rw [W, h, trace_smul, tr4, smul_eq_mul]

theorem double_contraction (a b c d : Fin 4 → ℂ) :
    ∑ μ, ∑ ν, η μ * η ν * W a b μ ν * W c d μ ν = 256 * mdot a c * mdot b d := by
  simp only [double_projector]
  have h := contraction a b c d
  have e : ∑ μ, ∑ ν, η μ * η ν * (2 * tr4 a b μ ν) * (2 * tr4 c d μ ν) =
      4 * ∑ μ, ∑ ν, η μ * η ν * tr4 a b μ ν * tr4 c d μ ν := by
    simp only [Finset.mul_sum]; congr 1; funext μ; congr 1; funext ν; ring
  rw [e, h]; ring

/-- **The muon-decay amplitude.** With muon `p`, electron `pₑ`, muon neutrino `k`, electron
antineutrino `k̄`: `(G²/2) Σ_{μν} W(k, p) W(pₑ, k̄) = 128 G² (p·k̄)(pₑ·k)`, and the average over the
muon's two spin states is `64 G² (p·k̄)(pₑ·k)`. -/
theorem muon_amplitude (G : ℂ) (p pe k kbar : Fin 4 → ℂ) :
    G ^ 2 / 2 * (∑ μ, ∑ ν, η μ * η ν * W k p μ ν * W pe kbar μ ν) =
      128 * G ^ 2 * mdot p kbar * mdot pe k ∧
    G ^ 2 / 2 * (∑ μ, ∑ ν, η μ * η ν * W k p μ ν * W pe kbar μ ν) / 2 =
      64 * G ^ 2 * mdot p kbar * mdot pe k := by
  rw [double_contraction]
  have : mdot k pe = mdot pe k := by unfold mdot; ring
  rw [this]
  constructor <;> ring

end PMAction.VATrace
