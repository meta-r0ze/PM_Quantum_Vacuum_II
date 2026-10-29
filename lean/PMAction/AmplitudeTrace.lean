import PMAction.MassiveVATrace

/-!
# The spin-summed V−A amplitude equals the trace product

Using `VATrace`'s gammas, `L = 1 − γ⁵`, `η = (1, −1, −1, −1)` and `ū = u† γ⁰`, the four-fermion
amplitude is built from Dirac bilinears,

  `M = (G/√2) Σ_μ η_μ (ū_k γ^μ L u_p)(ū_e γ^μ L v_k̄)`,

and its spin sum is derived, not assumed.

1. `pointwise`, `pair_sum`: for arbitrary spinor families and matrices,
   `Σ_{s,t} (a_s† B b_t) conj(a_s† C b_t) = Tr (B · Σ b b† · Cᴴ · Σ a a†)`.
2. `bar_bilinear`: `ū Γ w = u† (γ⁰Γ) w`. `Bv_adjoint`: `(γ⁰γ^νL)ᴴ = L γ⁰ γ^ν`.
   `g0_L_g0`: `γ⁰ L γ⁰ γ^ν = γ^ν L`. Together, `reduce`:
   `Tr (γ⁰γ^μL · Xγ⁰ · (γ⁰γ^νL)ᴴ · Yγ⁰) = Tr (Y γ^μ L X γ^ν L)`. This fixes the order and
   conjugation: the outgoing spinor's spin sum `Y` comes first, and the incoming one `X` sits between
   the projectors, which is `VATrace.W`/`MassiveVATrace.Wmass` exactly.
3. `amp_sum`: `Σ_spins M conj M = (G²/2) Σ_{μν} η_μ η_ν (Σ J^μ conj J^ν)(Σ J'^μ conj J'^ν)`, with
   `|G/√2|² = G²/2` explicit (`coupling_sq`). `current_trace`: each current sum is the trace of
   step 1.
4. `spin_averaged`: with normalized complete spinor families (`SpinorCompleteness.spin_sums`,
   `Σ u u† = (p̸ + m)γ⁰`; the antineutrino's from ker `(k̸̄ + m̄)`), the massive muon and
   antineutrino terms cancel (`MassiveVATrace.mass_cancels`), and
   `½ Σ_spins |M|² = 64 G² (p·k̄)(pₑ·k)`.

Hypotheses: real `G`, `m`, `m̄`; every momentum has positive energy and is on shell; `k` and `pₑ`
are massless; each spinor family is `√(2p₀)` times an orthonormal basis of the relevant kernel.
Not claimed: that this vertex, coupling or these external states are the substrate's weak
interaction, statistics, mediator or phase-space measure.
-/

noncomputable section
namespace PMAction.AmplitudeTrace
open Matrix ConcreteFermion VATrace SpinorCompleteness

/-! ### Step 1: spin sums of bilinears are traces -/

section General
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

set_option maxHeartbeats 4000000 in
/-- One pair of spin states: `(a† B b) conj (a† C b) = Tr (B b b† Cᴴ a a†)`. -/
lemma pointwise (a b : Fin 4 → ℂ) (B C : Spin) :
    (star a ⬝ᵥ (B *ᵥ b)) * star (star a ⬝ᵥ (C *ᵥ b)) =
      (B * vecMulVec b (star b) * Cᴴ * vecMulVec a (star a)).trace := by
  simp only [dotProduct, mulVec, trace, diag, mul_apply, vecMulVec, of_apply, Fin.sum_univ_four,
    conjTranspose_apply, Pi.star_apply, star_add, star_mul', star_star]
  ring

/-- **The reusable bridge.** With `J_μ(s, t) = a_s† B_μ b_t`,
`Σ_{s,t} J_μ(s,t) conj J_ν(s,t) = Tr (B_μ · Σ b b† · B_νᴴ · Σ a a†)`. -/
theorem pair_sum (a : ι → Fin 4 → ℂ) (b : κ → Fin 4 → ℂ) (B C : Spin) :
    ∑ s, ∑ t, (star (a s) ⬝ᵥ (B *ᵥ b t)) * star (star (a s) ⬝ᵥ (C *ᵥ b t)) =
      (B * outerSum b * Cᴴ * outerSum a).trace := by
  simp only [outerSum, Matrix.mul_sum, Matrix.sum_mul, trace_sum, pointwise]

end General

/-! ### Step 2: the Dirac-adjoint vertex and the matrix reduction -/

/-- The vertex matrix `γ⁰ γ^μ L`, so that `ū γ^μ L w = u† (γ⁰ γ^μ L) w`. -/
def Bv (μ : Fin 4) : Spin := g 0 * g μ * L

/-- `ū Γ w = u† (γ⁰ Γ) w` with `ū = u† γ⁰`. -/
lemma bar_bilinear (u w : Fin 4 → ℂ) (μ : Fin 4) :
    (star u ᵥ* g 0) ⬝ᵥ ((g μ * L) *ᵥ w) = star u ⬝ᵥ (Bv μ *ᵥ w) := by
  rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Bv, Matrix.mul_assoc]

/-- `(γ⁰ γ^ν L)ᴴ = L γ⁰ γ^ν`. -/
lemma Bv_adjoint (ν : Fin 4) : (Bv ν)ᴴ = L * g 0 * g ν := by
  fin_cases ν <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Bv, L, g, mul_apply, Fin.sum_univ_four, conjTranspose_apply]
  all_goals ring

/-- `γ⁰ L γ⁰ γ^ν = γ^ν L` (`γ⁰ L γ⁰ = 1 + γ⁵`, which moves through `γ^ν` to `L`). -/
lemma g0_L_g0 (ν : Fin 4) : g 0 * L * g 0 * g ν = g ν * L := by
  fin_cases ν <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [L, g, mul_apply, Fin.sum_univ_four]
  all_goals ring

/-- **Matrix reduction.** For any `X, Y`,
`Tr (γ⁰γ^μL · Xγ⁰ · (γ⁰γ^νL)ᴴ · Yγ⁰) = Tr (Y γ^μ L X γ^ν L)`. -/
theorem reduce (X Y : Spin) (μ ν : Fin 4) :
    (Bv μ * (X * g 0) * (Bv ν)ᴴ * (Y * g 0)).trace = (Y * g μ * L * X * g ν * L).trace := by
  rw [Bv_adjoint]
  have h1 : Bv μ * (X * g 0) * (L * g 0 * g ν) * (Y * g 0) =
      g 0 * (g μ * L * X * (g 0 * L * g 0 * g ν) * Y) * g 0 := by
    simp only [Bv, Matrix.mul_assoc]
  rw [h1, g0_L_g0, trace_mul_comm, ← Matrix.mul_assoc, g0_sq, Matrix.one_mul,
    trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-! ### Step 3: the amplitude and its spin sum -/

section Amplitude
variable {ιk ιp ιe ιb : Type*} [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]

/-- Dirac adjoint `ū = u† γ⁰`. -/
def bar (u : Fin 4 → ℂ) : Fin 4 → ℂ := star u ᵥ* g 0

/-- **The four-fermion amplitude** `M = (G/√2) Σ_μ η_μ (ū_k γ^μ L u_p)(ū_e γ^μ L v_k̄)`. -/
def amp (G : ℝ) (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ)
    (vb : ιb → Fin 4 → ℂ) (x : (ιk × ιp) × (ιe × ιb)) : ℂ :=
  ((G / Real.sqrt 2 : ℝ) : ℂ) * ∑ μ, η μ * (bar (uk x.1.1) ⬝ᵥ ((g μ * L) *ᵥ up x.1.2)) *
    (bar (ue x.2.1) ⬝ᵥ ((g μ * L) *ᵥ vb x.2.2))

lemma star_η (μ : Fin 4) : star (η μ) = η μ := by fin_cases μ <;> simp [η]

lemma coupling_sq (G : ℝ) :
    ((G / Real.sqrt 2 : ℝ) : ℂ) * star ((G / Real.sqrt 2 : ℝ) : ℂ) = ((G : ℂ) ^ 2 / 2) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : G / Real.sqrt 2 * (G / Real.sqrt 2) = G ^ 2 / 2 := by
    rw [div_mul_div_comm, h2]; ring
  rw [this]; push_cast; ring

/-- Current bilinears with the Dirac-adjoint vertex. -/
def Jk (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (μ : Fin 4) (y : ιk × ιp) : ℂ :=
  star (uk y.1) ⬝ᵥ (Bv μ *ᵥ up y.2)

/-- **Spin sum of `|M|²` factorizes into two current sums.** -/
theorem amp_sum (G : ℝ) (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ)
    (vb : ιb → Fin 4 → ℂ) :
    ∑ x, amp G uk up ue vb x * star (amp G uk up ue vb x) =
      ((G : ℂ) ^ 2 / 2) * ∑ μ, ∑ ν, η μ * η ν *
        (∑ y, Jk uk up μ y * star (Jk uk up ν y)) * (∑ z, Jk ue vb μ z * star (Jk ue vb ν z)) := by
  have hamp : ∀ x, amp G uk up ue vb x =
      ((G / Real.sqrt 2 : ℝ) : ℂ) * ∑ μ, η μ * Jk uk up μ x.1 * Jk ue vb μ x.2 := by
    intro x; simp only [amp, bar, bar_bilinear, Jk]
  have hterm : ∀ x, amp G uk up ue vb x * star (amp G uk up ue vb x) =
      ((G : ℂ) ^ 2 / 2) * ∑ μ, ∑ ν, η μ * η ν *
        (Jk uk up μ x.1 * star (Jk uk up ν x.1)) * (Jk ue vb μ x.2 * star (Jk ue vb ν x.2)) := by
    intro x
    rw [hamp, star_mul', ← coupling_sq]
    simp only [star_sum, star_mul', star_η, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  simp only [hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Each current sum is a trace of spin sums.** -/
theorem current_trace (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (μ ν : Fin 4) :
    ∑ y, Jk uk up μ y * star (Jk uk up ν y) =
      (Bv μ * outerSum up * (Bv ν)ᴴ * outerSum uk).trace := by
  rw [Fintype.sum_prod_type]; exact pair_sum uk up (Bv μ) (Bv ν)

end Amplitude

/-! ### Step 4: the spin-summed, spin-averaged amplitude -/

section Main
variable {ιk ιp ιe ιb : Type*} [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
  [DecidableEq ιk] [DecidableEq ιp] [DecidableEq ιe] [DecidableEq ιb]

/-- Hypotheses on one external state: `e` is an orthonormal basis of ker `(p̸ − m)`. -/
structure Basis (p : Fin 4 → ℝ) (m : ℝ) {ι : Type*} [DecidableEq ι] (e : ι → Fin 4 → ℂ) : Prop where
  orth : ∀ s t, star (e s) ⬝ᵥ e t = if s = t then 1 else 0
  ker : ∀ s, D p m *ᵥ e s = 0
  span : ∀ v, D p m *ᵥ v = 0 → v ∈ Submodule.span ℂ (Set.range e)

/-- Normalized spinors `√(2p₀) e`. -/
def norm (p : Fin 4 → ℝ) {ι : Type*} (e : ι → Fin 4 → ℂ) : ι → Fin 4 → ℂ :=
  fun s => ((Real.sqrt (2 * p 0) : ℝ) : ℂ) • e s

lemma outer_of_basis (p : Fin 4 → ℝ) (m : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin 4 → ℂ) (hp : 0 < p 0) (hs : msq p = m ^ 2) (hb : Basis p m e) :
    outerSum (norm p e) = A p m :=
  (spin_sums p m hp hs e hb.orth hb.ker hb.span).1

/-- **The spin-summed and averaged V−A amplitude.** Muon `p` (mass `m`), muon neutrino `k`
(massless), electron `pₑ` (massless), electron antineutrino `k̄` (mass `m̄`; its spinors span
ker `(k̸̄ + m̄)`). Then `½ Σ_spins |M|² = 64 G² (p·k̄)(pₑ·k)`. -/
theorem spin_averaged (G m mb : ℝ) (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ) (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : msq pk = 0) (hp : msq pp = m ^ 2) (he : msq pe = 0) (hb : msq pb = mb ^ 2)
    (bk : Basis pk 0 ek) (bp : Basis pp m ep) (be : Basis pe 0 ee) (bb : Basis pb (-mb) eb) :
    ((∑ x, Complex.normSq (amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x) : ℝ) : ℂ)
        / 2 = 64 * (G : ℂ) ^ 2 * mdot (cp pp) (cp pb) * mdot (cp pe) (cp pk) := by
  have hk' : msq pk = (0 : ℝ) ^ 2 := by rw [hk]; ring
  have he' : msq pe = (0 : ℝ) ^ 2 := by rw [he]; ring
  have hb' : msq pb = (-mb) ^ 2 := by rw [hb]; ring
  have Ok := outer_of_basis pk 0 ek hk0 hk' bk
  have Op := outer_of_basis pp m ep hp0 hp bp
  have Oe := outer_of_basis pe 0 ee he0 he' be
  have Ob := outer_of_basis pb (-mb) eb hb0 hb' bb
  push_cast
  simp only [← Complex.mul_conj]
  rw [show (∑ x, amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x *
      (starRingEnd ℂ) (amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x)) =
      ∑ x, amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x *
      star (amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x) from rfl]
  rw [amp_sum]
  simp only [current_trace, Ok, Op, Oe, Ob, A, reduce]
  have hW : ∀ μ ν, ((P pe + ((0:ℝ):ℂ) • 1) * g μ * L * (P pb + ((-mb : ℝ) : ℂ) • 1) * g ν * L).trace
      = W (cp pe) (cp pb) μ ν := by
    intro μ ν
    have := MassiveVATrace.mass_cancels (cp pe) (cp pb) ((-mb : ℝ) : ℂ) μ ν
    simpa [MassiveVATrace.Wmass, P] using this
  have hWm : ∀ μ ν, ((P pk + ((0:ℝ):ℂ) • 1) * g μ * L * (P pp + (m : ℂ) • 1) * g ν * L).trace
      = MassiveVATrace.Wmass (cp pk) (cp pp) m μ ν := by
    intro μ ν; simp [MassiveVATrace.Wmass, P]
  simp only [hW, hWm]
  have := MassiveVATrace.muon_trace (G : ℂ) (m : ℂ) (cp pp) (cp pe) (cp pk) (cp pb)
  rw [← this]

end Main

end PMAction.AmplitudeTrace
