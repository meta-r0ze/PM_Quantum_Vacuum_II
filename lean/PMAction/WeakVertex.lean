import PMAction.AmplitudeTrace
import PMAction.ChargedCurrent
import PMAction.ContactMatching
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The V−A contact vertex from W exchange, and the external spinor bases

Paper V's rate uses `AmplitudeTrace.amp`, the four-fermion amplitude, with complete orthonormal
kernel bases as hypotheses. This module derives both from Paper II material.

* `vertex_eq`: Paper II's charged-current vertex `(g/√2) γ^μ P_L`
  (`ChargedCurrent.vertex_coefficient`) is `(g/(2√2)) γ^μ (1 − γ⁵)`.
* `exchange`: the tree-level W-exchange amplitude, with unitary-gauge propagator
  `(g_μν − q_μ q_ν/m²)/(m² − q²)`.
* `exchange_at_zero`, `exchange_contact`: at zero momentum transfer the exchange amplitude *is*
  `AmplitudeTrace.amp G`, with `G = √2 g²/(8m²)`, and it tends to it as `q → 0`.
* `exchange_fermi`: with `m² = g²v²/4`, `G = 1/(√2 v²)` (`ContactMatching.fermi_from_mass`).
* `exchange_spin_averaged`: the contact limit of W exchange gives `64 G² (p·k̄)(pₑ·k)`.
* `basis_exists`: every kernel `ker(p̸ − m)` has an orthonormal spanning family, so the
  `AmplitudeTrace.Basis` hypotheses are always satisfiable.
-/

noncomputable section
namespace PMAction.WeakVertex
open Matrix VATrace AmplitudeTrace SpinorCompleteness Filter Topology

/-- Left projector `P_L = ½(1 − γ⁵)`. -/
def PL : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • L

/-- The charged-current vertex `(g/√2) γ^μ P_L`. -/
def vertex (gw : ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((gw / Real.sqrt 2 : ℝ) : ℂ) • (g μ * PL)

theorem vertex_eq (gw : ℝ) (μ : Fin 4) :
    vertex gw μ = ((gw / (2 * Real.sqrt 2) : ℝ) : ℂ) • (g μ * L) := by
  simp only [vertex, PL, mul_smul_comm, smul_smul]
  congr 1; push_cast; ring

/-- Vertex bilinear `ū Γ^μ w`. -/
def current (gw : ℝ) (μ : Fin 4) (u w : Fin 4 → ℂ) : ℂ := bar u ⬝ᵥ (vertex gw μ *ᵥ w)

/-- **Tree-level W exchange** with momentum transfer `q` and the unitary-gauge propagator. -/
def exchange (gw mW : ℝ) (q : Fin 4 → ℝ) {ιk ιp ιe ιb : Type*} (uk : ιk → Fin 4 → ℂ)
    (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ)
    (x : (ιk × ιp) × (ιe × ιb)) : ℂ :=
  ((1 / (mW ^ 2 - msq q) : ℝ) : ℂ) *
    (∑ μ, η μ * current gw μ (uk x.1.1) (up x.1.2) * current gw μ (ue x.2.1) (vb x.2.2) -
      (∑ μ, η μ * (q μ : ℂ) * current gw μ (uk x.1.1) (up x.1.2)) *
        (∑ ν, η ν * (q ν : ℂ) * current gw ν (ue x.2.1) (vb x.2.2)) / ((mW : ℂ) ^ 2))

/-- The Fermi constant of W exchange, `G = √2 g²/(8 m²)`. -/
def fermiG (gw mW : ℝ) : ℝ := Real.sqrt 2 * (gw ^ 2 / (8 * mW ^ 2))

lemma current_eq (gw : ℝ) (μ : Fin 4) (u w : Fin 4 → ℂ) :
    current gw μ u w = ((gw / (2 * Real.sqrt 2) : ℝ) : ℂ) * (bar u ⬝ᵥ ((g μ * L) *ᵥ w)) := by
  rw [current, vertex_eq, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **At zero momentum transfer, W exchange is the V−A contact amplitude.** -/
theorem exchange_at_zero (gw mW : ℝ) (hm : mW ≠ 0) {ιk ιp ιe ιb : Type*}
    (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ) :
    exchange gw mW 0 uk up ue vb = amp (fermiG gw mW) uk up ue vb := by
  funext x
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hc : ((1 / (mW ^ 2 - msq 0) : ℝ) : ℂ) * ((gw / (2 * Real.sqrt 2) : ℝ) : ℂ) ^ 2 =
      ((fermiG gw mW / Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    simp only [msq, Pi.zero_apply, fermiG]
    field_simp
    rw [hs]; ring
  simp only [exchange, amp, current_eq, Pi.zero_apply, Complex.ofReal_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, sub_zero, zero_div]
  rw [← hc]
  try simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- **The contact limit.** As the momentum transfer goes to zero, W exchange tends to the V−A
contact amplitude with `G = √2 g²/(8m²)`. -/
theorem exchange_contact (gw mW : ℝ) (hm : mW ≠ 0) {ιk ιp ιe ιb : Type*}
    (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ)
    (x : (ιk × ιp) × (ιe × ιb)) :
    Tendsto (fun q => exchange gw mW q uk up ue vb x) (𝓝 0)
      (𝓝 (amp (fermiG gw mW) uk up ue vb x)) := by
  rw [← exchange_at_zero gw mW hm uk up ue vb]
  have hden : mW ^ 2 - msq (0 : Fin 4 → ℝ) ≠ 0 := by
    simp only [msq, Pi.zero_apply]; norm_num; exact hm
  have hcm : ContinuousAt (fun q : Fin 4 → ℝ => mW ^ 2 - msq q) 0 := by
    unfold msq; fun_prop
  have hinv : ContinuousAt (fun q : Fin 4 → ℝ => ((1 / (mW ^ 2 - msq q) : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.div hcm hden)
  have hq : ∀ μ : Fin 4, Continuous (fun q : Fin 4 → ℝ => ((q μ : ℝ) : ℂ)) :=
    fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  have hrest : ContinuousAt (fun q : Fin 4 → ℝ =>
      ∑ μ, η μ * current gw μ (uk x.1.1) (up x.1.2) * current gw μ (ue x.2.1) (vb x.2.2) -
        (∑ μ, η μ * (q μ : ℂ) * current gw μ (uk x.1.1) (up x.1.2)) *
          (∑ ν, η ν * (q ν : ℂ) * current gw ν (ue x.2.1) (vb x.2.2)) / ((mW : ℂ) ^ 2)) 0 := by
    apply Continuous.continuousAt
    have := hq
    fun_prop
  exact (hinv.mul hrest).tendsto

/-- With the mediator mass `m² = g²v²/4`, the contact coupling is `1/(√2 v²)`. -/
theorem exchange_fermi (gw v mW : ℝ) (hg : gw ≠ 0) (hv : v ≠ 0)
    (hm : mW ^ 2 = gw ^ 2 * v ^ 2 / 4) : fermiG gw mW = 1 / (Real.sqrt 2 * v ^ 2) :=
  ContactMatching.fermi_from_mass gw v mW hg hv hm

/-- **W exchange at zero momentum transfer gives Paper V's spin-averaged rate input.** -/
theorem exchange_spin_averaged (gw mW m mb : ℝ) (hm : mW ≠ 0) {ιk ιp ιe ιb : Type*}
    [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
    [DecidableEq ιk] [DecidableEq ιp] [DecidableEq ιe] [DecidableEq ιb]
    (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ) (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : msq pk = 0) (hp : msq pp = m ^ 2) (he : msq pe = 0) (hb : msq pb = mb ^ 2)
    (bk : Basis pk 0 ek) (bp : Basis pp m ep) (be : Basis pe 0 ee) (bb : Basis pb (-mb) eb) :
    ((∑ x, Complex.normSq (exchange gw mW 0 (norm pk ek) (norm pp ep) (norm pe ee)
        (norm pb eb) x) : ℝ) : ℂ) / 2 =
      64 * (fermiG gw mW : ℂ) ^ 2 * mdot (cp pp) (cp pb) * mdot (cp pe) (cp pk) := by
  rw [exchange_at_zero gw mW hm]
  exact spin_averaged _ m mb pk pp pe pb ek ep ee eb hk0 hp0 he0 hb0 hk hp he hb bk bp be bb

/-! ## External spinor bases exist -/

/-- **Orthonormal kernel bases exist.** For every momentum and mass, `ker(p̸ − m)` has an
orthonormal spanning family. So `AmplitudeTrace.Basis` is always satisfiable; on shell with
positive energy it has exactly two members (`SpinorCompleteness.rank_two`). -/
theorem basis_exists (p : Fin 4 → ℝ) (m : ℝ) :
    ∃ (k : ℕ) (e : Fin k → Fin 4 → ℂ), Basis p m e := by
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin 4)) :=
    Submodule.comap (WithLp.linearEquiv 2 ℂ (Fin 4 → ℂ)).toLinearMap
      (LinearMap.ker (D p m).mulVecLin)
  let b := stdOrthonormalBasis ℂ W
  have hmem : ∀ w : W, D p m *ᵥ (w : EuclideanSpace ℂ (Fin 4)).ofLp = 0 := by
    intro w
    have := w.2
    rw [Submodule.mem_comap, LinearMap.mem_ker] at this
    exact this
  refine ⟨Module.finrank ℂ W, fun s => ((b s : W) : EuclideanSpace ℂ (Fin 4)).ofLp, ?_, ?_, ?_⟩
  · intro s t
    have h := orthonormal_iff_ite.mp b.orthonormal s t
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm]; exact h
  · intro s; exact hmem (b s)
  · intro v hv
    have hw : WithLp.toLp 2 v ∈ W := by
      simp [W, Submodule.mem_comap, LinearMap.mem_ker, hv]
    have hsum := b.sum_repr ⟨WithLp.toLp 2 v, hw⟩
    have hv' : v = ∑ i, (b.repr ⟨WithLp.toLp 2 v, hw⟩).ofLp i •
        ((b i : W) : EuclideanSpace ℂ (Fin 4)).ofLp := by
      have := congrArg (fun w : W => ((w : EuclideanSpace ℂ (Fin 4))).ofLp) hsum
      simpa using this.symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end PMAction.WeakVertex
