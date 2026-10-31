import PMAction.IntegratedGaugeAction

/-!
# PM's lattice gauge action has the classical Yang–Mills continuum limit

**Main theorem (`pm_lattice_yang_mills`).** Let `A` be a `u(N)`-valued connection on `ℝ⁴` with
continuous derivative, Lipschitz within distance two of each point of a box `I` (one constant), and
let `U` be any unitary link family, one matrix per directed edge, within `K h³` of the midpoint
exponentials of `A` (cubic consistency: the links discretize `A`). Take the Wilson density on the
D₄ minimal triangles, `linkDensity U x β h = (β/12) Σ_△ Re tr(1 − U_△)/h⁴`. Accumulate it with
cell volumes over any refining sequence of tagged partitions of `I` while `h → 0⁺`. Then the sums
converge to

    ∫_I (β/2) Σ_{μ,ν} ‖F_{μν}(x)‖²_F dx,

the classical Yang–Mills action on `I`.

**What this is and is not.** The tagged partitions are unrelated to the lattice: this is a Riemann
sum of the per-site density, sampled anywhere. The sum over the actual D₄ sites with the D₄ cell
volume is `LatticeSiteAction.d4_yang_mills_action`, which also removes the consistency and
unitarity hypotheses for parallel-transport links. In every version the link field is built from
a given smooth connection `A`; no theorem derives the links from PM's substrate update. The gauge
group, `N` and `β` are inputs.

**Normalization.** `canonical_density` takes the generator identity
`‖F_{μν}‖²_F = (g²/2) Σ_a (F^a_{μν})²` as a hypothesis (pure arithmetic). `canonical_from_generators`
derives it from `F = −i g Σ_a F^a T^a` with Hermitian `tr T^a T^b = δ^{ab}/2`
(`generator_norm`): at `β = 1/g²` the limit is the canonical `(1/4) Σ_{μν a} (F^a_{μν})²`. This is
a convention-matching statement, not a derivation of `g`: `SummedReference.sum_canonical_iff` only
restates the canonical condition as `g² = 1/(κ·toll·m·W)`, and those factors are not all fixed.

Proof chain, all in Lean: triangle Taylor expansion with explicit remainder
(`VaryingFields.triangle_expand_explicit`), unitarity identity for the Wilson term
(`LinkConsistency.wilson_of_expansion`), stability of the actual links (`holonomy_uniform`),
compactness for one constant on the box (`UniformGaugeAction`), and Riemann-sum convergence
(`IntegratedGaugeAction.sampled_limit`).

Hypotheses retained: local `C^{1,1}` regularity (the derivative bound is used only within
distance two of the box; earlier versions demanded a global bound, which excluded every connection
whose derivative grows, e.g. polynomial ones); cubic consistency, a theorem for parallel-transport
links (`ParallelTransport.transport_consistent`). `GaugeTransport` shows unitarity, locality and
conservation alone do not imply it. This is a **classical** statement about smooth fields. It
constructs no quantum measure and says nothing about a mass gap; see `YANG-MILLS-STATUS.md`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ClassicalYangMills
open Matrix Set Filter Topology MeasureTheory BoxIntegral VaryingFields
open scoped Matrix.Norms.L2Operator

local notation "V4" => (Fin 4 → ℝ)
variable {N : ℕ}

/-- **The actual holonomy expands uniformly.** -/
theorem holonomy_uniform {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V4} (hs : IsCompact s)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L K : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ s, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : ∀ x ∈ s, LinkConsistency.CubicConsistent U A x K)
    (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖(LinkConsistency.holonomy U x (rv p.1) (rv p.2) h - 1) -
        h ^ 2 • ((1 / 2 : ℝ) • curvature A DA x (rv p.1) (rv p.2))‖ ≤ K' * h ^ 3 := by
  obtain ⟨C0, hC0, hb⟩ := UniformGaugeAction.triangle_uniform hs hA hDA hL0 (rv p.1) (rv p.2)
    (fun x hx y hy => hL x hx y (hy.trans (rv_pair p)))
  refine ⟨C0 + 3 * K, by positivity, fun x hx h hh h1 => ?_⟩
  have ha := LinkConsistency.rv_norm p.1
  have hb2 := LinkConsistency.rv_norm p.2
  have hba : ‖rv p.2 - rv p.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hclose : ‖LinkConsistency.holonomy U x (rv p.1) (rv p.2) h -
      triangle A x (rv p.1) (rv p.2) h‖ ≤ 3 * K * h ^ 3 := by
    unfold LinkConsistency.holonomy triangle
    refine (LinkConsistency.holonomy_close (hU _ _ _) (Unitary.star_mem (hU _ _ _))
      (LinkConsistency.link_unitary hskew x _ h)
      (LinkConsistency.link_unitary hskew _ _ h)).trans ?_
    have e1 := hc x hx x (rv p.1) h hh h1 (by simp) (by linarith)
    have e2 := hc x hx (x + h • rv p.1) (rv p.2 - rv p.1) h hh h1 (by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
        nlinarith [norm_nonneg (rv p.1)]) hba
    have e3 : ‖(U x (rv p.2) h)ᴴ -
        NormedSpace.exp (h • -(A (x + (h / 2) • rv p.2) (rv p.2)))‖ ≤ K * h ^ 3 := by
      rw [← LinkConsistency.reverse_eq hskew, ← conjTranspose_sub,
        Matrix.l2_opNorm_conjTranspose]
      exact hc x hx x (rv p.2) h hh h1 (by simp) (by linarith)
    rw [← Matrix.star_eq_conjTranspose] at e3
    linarith
  have htri := hb x hx h hh.le h1
  have e : (LinkConsistency.holonomy U x (rv p.1) (rv p.2) h - 1) -
      h ^ 2 • ((1 / 2 : ℝ) • curvature A DA x (rv p.1) (rv p.2)) =
      (LinkConsistency.holonomy U x (rv p.1) (rv p.2) h - triangle A x (rv p.1) (rv p.2) h) +
      (triangle A x (rv p.1) (rv p.2) h -
        (1 + (h ^ 2 / 2) • curvature A DA x (rv p.1) (rv p.2))) := by
    rw [smul_smul]
    module
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 3 * K * h ^ 3 + C0 * h ^ 3 := add_le_add hclose htri
    _ = (C0 + 3 * K) * h ^ 3 := by ring

/-- Uniform Wilson-term control for the actual links on one D₄ triangle. -/
theorem link_wilson_uniform {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V4} (hs : IsCompact s)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L K : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ s, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : ∀ x ∈ s, LinkConsistency.CubicConsistent U A x K)
    (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (1 - LinkConsistency.holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        UniformGaugeAction.triangleTarget A DA x (rv p.1) (rv p.2)| ≤ C * h := by
  obtain ⟨K', hK', hb⟩ := holonomy_uniform hs hA hDA hL0 hL hskew U hU hK hc p
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hcont : Continuous (fun x => (1 / 2 : ℝ) • curvature A DA x (rv p.1) (rv p.2)) := by
    unfold curvature
    fun_prop
  obtain ⟨C, hC, hw⟩ := UniformGaugeAction.wilson_uniform
    (P := fun x h => LinkConsistency.holonomy U x (rv p.1) (rv p.2) h) hs hcont hK'
    (fun x _ h _ _ => (Unitary.mem_iff.mp ((unitary _).mul_mem ((unitary _).mul_mem
      (hU _ _ _) (hU _ _ _)) (Unitary.star_mem (hU _ _ _)))).1)
    (fun x hx h hh h1 => hb x hx h hh h1)
  exact ⟨C, hC, hw⟩

/-- The two forms of the limit density agree pointwise. -/
theorem quadratic_eq {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V4} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    UniformGaugeAction.quadraticDensity A DA x β = UniformGaugeAction.yangMillsDensity A DA x β := by
  obtain ⟨C, hC, hb⟩ := UniformGaugeAction.quadratic_uniform (isCompact_singleton (x := x)) hA
    hDA hL0 (fun y hy z hz => by rw [mem_singleton_iff.mp hy] at hz ⊢; exact hL z hz) hskew β
  have hnew := UniformGaugeAction.limit_of_bound (fun h => d4Density A x β h) _ C hC
    (hb x (mem_singleton x))
  exact tendsto_nhds_unique hnew (d4_yang_mills_tendsto_loc hA hL0 hL hskew β)

/-- **Uniform convergence of PM's link density to the Yang–Mills density.** -/
theorem link_yang_mills_uniform {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V4} (hs : IsCompact s)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L K : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ s, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : ∀ x ∈ s, LinkConsistency.CubicConsistent U A x K) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ h : ℝ, 0 < h → h ≤ 1 →
      |LinkConsistency.linkDensity U x β h - UniformGaugeAction.yangMillsDensity A DA x β| ≤
        C * h := by
  have hp (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :=
    link_wilson_uniform hs hA hDA hL0 hL hskew U hU hK hc p
  choose C hC hb using hp
  refine ⟨|β| / 12 * ∑ p ∈ D4Gauge.tri, C p,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => hC p), fun x hx h hh h1 => ?_⟩
  rw [← quadratic_eq hA hDA hL0 (hL x hx) hskew β, LinkConsistency.linkDensity,
    UniformGaugeAction.quadraticDensity, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
  have hsum : |∑ p ∈ D4Gauge.tri,
      ((trace (1 - LinkConsistency.holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        UniformGaugeAction.triangleTarget A DA x (rv p.1) (rv p.2))| ≤
      (∑ p ∈ D4Gauge.tri, C p) * h := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hb p x hx h hh h1)
  rw [show |β / 12| = |β| / 12 by rw [abs_div]; norm_num]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

/-- **PM's lattice gauge action converges to the classical Yang–Mills action on a box.** -/
theorem pm_lattice_yang_mills {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} (I : Box (Fin 4))
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L K : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ I.Icc, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : ∀ x ∈ I.Icc, LinkConsistency.CubicConsistent U A x K) (β : ℝ)
    (π : ℕ → TaggedPrepartition I)
    (hπ : Tendsto π atTop (IntegrationParams.Riemann.toFilteriUnion I ⊤))
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[>] (0 : ℝ))) :
    Tendsto (fun r => IntegratedGaugeAction.sample I
        (fun x => LinkConsistency.linkDensity U x β (h r)) (π r)) atTop
      (𝓝 (∫ x in I, UniformGaugeAction.yangMillsDensity A DA x β)) := by
  obtain ⟨C, hC, hb⟩ := link_yang_mills_uniform I.isCompact_Icc hA hDA hL0 hL hskew U hU hK hc β
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hsmall := hh.eventually (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
  have hε : Tendsto (fun r => C * h r) atTop (𝓝 0) := by
    simpa using (hh.mono_right nhdsWithin_le_nhds).const_mul C
  apply IntegratedGaugeAction.sampled_limit I _ _
    (IntegratedGaugeAction.yang_mills_continuous A DA hAc hDA β) π hπ _ hε
  filter_upwards [hsmall] with r hr
  exact fun x hx => hb x hx (h r) hr.1 hr.2.le

/-- **Canonical normalization.** With `β = 1/g²` and `‖F_{μν}‖²_F = (g²/2) Σ_a (F^a_{μν})²`, the
limit density is the canonical Yang–Mills Lagrangian `(1/4) Σ_{μν a} (F^a_{μν})²`. -/
theorem canonical_density (A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x : V4) {g : ℝ} (hg : g ≠ 0)
    {n : ℕ} (Fa : Fin 4 → Fin 4 → Fin n → ℝ)
    (hF : ∀ μ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2 = g ^ 2 / 2 * ∑ a, Fa μ ν a ^ 2) :
    UniformGaugeAction.yangMillsDensity A DA x (1 / g ^ 2) =
      1 / 4 * ∑ μ, ∑ ν, ∑ a, Fa μ ν a ^ 2 := by
  unfold UniformGaugeAction.yangMillsDensity
  simp only [hF, ← Finset.mul_sum]
  field_simp
  ring

/-- Frobenius norm as a trace. -/
theorem frobenius_eq (X : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i, ∑ j, ‖X i j‖ ^ 2 = (trace (Xᴴ * X)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

/-- **Generator normalization, derived.** For Hermitian generators with
`tr(T^a T^b) = δ^{ab}/2`, a field `F = −i g Σ_a c_a T^a` has `‖F‖²_F = (g²/2) Σ_a c_a²`. -/
theorem generator_norm {n : ℕ} (Tg : Fin n → Matrix (Fin N) (Fin N) ℂ)
    (hherm : ∀ a, (Tg a)ᴴ = Tg a)
    (hnorm : ∀ a b, trace (Tg a * Tg b) = if a = b then (1 / 2 : ℂ) else 0)
    (g : ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, ‖(∑ a, (-(Complex.I * g * c a)) • Tg a) i j‖ ^ 2 = g ^ 2 / 2 * ∑ a, c a ^ 2 := by
  rw [frobenius_eq, conjTranspose_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, conjTranspose_smul, hherm, smul_mul_smul_comm, trace_sum, trace_smul,
    hnorm, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [star_neg, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

/-- **Canonical normalization from the generator basis.** If the field strength is
`F_{μν} = −i g Σ_a F^a_{μν} T^a` with Hermitian `tr(T^a T^b) = δ^{ab}/2` generators, then at
`β = 1/g²` the limit density is the canonical `(1/4) Σ_{μν a} (F^a_{μν})²`. The Frobenius-norm
identity is proved (`generator_norm`), not assumed. -/
theorem canonical_from_generators (A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x : V4) {g : ℝ} (hg : g ≠ 0)
    {n : ℕ} (Tg : Fin n → Matrix (Fin N) (Fin N) ℂ) (hherm : ∀ a, (Tg a)ᴴ = Tg a)
    (hnorm : ∀ a b, trace (Tg a * Tg b) = if a = b then (1 / 2 : ℂ) else 0)
    (Fa : Fin 4 → Fin 4 → Fin n → ℝ)
    (hdec : ∀ μ ν, fieldStrength A DA x μ ν = ∑ a, (-(Complex.I * g * Fa μ ν a)) • Tg a) :
    UniformGaugeAction.yangMillsDensity A DA x (1 / g ^ 2) =
      1 / 4 * ∑ μ, ∑ ν, ∑ a, Fa μ ν a ^ 2 :=
  canonical_density A DA x hg Fa fun μ ν => by
    rw [hdec μ ν]; exact generator_norm Tg hherm hnorm g (Fa μ ν)

end PMAction.ClassicalYangMills
