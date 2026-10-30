import PMAction.ReferenceSampling

/-!
# Event-priced scalar transport and its continuum limit on D₄

The scalar is read like a gauge link (Paper II `CommonResponse.linkFlag`): a directed root
link at `x` compares the transported packet `U Φ(x + hv)` with `Φ(x)`. The flag
`Σ|(UΦ(x + hv) − Φ(x))ᵢ|²/4` is repaired by `m` events at the common toll, and each
undirected link is counted once per D₄ cell volume (weight `1/4` on the 24 directed roots).

* `taylor_vec`, `quadratic_close`: the generic first-order estimates.
* `link_first`: midpoint links are `1 + h A_v(x) + O(h²)`.
* `covariant_expand`: links within `K h³` of the midpoint links give
  `UΦ(x + hv) − Φ(x) = h(∂_v + A_v)Φ(x) + O(h²)`.
* `root_moment`, `complex_moment`: `Σ_{roots} k_μ k_ν = 12 δ_{μν}`.
* `scalar_limit`: with cubically consistent links of a `C^{1,1}` connection and a `C^{1,1}`
  column field, the event-priced scalar density converges to
  `Z_φ Σ_μ ‖(∂_μ + A_μ)Φ(x)‖²` with `Z_φ = (3/4)·toll·m`.
* `scalar_canonical`: `√Z_φ Φ` is the canonically normalized field.

Premises: event pricing of scalar links with the common toll and repair length, the link
weight `1/4`, `C^{1,1}` regularity and cubic link consistency. No potential, VEV or budget
is derived here.
-/

noncomputable section
namespace PMAction.ScalarTransport
open Matrix VaryingFields LinkConsistency CommonResponse ReferenceSampling
open scoped Matrix.Norms.L2Operator

/-! ## Generic estimates -/

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First-order Taylor bound for a vector-valued field with Lipschitz derivative at `x`. -/
theorem taylor_vec {Φ : E → F} {DΦ : E → E →L[ℝ] F} {x w : E} {L t : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DΦ y - DΦ x‖ ≤ L * ‖y - x‖) (ht : 0 ≤ t) :
    ‖Φ (x + t • w) - Φ x - t • DΦ x w‖ ≤ L * ‖w‖ ^ 2 * t ^ 2 := by
  set g : ℝ → F := fun s => Φ (x + s • w) - s • DΦ x w with hgdef
  have hg : ∀ s, HasDerivAt g (DΦ (x + s • w) w - DΦ x w) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add x
    have h1 := (hΦ (x + s • w)).comp_hasDerivAt s hl
    have h2 : HasDerivAt (fun s : ℝ => s • DΦ x w) (DΦ x w) s := by
      simpa using (hasDerivAt_id s).smul_const (DΦ x w)
    exact h1.sub h2
  have hb : ∀ s ∈ Set.Ico 0 t, ‖DΦ (x + s • w) w - DΦ x w‖ ≤ L * ‖w‖ ^ 2 * t := by
    intro s hs
    have heq : DΦ (x + s • w) w - DΦ x w = (DΦ (x + s • w) - DΦ x) w := by simp
    rw [heq]
    have hs' : ‖s • w‖ ≤ t * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
    calc _ ≤ ‖DΦ (x + s • w) - DΦ x‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * (t * ‖w‖)) * ‖w‖ := by
          gcongr
          exact (hL _).trans (by simpa using mul_le_mul_of_nonneg_left hs' hL0)
      _ = L * ‖w‖ ^ 2 * t := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := t)
    (fun s _ => (hg s).hasDerivWithinAt) hb t ⟨ht, le_rfl⟩
  have e : g t - g 0 = Φ (x + t • w) - Φ x - t • DΦ x w := by
    simp only [hgdef, zero_smul, add_zero, sub_zero]; abel
  rw [e] at this
  calc _ ≤ L * ‖w‖ ^ 2 * t * (t - 0) := this
    _ = _ := by ring

/-- Squared-norm stability at first order: `‖Δ − h D‖ ≤ C h²` gives
`|‖Δ‖²/h² − ‖D‖²| ≤ C(2‖D‖ + C) h`. -/
theorem quadratic_close {Δ D : F} {C h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hC : 0 ≤ C)
    (hΔ : ‖Δ - h • D‖ ≤ C * h ^ 2) :
    |‖Δ‖ ^ 2 / h ^ 2 - ‖D‖ ^ 2| ≤ C * (2 * ‖D‖ + C) * h := by
  set e := h⁻¹ • (Δ - h • D)
  have he : ‖e‖ ≤ C * h := by
    simp only [e, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh]
    rw [inv_mul_le_iff₀ hh]
    calc _ ≤ C * h ^ 2 := hΔ
      _ = h * (C * h) := by ring
  have hΔ' : Δ = h • (D + e) := by
    simp only [e, smul_add, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]; abel
  have hn : ‖Δ‖ ^ 2 / h ^ 2 = ‖D + e‖ ^ 2 := by
    rw [hΔ', norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  rw [hn]
  have t1 := norm_add_le D e
  have t2 : ‖D‖ ≤ ‖D + e‖ + ‖e‖ := by
    have := norm_sub_le (D + e) e; simpa using this
  have hne : 0 ≤ ‖e‖ := norm_nonneg _
  have hCh : C * h ≤ C := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg D, norm_nonneg (D + e)]

end Generic

/-! ## Links and covariant differences -/

variable {N : ℕ}
abbrev V := Fin 4 → ℝ
/-- Column packets of the scalar field. -/
abbrev Col (N : ℕ) := Matrix (Fin N) (Fin 1) ℂ

/-- **First-order link expansion.** A midpoint link is `1 + h A(x)v + O(h²)`. -/
theorem link_first {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖) (v : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖link A x v h - (1 + h • A x v)‖ ≤ C * h ^ 2 := by
  obtain ⟨D0, hD0d⟩ : ∃ D, D = ‖DA x v v‖ + L * ‖v‖ ^ 3 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D0 := by rw [hD0d]; positivity
  obtain ⟨M, hMd⟩ : ∃ M, M = ‖A x v‖ + D0 := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMd]; positivity
  refine ⟨M ^ 2 / 2 + M ^ 3 * Real.exp M + D0, by positivity, fun h h0 h1 => ?_⟩
  set c := A (x + (h / 2) • v) v
  have ht : 0 ≤ h / 2 := by positivity
  have tap := taylor_apply (w := v) hA hL0 hL ht v
  have hcA : ‖c - A x v‖ ≤ D0 * h := by
    have e : c - A x v = (c - A x v - (h / 2) • DA x v v) + (h / 2) • DA x v v := by abel
    rw [e]
    have h2 : ‖(h / 2) • DA x v v‖ ≤ h * ‖DA x v v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]; nlinarith [norm_nonneg (DA x v v)]
    have h3 : L * ‖v‖ ^ 2 * ‖v‖ * (h / 2) ^ 2 ≤ L * ‖v‖ ^ 3 * h := by
      have : (h / 2) ^ 2 ≤ h := by nlinarith
      calc L * ‖v‖ ^ 2 * ‖v‖ * (h / 2) ^ 2 = (L * ‖v‖ ^ 3) * (h / 2) ^ 2 := by ring
        _ ≤ (L * ‖v‖ ^ 3) * h := by gcongr
    have := norm_add_le (c - A x v - (h / 2) • DA x v v) ((h / 2) • DA x v v)
    rw [hD0d]; nlinarith
  have hc : ‖c‖ ≤ M := by
    have := norm_le_insert' c (A x v)
    have hDh : D0 * h ≤ D0 := by nlinarith
    rw [hMd]; linarith
  set z := h • c
  have hz : ‖z‖ ≤ h * M := by
    simp only [z]; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]; gcongr
  have hz1 : ‖z‖ ≤ M := hz.trans (by nlinarith)
  have hex := exp_second z
  have hz2 : ‖z ^ 2‖ ≤ ‖z‖ ^ 2 := norm_pow_le' z (by norm_num)
  have e1 : link A x v h - (1 + h • A x v) =
      (NormedSpace.exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)) + (1 / 2 : ℝ) • z ^ 2 +
        h • (c - A x v) := by
    simp only [link, z, c, smul_sub]; abel
  rw [e1]
  have b1 : ‖NormedSpace.exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)‖ ≤ M ^ 3 * Real.exp M * h ^ 2 := by
    refine hex.trans ?_
    calc ‖z‖ ^ 3 * Real.exp ‖z‖ ≤ (h * M) ^ 3 * Real.exp M := by gcongr
      _ = M ^ 3 * Real.exp M * h ^ 2 * h := by ring
      _ ≤ M ^ 3 * Real.exp M * h ^ 2 * 1 := by gcongr
      _ = _ := by ring
  have b2 : ‖(1 / 2 : ℝ) • z ^ 2‖ ≤ M ^ 2 / 2 * h ^ 2 := by
    rw [norm_smul]
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]
    calc 1 / 2 * ‖z ^ 2‖ ≤ 1 / 2 * (h * M) ^ 2 := by
          gcongr; exact hz2.trans (pow_le_pow_left₀ (norm_nonneg _) hz 2)
      _ = _ := by ring
  have b3 : ‖h • (c - A x v)‖ ≤ D0 * h ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    calc h * ‖c - A x v‖ ≤ h * (D0 * h) := by gcongr
      _ = _ := by ring
  have := norm_add_le ((NormedSpace.exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)) + (1 / 2 : ℝ) • z ^ 2)
    (h • (c - A x v))
  have := norm_add_le (NormedSpace.exp z - (1 + z + (1 / 2 : ℝ) • z ^ 2)) ((1 / 2 : ℝ) • z ^ 2)
  have ex : (M ^ 2 / 2 + M ^ 3 * Real.exp M + D0) * h ^ 2 =
      M ^ 3 * Real.exp M * h ^ 2 + M ^ 2 / 2 * h ^ 2 + D0 * h ^ 2 := by ring
  linarith

/-- **Covariant difference.** For a `C^{1,1}` column field `Φ` and a link within `K h³` of the
midpoint link, `U Φ(x + h v) − Φ(x) = h (∂_v Φ + A_v Φ)(x) + O(h²)`. -/
theorem covariant_expand {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (v : V) (U : ℝ → Matrix (Fin N) (Fin N) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hU : ∀ h, 0 < h → h ≤ 1 → ‖U h - link A x v h‖ ≤ K * h ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖(U h * Φ (x + h • v) - Φ x) - h • (DΦ x v + A x v * Φ x)‖ ≤ C * h ^ 2 := by
  obtain ⟨C1, hC1, hl⟩ := link_first hA hL0 hL v
  obtain ⟨B1, hB1d⟩ : ∃ B, B = ‖DΦ x v‖ + LΦ * ‖v‖ ^ 2 := ⟨_, rfl⟩
  have hB1 : 0 ≤ B1 := by rw [hB1d]; positivity
  obtain ⟨B2, hB2d⟩ : ∃ B, B = ‖Φ x‖ + B1 := ⟨_, rfl⟩
  have hB2 : 0 ≤ B2 := by rw [hB2d]; positivity
  refine ⟨(K + C1) * B2 + LΦ * ‖v‖ ^ 2 + ‖A x v‖ * B1, by positivity, fun h hh h1 => ?_⟩
  set P := Φ (x + h • v)
  have tv := taylor_vec (w := v) hΦ hLΦ0 hLΦ hh.le
  have hP1 : ‖P - Φ x‖ ≤ h * B1 := by
    have e : P - Φ x = (P - Φ x - h • DΦ x v) + h • DΦ x v := by abel
    rw [e]
    have := norm_add_le (P - Φ x - h • DΦ x v) (h • DΦ x v)
    have h2 : ‖h • DΦ x v‖ = h * ‖DΦ x v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have h3 : LΦ * ‖v‖ ^ 2 * h ^ 2 ≤ LΦ * ‖v‖ ^ 2 * h := by
      have : h ^ 2 ≤ h := by nlinarith
      gcongr
    rw [hB1d]; nlinarith
  have hP2 : ‖P‖ ≤ B2 := by
    have := norm_le_insert' P (Φ x)
    have : h * B1 ≤ B1 := by nlinarith
    rw [hB2d]; linarith
  have hU1 : ‖U h - (1 + h • A x v)‖ ≤ (K + C1) * h ^ 2 := by
    have e : U h - (1 + h • A x v) = (U h - link A x v h) + (link A x v h - (1 + h • A x v)) := by
      abel
    rw [e]
    have := norm_add_le (U h - link A x v h) (link A x v h - (1 + h • A x v))
    have := hU h hh h1
    have := hl h hh.le h1
    have : K * h ^ 3 ≤ K * h ^ 2 := by
      have : h ^ 3 ≤ h ^ 2 := by nlinarith
      gcongr
    nlinarith
  have e : (U h * P - Φ x) - h • (DΦ x v + A x v * Φ x) =
      (U h - (1 + h • A x v)) * P + (P - Φ x - h • DΦ x v) + h • (A x v * (P - Φ x)) := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
      smul_add, smul_sub]
    abel
  rw [e]
  have t1 : ‖(U h - (1 + h • A x v)) * P‖ ≤ (K + C1) * h ^ 2 * B2 :=
    (l2_opNorm_mul _ _).trans (mul_le_mul hU1 hP2 (norm_nonneg _) (by positivity))
  have t3 : ‖h • (A x v * (P - Φ x))‖ ≤ ‖A x v‖ * B1 * h ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    calc h * ‖A x v * (P - Φ x)‖ ≤ h * (‖A x v‖ * (h * B1)) := by
          gcongr; exact (l2_opNorm_mul _ _).trans (by gcongr)
      _ = _ := by ring
  have := norm_add_le ((U h - (1 + h • A x v)) * P + (P - Φ x - h • DΦ x v))
    (h • (A x v * (P - Φ x)))
  have := norm_add_le ((U h - (1 + h • A x v)) * P) (P - Φ x - h • DΦ x v)
  have ex : ((K + C1) * B2 + LΦ * ‖v‖ ^ 2 + ‖A x v‖ * B1) * h ^ 2 =
      (K + C1) * h ^ 2 * B2 + LΦ * ‖v‖ ^ 2 * h ^ 2 + ‖A x v‖ * B1 * h ^ 2 := by ring
  linarith

/-! ## The event-priced scalar action on D₄ -/

/-- Second moment of the 24 D₄ roots: `Σ_k k_μ k_ν = 12 δ_{μν}`. -/
lemma root_moment_int : ∀ μ ν : Fin 4, (∑ k ∈ D4Gauge.roots, D4Gauge.vec k μ * D4Gauge.vec k ν) =
    if μ = ν then 12 else 0 := by decide +kernel

lemma root_moment (μ ν : Fin 4) : (∑ k ∈ D4Gauge.roots, rv k μ * rv k ν) =
    if μ = ν then 12 else 0 := by
  have := congrArg (fun z : ℤ => (z : ℝ)) (root_moment_int μ ν)
  push_cast at this
  simpa [rv] using this

lemma quad_moment (y : Fin 4 → ℝ) :
    (∑ k ∈ D4Gauge.roots, (∑ μ, rv k μ * y μ) ^ 2) = 12 * ∑ μ, y μ ^ 2 := by
  have e : ∀ k, (∑ μ, rv k μ * y μ) ^ 2 = ∑ μ, ∑ ν, (rv k μ * rv k ν) * (y μ * y ν) := by
    intro k; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
  simp only [e]
  calc (∑ k ∈ D4Gauge.roots, ∑ μ, ∑ ν, (rv k μ * rv k ν) * (y μ * y ν))
      = ∑ μ, ∑ ν, ∑ k ∈ D4Gauge.roots, (rv k μ * rv k ν) * (y μ * y ν) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ μ, ∑ ν, (∑ k ∈ D4Gauge.roots, rv k μ * rv k ν) * (y μ * y ν) := by
        simp only [Finset.sum_mul]
    _ = 12 * ∑ μ, y μ ^ 2 := by
        simp only [root_moment, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring

lemma complex_moment (z : Fin 4 → ℂ) :
    (∑ k ∈ D4Gauge.roots, ‖∑ μ, ((rv k μ : ℝ) : ℂ) * z μ‖ ^ 2) = 12 * ∑ μ, ‖z μ‖ ^ 2 := by
  have e : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp only [e, Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Finset.sum_add_distrib, quad_moment, mul_add]

/-- The covariant derivative `∂_v Φ + A_v Φ` at `x`. -/
def covD (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N) (DΦ : V → V →L[ℝ] Col N)
    (x v : V) : Col N := DΦ x v + A x v * Φ x

lemma covD_expand (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (x v : V) (i : Fin N) :
    covD A Φ DΦ x v i 0 = ∑ μ, ((v μ : ℝ) : ℂ) * covD A Φ DΦ x (basis μ) i 0 := by
  conv_lhs => rw [vec_expand v]
  simp only [covD, map_sum, map_smul, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, mul_add,
    Finset.sum_add_distrib]

/-- Event-priced scalar density: every directed root link at `x` is a readout flag
`Σ|(UΦ(x + hv) − Φ(x))ᵢ|²/4` repaired by `m` events at the common toll; the weight `1/4` counts
each undirected link once (`1/2`) per D₄ cell volume (`2`). -/
def scalarDensity (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N) (x : V)
    (toll : ℝ) (m : ℕ) (h : ℝ) : ℝ :=
  (1 / 4) * ∑ k ∈ D4Gauge.roots,
    toll * m * ((∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / 4) / h ^ 2

/-- **Scalar continuum limit.** For a `C^{1,1}` connection and column field, with links
cubically consistent at `x`, the event-priced scalar density converges to
`(3/4)·toll·m · Σ_μ ‖(∂_μ + A_μ)Φ(x)‖²`. -/
theorem scalar_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hK : 0 ≤ K) (hc : CubicConsistent U A x K)
    (toll : ℝ) (m : ℕ) :
    Filter.Tendsto (fun h => scalarDensity U Φ x toll m h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (3 / 4 * (toll * m) * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2)) := by
  -- per-root expansion
  have hroot : ∀ k : Fin 4 → Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
        ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2| ≤ C * h := by
    intro k
    obtain ⟨C, hC, hb⟩ := covariant_expand hA hL0 hL hΦ hLΦ0 hLΦ (rv k) (fun h => U x (rv k) h) hK
      (fun h hh h1 => hc x (rv k) h hh h1 (by simp) ((rv_norm k).trans (by norm_num)))
    refine ⟨N * (C * (2 * ‖covD A Φ DΦ x (rv k)‖ + C)), by positivity, fun h hh h1 => ?_⟩
    have hent : ∀ i, |‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2 / h ^ 2 -
        ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2| ≤ C * (2 * ‖covD A Φ DΦ x (rv k)‖ + C) * h := by
      intro i
      have hi : ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0 -
          h • covD A Φ DΦ x (rv k) i 0‖ ≤ C * h ^ 2 := by
        have := entry_le' ((U x (rv k) h * Φ (x + h • rv k) - Φ x) -
          h • covD A Φ DΦ x (rv k)) i 0
        simp only [Matrix.sub_apply, Matrix.smul_apply] at this
        exact this.trans (hb h hh h1)
      refine (quadratic_close hh h1 hC hi).trans ?_
      gcongr
      exact entry_le' _ i 0
    have e2 : (∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
        ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2 =
        ∑ i, (‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2 / h ^ 2 -
          ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    rw [e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hent i).trans ?_
    simp [Finset.sum_const, Finset.card_univ]; ring_nf; rfl
  choose C hC0 hCb using hroot
  -- the root sum of the limits
  have hmom : (∑ k ∈ D4Gauge.roots, ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) =
      12 * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2 := by
    simp only [covD_expand A Φ DΦ x (rv _)]
    rw [Finset.sum_comm]
    simp only [complex_moment, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  set T := toll * m
  have hbound : ∀ h, 0 < h → h ≤ 1 → |scalarDensity U Φ x toll m h -
      3 / 4 * T * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2| ≤
      (|T| / 16 * ∑ k ∈ D4Gauge.roots, C k) * h := by
    intro h hh h1
    have e : scalarDensity U Φ x toll m h - 3 / 4 * T * ∑ μ, ∑ i,
        ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2 = (T / 16) * ∑ k ∈ D4Gauge.roots,
          ((∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
            ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2) := by
      have hA1 : scalarDensity U Φ x toll m h = T / 16 * ∑ k ∈ D4Gauge.roots,
          (∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 := by
        rw [scalarDensity, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp only [T]; ring
      have hA2 : 3 / 4 * T * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2 =
          T / 16 * ∑ k ∈ D4Gauge.roots, ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2 := by
        rw [hmom]; ring
      rw [hA1, hA2, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [e, abs_mul, show |T / 16| = |T| / 16 by rw [abs_div]; norm_num]
    have hs : |∑ k ∈ D4Gauge.roots,
        ((∑ i, ‖(U x (rv k) h * Φ (x + h • rv k) - Φ x : Col N) i 0‖ ^ 2) / h ^ 2 -
          ∑ i, ‖covD A Φ DΦ x (rv k) i 0‖ ^ 2)| ≤ (∑ k ∈ D4Gauge.roots, C k) * h := by
      rw [Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hCb k h hh h1)
    calc |T| / 16 * |_| ≤ |T| / 16 * ((∑ k ∈ D4Gauge.roots, C k) * h) := by gcongr
      _ = _ := by ring
  set Ct := |T| / 16 * ∑ k ∈ D4Gauge.roots, C k
  have hCt : Filter.Tendsto (fun h : ℝ => Ct * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun h : ℝ => Ct * h) := by fun_prop
    have := (hcont.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hCt
  have h1 : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [h1] with h hh
  rw [Real.norm_eq_abs]
  exact hbound h hh.1 hh.2.le

/-- The covariant derivative is linear in the field. -/
lemma covD_smul (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (c : ℝ) (x v : V) :
    covD A (fun y => c • Φ y) (fun y => c • DΦ y) x v = c • covD A Φ DΦ x v := by
  simp only [covD, _root_.smul_apply, Matrix.mul_smul, smul_add]

/-- **Canonical scalar field.** The limit `Z_φ Σ‖(∂+A)Φ‖²` with `Z_φ = (3/4)·toll·m ≥ 0` is the
canonical kinetic term of the rescaled field `√Z_φ Φ`. -/
theorem scalar_canonical (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (Φ : V → Col N)
    (DΦ : V → V →L[ℝ] Col N) (x : V) {T : ℝ} (hT : 0 ≤ T) :
    3 / 4 * T * ∑ μ, ∑ i, ‖covD A Φ DΦ x (basis μ) i 0‖ ^ 2 =
      ∑ μ, ∑ i, ‖covD A (fun y => Real.sqrt (3 / 4 * T) • Φ y)
        (fun y => Real.sqrt (3 / 4 * T) • DΦ y) x (basis μ) i 0‖ ^ 2 := by
  simp only [covD_smul, Matrix.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3 / 4 * T), Finset.mul_sum]

end PMAction.ScalarTransport
