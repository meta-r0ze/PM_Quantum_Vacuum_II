import PMAction.VaryingFields

/-!
# Robustness of the D₄ gauge-density limit under cubic link consistency

`VaryingFields` proves the pointwise D₄ triangle-density limit for exact midpoint
exponential links. Here the links are an arbitrary family of unitary matrices, one per
directed edge, assumed to be within `K h³` of the midpoint exponentials. The reverse edge
of each triangle uses the adjoint of the forward link. Under that explicit cubic
consistency hypothesis:

* `holonomy_close`: ordered products of three unitaries differ by at most the sum of the
  factor errors;
* `wilson_of_expansion`: a unitary `P` with `P = 1 + h² F' + O(h³)` has
  `Re tr(1 − P)/h⁴ = Σ |F'ᵢⱼ|²/2 + O(h)` (the unitarity identity `2 Re tr(1 − P) = ‖P − 1‖²_F`
  is what prevents losing a power of `h`);
* `triangle_stability`: the actual and midpoint triangle Wilson terms differ by `O(h)` after
  division by `h⁴`;
* `d4_link_stability`, `d4_link_tendsto`: the actual-link D₄ density with prefactor `β/12`
  has the same pointwise limit as `d4_yang_mills_tendsto`;
* `counterexample_*`: constant unitary links `−1` around `A = 0` are unitary but not cubically
  consistent, and their density diverges like `32β/h⁴`.

The consistency hypothesis is not derived. No claim is made that PM selects it, the gauge
group, the trace normalization or `β`, nor that midpoint links are necessary.
-/
noncomputable section
namespace PMAction.LinkConsistency
open Matrix VaryingFields
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-! ## Products of unitaries -/

lemma norm_umul {U A : Matrix (Fin N) (Fin N) ℂ} (hU : U ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    ‖U * A‖ = ‖A‖ := CStarRing.norm_coe_unitary_mul ⟨U, hU⟩ A

lemma norm_mulu {U A : Matrix (Fin N) (Fin N) ℂ} (hU : U ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    ‖A * U‖ = ‖A‖ := CStarRing.norm_mul_coe_unitary A ⟨U, hU⟩

/-- **Holonomy stability.** Ordered products of three unitaries differ by at most the sum
of the factor differences. -/
theorem holonomy_close {U1 U2 U3 V1 V2 V3 : Matrix (Fin N) (Fin N) ℂ}
    (hU2 : U2 ∈ unitary _) (hU3 : U3 ∈ unitary _) (hV1 : V1 ∈ unitary _) (hV2 : V2 ∈ unitary _) :
    ‖U1 * U2 * U3 - V1 * V2 * V3‖ ≤ ‖U1 - V1‖ + ‖U2 - V2‖ + ‖U3 - V3‖ := by
  have e : U1 * U2 * U3 - V1 * V2 * V3 =
      (U1 - V1) * U2 * U3 + V1 * (U2 - V2) * U3 + V1 * V2 * (U3 - V3) := by noncomm_ring
  rw [e]
  have h1 : ‖(U1 - V1) * U2 * U3‖ = ‖U1 - V1‖ := by rw [norm_mulu hU3, norm_mulu hU2]
  have h2 : ‖V1 * (U2 - V2) * U3‖ = ‖U2 - V2‖ := by rw [norm_mulu hU3, norm_umul hV1]
  have h3 : ‖V1 * V2 * (U3 - V3)‖ = ‖U3 - V3‖ := by
    rw [Matrix.mul_assoc, norm_umul hV1, norm_umul hV2]
  calc _ ≤ ‖(U1 - V1) * U2 * U3 + V1 * (U2 - V2) * U3‖ + ‖V1 * V2 * (U3 - V3)‖ := norm_add_le _ _
    _ ≤ ‖(U1 - V1) * U2 * U3‖ + ‖V1 * (U2 - V2) * U3‖ + ‖V1 * V2 * (U3 - V3)‖ := by
        gcongr; exact norm_add_le _ _
    _ = _ := by rw [h1, h2, h3]

/-! ## Wilson term from a second-order expansion -/

/-- **Wilson term of a unitary with a quadratic expansion.** -/
theorem wilson_of_expansion (P F : Matrix (Fin N) (Fin N) ℂ) (hP : star P * P = 1)
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 < h) (h1 : h ≤ 1)
    (he : ‖(P - 1) - h ^ 2 • F‖ ≤ K * h ^ 3) :
    |(trace (1 - P)).re / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 2| ≤
      (N : ℝ) ^ 2 * (K * (2 * ‖F‖ + K)) / 2 * h := by
  have hw := wilson_sum P hP
  have hent : ∀ i j, |‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F i j‖ ^ 2| ≤ K * (2 * ‖F‖ + K) * h := by
    intro i j
    have hij : ‖(P - 1) i j - h ^ 2 • F i j‖ ≤ K * h ^ 3 := by
      have := entry_le ((P - 1) - h ^ 2 • F) i j
      simp only [Matrix.sub_apply, Matrix.smul_apply] at this
      exact this.trans he
    refine (quartic_close hh h1 hK hij).trans ?_
    gcongr
    exact entry_le F i j
  have hre : (trace (1 - P)).re = (∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2) / 2 := by linarith
  rw [hre]
  have key : (∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2) / 2 / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 2 =
      (∑ i, ∑ j, (‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F i j‖ ^ 2)) / 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]; ring
  rw [key, abs_div, abs_two]
  have hs : |∑ i, ∑ j, (‖(P - 1) i j‖ ^ 2 / h ^ 4 - ‖F i j‖ ^ 2)| ≤
      (N : ℝ) ^ 2 * (K * (2 * ‖F‖ + K) * h) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j).trans ?_
    simp [Finset.sum_const, Finset.card_univ]; ring_nf; rfl
  have : (N : ℝ) ^ 2 * (K * (2 * ‖F‖ + K)) / 2 * h = (N : ℝ) ^ 2 * (K * (2 * ‖F‖ + K) * h) / 2 := by
    ring
  rw [this]
  exact div_le_div_of_nonneg_right hs (by norm_num)

/-! ## One triangle -/

/-- Skew-adjoint exponentials are unitary. -/
lemma exp_skew_unitary (X : Matrix (Fin N) (Fin N) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  have he : (NormedSpace.exp X)ᴴ = NormedSpace.exp (-X) := by rw [← Matrix.exp_conjTranspose, hX]
  constructor
  · change (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1
    rw [he, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left]; simp
  · change NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1
    rw [he, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right]; simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smul_skew {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hskew : ∀ y v, star (A y v) = -A y v) (t : ℝ) (y v : E) :
    (t • A y v)ᴴ = -(t • A y v) := by
  rw [conjTranspose_smul, star_trivial, ← Matrix.star_eq_conjTranspose, hskew, smul_neg]

lemma link_unitary {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hskew : ∀ y v, star (A y v) = -A y v) (y v : E) (h : ℝ) :
    link A y v h ∈ unitary _ :=
  exp_skew_unitary _ (smul_skew hskew h _ _)

lemma reverse_unitary {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hskew : ∀ y v, star (A y v) = -A y v) (y v : E) (h : ℝ) :
    NormedSpace.exp (h • -(A y v)) ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  rw [smul_neg]
  exact exp_skew_unitary _ (by rw [conjTranspose_neg, smul_skew hskew])

/-- The reverse factor of `VaryingFields.triangle` is the adjoint of the forward link. -/
lemma reverse_eq {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hskew : ∀ y v, star (A y v) = -A y v) (x b : E) (h : ℝ) :
    (link A x b h)ᴴ = NormedSpace.exp (h • -(A (x + (h / 2) • b) b)) := by
  rw [link, ← Matrix.exp_conjTranspose, smul_skew hskew, smul_neg]

/-- **Triangle Wilson-term stability.** If three unitary factors are each within `K h³` of
the midpoint factors of `VaryingFields.triangle`, the Wilson terms divided by `h⁴` agree
up to `O(h)`, and both converge to `Σ|F(a,b)|²/8`. -/
theorem triangle_stability {A : E → E →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : E → E →L[ℝ] (E →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : E} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (a b : E) (hK : 0 ≤ K)
    (U1 U2 U3 : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hu : ∀ h, U1 h ∈ unitary _ ∧ U2 h ∈ unitary _ ∧ U3 h ∈ unitary _)
    (h1c : ∀ h, 0 < h → h ≤ 1 → ‖U1 h - link A x a h‖ ≤ K * h ^ 3)
    (h2c : ∀ h, 0 < h → h ≤ 1 → ‖U2 h - link A (x + h • a) (b - a) h‖ ≤ K * h ^ 3)
    (h3c : ∀ h, 0 < h → h ≤ 1 →
      ‖U3 h - NormedSpace.exp (h • -(A (x + (h / 2) • b) b))‖ ≤ K * h ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖U1 h * U2 h * U3 h - triangle A x a b h‖ ≤ 3 * K * h ^ 3 ∧
      |(trace (1 - U1 h * U2 h * U3 h)).re / h ^ 4 -
        (∑ i, ∑ j, ‖curvature A DA x a b i j‖ ^ 2) / 8| ≤ C * h ∧
      |(trace (1 - U1 h * U2 h * U3 h)).re / h ^ 4 -
        (trace (1 - triangle A x a b h)).re / h ^ 4| ≤ C * h := by
  obtain ⟨C0, hC0, hb⟩ := triangle_expand hA hL0 hL a b
  obtain ⟨Cm, hCm, hm⟩ := triangle_wilson hA hL0 hL hskew a b
  set F := curvature A DA x a b
  set F' : Matrix (Fin N) (Fin N) ℂ := (1 / 2 : ℝ) • F
  set K' := C0 + 3 * K
  set Ca := (N : ℝ) ^ 2 * (K' * (2 * ‖F'‖ + K')) / 2
  have hCa : 0 ≤ Ca := by positivity
  refine ⟨Ca + Cm, by positivity, fun h hh h1 => ?_⟩
  set P := U1 h * U2 h * U3 h
  obtain ⟨u1, u2, u3⟩ := hu h
  have hclose : ‖P - triangle A x a b h‖ ≤ 3 * K * h ^ 3 := by
    have := holonomy_close (U1 := U1 h) u2 u3 (link_unitary hskew x a h)
      (link_unitary hskew (x + h • a) (b - a) h)
      (V3 := NormedSpace.exp (h • -(A (x + (h / 2) • b) b)))
    refine this.trans ?_
    have := h1c h hh h1; have := h2c h hh h1; have := h3c h hh h1
    linarith
  have hexp : ‖(P - 1) - h ^ 2 • F'‖ ≤ K' * h ^ 3 := by
    have e : (P - 1) - h ^ 2 • F' = (P - triangle A x a b h) +
        (triangle A x a b h - (1 + (h ^ 2 / 2) • F)) := by
      simp only [F', smul_smul]; ring_nf; abel
    rw [e]
    have := hb h hh.le h1
    calc _ ≤ ‖P - triangle A x a b h‖ + ‖triangle A x a b h - (1 + (h ^ 2 / 2) • F)‖ :=
          norm_add_le _ _
      _ ≤ 3 * K * h ^ 3 + C0 * h ^ 3 := add_le_add hclose this
      _ = K' * h ^ 3 := by simp only [K']; ring
  have hPu : star P * P = 1 :=
    (Unitary.mem_iff.mp ((unitary _).mul_mem ((unitary _).mul_mem u1 u2) u3)).1
  have hw := wilson_of_expansion P F' hPu (by positivity) hh h1 hexp
  have hF : (∑ i, ∑ j, ‖F' i j‖ ^ 2) / 2 = (∑ i, ∑ j, ‖F i j‖ ^ 2) / 8 := by
    have : ∀ i j, ‖F' i j‖ ^ 2 = ‖F i j‖ ^ 2 / 4 := fun i j => by
      simp only [F', Matrix.smul_apply, norm_smul]; norm_num; ring
    simp only [this, ← Finset.sum_div]; ring
  rw [hF] at hw
  replace hw : |(trace (1 - P)).re / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 8| ≤ Ca * h := hw
  have hm' := hm h hh h1
  have hCm' : Cm * h ≥ 0 := by positivity
  have hsplit : (Ca + Cm) * h = Ca * h + Cm * h := by ring
  refine ⟨hclose, hw.trans (by linarith), ?_⟩
  calc _ ≤ |(trace (1 - P)).re / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 8| +
        |(∑ i, ∑ j, ‖F i j‖ ^ 2) / 8 - (trace (1 - triangle A x a b h)).re / h ^ 4| :=
        abs_sub_le _ _ _
    _ = |(trace (1 - P)).re / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 8| +
        |(trace (1 - triangle A x a b h)).re / h ^ 4 - (∑ i, ∑ j, ‖F i j‖ ^ 2) / 8| := by
        rw [abs_sub_comm ((∑ i, ∑ j, ‖F i j‖ ^ 2) / 8)]
    _ ≤ Ca * h + Cm * h := add_le_add hw hm'
    _ = (Ca + Cm) * h := by ring

/-! ## One shared directed-edge family on the D₄ triangles -/

section D4
abbrev V := Fin 4 → ℝ

/-- Holonomy of `x → x+ha → x+hb → x` from a directed-edge link family: `U y v h` is the
link from `y` to `y + h v`, and the closing edge uses the adjoint of the forward link
`x → x + h b`. The middle edge is the link based at `x + h a`. -/
def holonomy (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x a b : V) (h : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  U x a h * U (x + h • a) (b - a) h * (U x b h)ᴴ

/-- Per-site D₄ density from the actual links, with the same `β/12` prefactor. -/
def linkDensity (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x : V) (β h : ℝ) : ℝ :=
  (β / 12) * ∑ p ∈ D4Gauge.tri, (trace (1 - holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4

/-- **Cubic consistency** of the link family with midpoint exponentials, on the edges
based within distance one of `x` with direction of norm at most two (sup norm). -/
def CubicConsistent (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (x : V) (K : ℝ) : Prop :=
  ∀ y v h, 0 < h → h ≤ 1 → ‖y - x‖ ≤ 1 → ‖v‖ ≤ 2 → ‖U y v h - link A y v h‖ ≤ K * h ^ 3

lemma rv_norm (k : Fin 4 → Fin 3) : ‖rv k‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  simp only [rv, D4Gauge.vec, Real.norm_eq_abs]
  generalize k i = m
  fin_cases m <;> norm_num

/-- **Robustness of the D₄ density.** Unitary links that are cubically consistent give the
same density as the midpoint links up to `O(h)`. -/
theorem d4_link_stability {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |linkDensity U x β h - d4Density A x β h| ≤ C * h := by
  have hp : ∀ p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3), ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (1 - holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        (trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4| ≤ C * h := by
    intro p
    have ha := rv_norm p.1
    have hb := rv_norm p.2
    have hba : ‖rv p.2 - rv p.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    obtain ⟨C, hC, hs⟩ := triangle_stability hA hL0 hL hskew (rv p.1) (rv p.2) hK
      (fun h => U x (rv p.1) h) (fun h => U (x + h • rv p.1) (rv p.2 - rv p.1) h)
      (fun h => (U x (rv p.2) h)ᴴ)
      (fun h => ⟨hU _ _ _, hU _ _ _, Unitary.star_mem (hU _ _ _)⟩)
      (fun h hh h1 => hc _ _ h hh h1 (by simp) (by linarith))
      (fun h hh h1 => hc _ _ h hh h1 (by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
        nlinarith [norm_nonneg (rv p.1)]) hba)
      (fun h hh h1 => by
        rw [← reverse_eq hskew, ← conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
        exact hc _ _ h hh h1 (by simp) (by linarith))
    exact ⟨C, hC, fun h hh h1 => (hs h hh h1).2.2⟩
  choose C hC0 hCb using hp
  refine ⟨|β| / 12 * ∑ p ∈ D4Gauge.tri, C p,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => hC0 p), fun h hh h1 => ?_⟩
  have e : linkDensity U x β h - d4Density A x β h = (β / 12) * ∑ p ∈ D4Gauge.tri,
      ((trace (1 - holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        (trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4) := by
    rw [linkDensity, d4Density, Finset.sum_sub_distrib, mul_sub]
  rw [e, abs_mul, show |β / 12| = |β| / 12 by rw [abs_div]; norm_num]
  have hs : |∑ p ∈ D4Gauge.tri,
      ((trace (1 - holonomy U x (rv p.1) (rv p.2) h)).re / h ^ 4 -
        (trace (1 - triangle A x (rv p.1) (rv p.2) h)).re / h ^ 4)| ≤
      (∑ p ∈ D4Gauge.tri, C p) * h := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hCb p h hh h1)
  calc |β| / 12 * |_| ≤ |β| / 12 * ((∑ p ∈ D4Gauge.tri, C p) * h) := by gcongr
    _ = _ := by ring

/-- **Same pointwise limit.** The actual-link density has the limit of
`VaryingFields.d4_yang_mills_tendsto`. -/
theorem d4_link_tendsto {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (β : ℝ) :
    Filter.Tendsto (fun h => linkDensity U x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := d4_link_stability hA hL0 hL hskew U hU hK hc β
  have hlim := d4_yang_mills_tendsto hA hL0 hL hskew β
  have hCh : Filter.Tendsto (fun h : ℝ => C * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun h : ℝ => C * h) := by fun_prop
    have := (hcont.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hd : Filter.Tendsto (fun h => linkDensity U x β h - d4Density A x β h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hCh
    have h1 : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [h1] with h hh
    rw [Real.norm_eq_abs]
    exact hb h hh.1 hh.2.le
  have := hlim.add hd
  simpa using this

/-! ## Unitarity alone is not enough -/

/-- Zero potential on one internal mode. -/
def zeroA : V → V →L[ℝ] Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0

/-- Constant link `−1` on every directed edge. -/
def flipLinks : V → V → ℝ → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ _ => -1

theorem flip_unitary (y v : V) (h : ℝ) : flipLinks y v h ∈ unitary (Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [Unitary.mem_iff]; simp [flipLinks]

lemma link_zero (y v : V) (h : ℝ) : link zeroA y v h = 1 := by
  simp [link, zeroA]

/-- **Not cubically consistent:** for every constant `K`, some edge violates the bound. -/
theorem flip_not_consistent (x : V) (K : ℝ) : ¬ CubicConsistent flipLinks zeroA x K := by
  intro hc
  set h : ℝ := 1 / (|K| + 2)
  have hpos : 0 < h := by positivity
  have hh2 : h ≤ 1 / 2 := by
    simp only [h]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [abs_nonneg K]
  have hb := hc x 0 h hpos (by linarith) (by simp) (by simp)
  rw [link_zero] at hb
  have h2 : (2 : ℝ) ≤ ‖flipLinks x 0 h - 1‖ := by
    have := entry_le (flipLinks x 0 h - 1) 0 0
    have e : (flipLinks x 0 h - 1) 0 0 = -2 := by simp [flipLinks]; norm_num
    rw [e] at this
    simpa using this
  have hk : K * h ^ 3 < 2 := by
    have h3 : h ^ 3 ≤ h := by
      have : h ^ 3 = h * h ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg h]
    have : |K| * h < 1 := by
      simp only [h]; rw [mul_one_div, div_lt_one (by positivity)]; linarith
    calc K * h ^ 3 ≤ |K| * h ^ 3 := by gcongr; exact le_abs_self K
      _ ≤ |K| * h := by gcongr
      _ < 2 := by linarith
  linarith

/-- The constant flip links have Wilson density `32 β / h⁴`. -/
theorem flip_density (x : V) (β h : ℝ) : linkDensity flipLinks x β h = 32 * β / h ^ 4 := by
  have hhol : ∀ a b : V, holonomy flipLinks x a b h = -1 := by
    intro a b; simp [holonomy, flipLinks]
  simp only [linkDensity, hhol]
  have htr : (trace (1 - (-1 : Matrix (Fin 1) (Fin 1) ℂ))).re = 2 := by
    simp [trace]; norm_num
  rw [htr, Finset.sum_const, D4Gauge.tri_card]
  norm_num; ring

/-- The midpoint density of the zero potential vanishes identically. -/
theorem zero_density (x : V) (β h : ℝ) : d4Density zeroA x β h = 0 := by
  simp [d4Density, triangle, link, zeroA]

/-- **Unitary link data alone do not give a finite continuum density.** For `β ≠ 0` the
flip-link density is unbounded as `h → 0⁺`, while the zero-potential density is `0`. -/
theorem flip_unbounded (x : V) (β : ℝ) (hβ : β ≠ 0) (M : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ M < |linkDensity flipLinks x β h| := by
  have hb : 0 < |β| := abs_pos.mpr hβ
  set h : ℝ := min 1 (32 * |β| / (|M| + 1))
  have hpos : 0 < h := lt_min one_pos (by positivity)
  have h1 : h ≤ 1 := min_le_left _ _
  refine ⟨h, hpos, h1, ?_⟩
  rw [flip_density, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32),
    abs_of_pos (by positivity : 0 < h ^ 4)]
  have h4 : h ^ 4 ≤ h := by
    have : h ^ 4 = h * h ^ 3 := by ring
    rw [this]
    nlinarith [pow_le_one₀ hpos.le h1 (n := 3), pow_nonneg hpos.le 3]
  have hle : h ≤ 32 * |β| / (|M| + 1) := min_le_right _ _
  have key : |M| + 1 ≤ 32 * |β| / h := by
    rw [le_div_iff₀ hpos]
    rw [le_div_iff₀ (by positivity)] at hle
    linarith
  calc M ≤ |M| := le_abs_self M
    _ < |M| + 1 := by linarith
    _ ≤ 32 * |β| / h := key
    _ ≤ 32 * |β| / h ^ 4 := div_le_div_of_nonneg_left (by positivity) (by positivity) h4

end D4

end PMAction.LinkConsistency
