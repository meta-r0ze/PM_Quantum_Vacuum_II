import PMAction.ParallelTransport
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# PM's D₄ lattice action, summed over actual lattice sites, converges to Yang–Mills

`ClassicalYangMills.pm_lattice_yang_mills` accumulates the per-site Wilson density over arbitrary
refining tagged box partitions, with tags anywhere. That is a Riemann sum of the density, not the
lattice action: nothing tied the sample points to D₄ sites or the weights to the D₄ cell. This file
proves the statement for the lattice itself.

* `d4_sites`: the basis `e₁−e₂, e₂−e₃, e₃−e₄, e₃+e₄` generates exactly the integer vectors with
  even coordinate sum, i.e. D₄; `d4Map_det`: its cell volume is `2`.
* `siteAction U β S n`: `Σ_{y ∈ S ∩ (1/n)D₄} (2/n⁴) · linkDensity U y β (1/n)`, the D₄ Wilson
  action of the region `S` at spacing `1/n`, each site weighted by its cell volume.
* `site_sum_limit`: such cell-weighted sums over the image of `ℤ⁴/n` under a linear isomorphism
  converge to `∫_S g` when the summand converges uniformly to a continuous `g` (Mathlib's lattice
  Riemann-sum theorem plus the linear change of variables).
* `site_action_limit`: for cubically consistent links, `siteAction → ∫_S (β/2) Σ ‖F_{μν}‖²_F`.
* `transport_unitary`: parallel transport of a `u(N)` connection is unitary (derived).
* `d4_yang_mills_action`: **main theorem.** For the parallel-transport links of a `u(N)`
  connection whose derivative is Lipschitz on compact sets (every `C²` connection), the D₄ site
  action of any bounded measurable region with null boundary converges to the classical
  Yang–Mills action. Remaining inputs: the connection, the gauge group, `β`, and that the links are
  its parallel transports (the existence of the transport ODE solution is assumed, not
  constructed). This is a statement about smooth classical fields only.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.LatticeSiteAction
open Matrix Set Filter Topology MeasureTheory Pointwise
open scoped Matrix.Norms.L2Operator

local notation "V4" => (Fin 4 → ℝ)
variable {N : ℕ}

/-- The integer grid at spacing `1/n`. -/
def grid (n : ℕ) : Set V4 :=
  (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4))) : Set V4)

theorem grid_finite (X : Set V4) (hX : Bornology.IsBounded X) (n : ℕ) [NeZero n] :
    (X ∩ grid n).Finite := by
  obtain ⟨C, hC⟩ := hX.exists_norm_le
  set m : ℤ := ⌈(n : ℝ) * C⌉
  have hK : (Set.pi Set.univ fun _ : Fin 4 => Set.Icc (-m) m).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hK.image fun k : Fin 4 → ℤ => (n : ℝ)⁻¹ • (fun i => (k i : ℝ))).subset ?_
  rintro x ⟨hxX, hxg⟩
  have hx := (BoxIntegral.unitPartition.mem_smul_span_iff (v := x)).mp hxg
  choose k hk using hx
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨k, fun i _ => ⟨?_, ?_⟩, ?_⟩
  · have h1 : |x i| ≤ C := (norm_le_pi_norm x i).trans (hC x hxX)
    have h2 : (k i : ℝ) = n * x i := by simpa using hk i
    have h3 : -((n : ℝ) * C) ≤ k i := by rw [h2]; nlinarith [abs_le.mp h1]
    have h4 : -(m : ℝ) ≤ k i := le_trans (by linarith [Int.le_ceil ((n : ℝ) * C)]) h3
    exact_mod_cast h4
  · have h1 : |x i| ≤ C := (norm_le_pi_norm x i).trans (hC x hxX)
    have h2 : (k i : ℝ) = n * x i := by simpa using hk i
    have h3 : (k i : ℝ) ≤ n * C := by rw [h2]; nlinarith [abs_le.mp h1]
    have h4 : (k i : ℝ) ≤ m := h3.trans (Int.le_ceil _)
    exact_mod_cast h4
  · ext i
    have h2 : (k i : ℝ) = n * x i := by simpa using hk i
    simp only [Pi.smul_apply, smul_eq_mul, h2]
    field_simp

/-- Error of a finite sum, by the number of terms. -/
theorem tsum_err {X : Type*} [Finite X] (a b : X → ℝ) (ε : ℝ)
    (h : ∀ x, |a x - b x| ≤ ε) :
    |(∑' x, a x) - ∑' x, b x| ≤ Nat.card X * ε := by
  let _ := Fintype.ofFinite X
  rw [tsum_fintype, tsum_fintype, ← Finset.sum_sub_distrib, Nat.card_eq_fintype_card]
  calc _ ≤ ∑ x, |a x - b x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : X, ε := Finset.sum_le_sum fun x _ => h x
    _ = _ := by simp

/-- **Lattice sums over the image of the integer grid.** For a linear isomorphism `M`, sums of
`f n` over the sites `M x`, `x ∈ ℤ⁴/n`, lying in `S`, weighted by the cell volume `|det M|/n⁴`,
converge to `∫_S g` when `f n → g` uniformly on `S` and `g` is continuous. -/
theorem site_sum_limit (M : V4 ≃L[ℝ] V4) (S : Set V4) (hSb : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hSf : volume (frontier S) = 0) (g : V4 → ℝ) (hg : Continuous g)
    (f : ℕ → V4 → ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hfe : ∀ᶠ n in atTop, ∀ y ∈ S, |f n y - g y| ≤ ε n) :
    Tendsto (fun n : ℕ => |LinearMap.det (M : V4 →ₗ[ℝ] V4)| *
        ((∑' x : ↑(M ⁻¹' S ∩ grid n), f n (M x)) / (n : ℝ) ^ 4)) atTop (𝓝 (∫ y in S, g y)) := by
  set d := LinearMap.det (M : V4 →ₗ[ℝ] V4)
  have hdet : d ≠ 0 := (LinearEquiv.isUnit_det' M.toLinearEquiv).ne_zero
  set S' := M ⁻¹' S
  have hb' : Bornology.IsBounded S' := by
    rw [show S' = M.symm '' S from (M.image_symm_eq_preimage S).symm]
    exact (ContinuousLinearMap.lipschitzWith (M.symm : V4 →L[ℝ] V4)).isBounded_image hSb
  have hm' : MeasurableSet S' := hSm.preimage M.continuous.measurable
  have hf' : volume (frontier S') = 0 := by
    have e : frontier S' = M ⁻¹' frontier S := (M.toHomeomorph.preimage_frontier S).symm
    rw [e, show (⇑M : V4 → V4) = ⇑(M : V4 →ₗ[ℝ] V4) from rfl,
      Measure.addHaar_preimage_linearMap _ hdet, hSf, mul_zero]
  -- main term
  have h1 := tendsto_tsum_div_pow_atTop_integral S' (fun x => g (M x)) (hg.comp M.continuous)
    hb' hm' hf'
  simp only [Fintype.card_fin] at h1
  have hcv : ∫ x in S', g (M x) = |d|⁻¹ * ∫ y in S, g y := by
    have hme : MeasurableEmbedding (⇑M) := M.toHomeomorph.measurableEmbedding
    rw [← hme.setIntegral_map g S,
      show (⇑M : V4 → V4) = ⇑(M : V4 →ₗ[ℝ] V4) from rfl,
      Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.restrict_smul,
      integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]
  -- error term
  have hcard := tendsto_card_div_pow_atTop_volume S' hb' hm' hf'
  simp only [Fintype.card_fin] at hcard
  have herr : Tendsto (fun n : ℕ => ε n * ((Nat.card ↑(S' ∩ grid n) : ℝ) / (n : ℝ) ^ 4)) atTop
      (𝓝 0) := by
    simpa [grid] using hε.mul hcard
  have hD : Tendsto (fun n : ℕ => ((∑' x : ↑(S' ∩ grid n), f n (M x)) -
      ∑' x : ↑(S' ∩ grid n), g (M x)) / (n : ℝ) ^ 4) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [hfe, eventually_ge_atTop 1] with n hn hn1
    have : NeZero n := ⟨by omega⟩
    have : Finite ↑(S' ∩ grid n) := (grid_finite S' hb' n).to_subtype
    have hpos : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, mul_div_assoc', div_le_div_iff_of_pos_right hpos,
      mul_comm]
    exact tsum_err _ _ _ fun x => hn _ x.2.1
  have hsum := (h1.add hD).const_mul |d|
  rw [hcv, add_zero, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_mul] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  simp only [grid]
  ring

/-! ## The D₄ lattice -/

/-- Columns: a basis `e₁−e₂, e₂−e₃, e₃−e₄, e₃+e₄` of D₄. -/
def basisZ : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; -1, 1, 0, 0; 0, -1, 1, 1; 0, 0, -1, 1]

def basisR : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; -1, 1, 0, 0; 0, -1, 1, 1; 0, 0, -1, 1]
def basisInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 1/2, 1/2, 1/2, -1/2; 1/2, 1/2, 1/2, 1/2]

theorem basis_mul_inv : basisR * basisInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [basisR, basisInv, Matrix.mul_apply, Fin.sum_univ_four]
theorem inv_mul_basis : basisInv * basisR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [basisR, basisInv, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The basis generates exactly D₄**: an integer vector is an integer combination of the
columns iff its coordinate sum is even. -/
theorem d4_sites (y : Fin 4 → ℤ) : (∃ k, y = basisZ *ᵥ k) ↔ Even (∑ i, y i) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k 3, ?_⟩
    simp [basisZ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  · rintro ⟨r, hr⟩
    simp only [Fin.sum_univ_four] at hr
    refine ⟨![y 0, y 0 + y 1, r - y 3, r], ?_⟩
    ext i; fin_cases i <;> simp [basisZ, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linarith

theorem basis_det : basisR.det = 2 := by
  simp [basisR, Matrix.det_succ_row_zero, Fin.sum_univ_succ]; norm_num

/-- The D₄ basis map, as a continuous linear isomorphism of `ℝ⁴`. -/
def d4Map : V4 ≃L[ℝ] V4 :=
  (LinearEquiv.ofLinearMap (Matrix.toLin' basisR) (Matrix.toLin' basisInv)
    (by rw [← Matrix.toLin'_mul, basis_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, inv_mul_basis, Matrix.toLin'_one])).toContinuousLinearEquiv

theorem d4Map_det : |LinearMap.det (d4Map : V4 →ₗ[ℝ] V4)| = 2 := by
  have : (d4Map : V4 →ₗ[ℝ] V4) = Matrix.toLin' basisR := rfl
  rw [this, LinearMap.det_toLin', basis_det]; norm_num

theorem d4Map_apply (x : V4) : d4Map x = basisR *ᵥ x := rfl

/-! ## The D₄ site action and its limit -/

/-- **PM's D₄ lattice action on a region `S`**, at spacing `1/n`: the sum of the per-site Wilson
density over the D₄ sites `y ∈ S ∩ (1/n)D₄`, each weighted by the D₄ cell volume `2/n⁴`. The sites
are `d4Map x` for `x ∈ ℤ⁴/n` (`d4_sites`). -/
def siteAction (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (β : ℝ) (S : Set V4) (n : ℕ) : ℝ :=
  2 * ((∑' x : ↑(d4Map ⁻¹' S ∩ grid n), LinkConsistency.linkDensity U (d4Map x) β (1 / n)) /
    (n : ℝ) ^ 4)

/-- **The D₄ site action converges to the Yang–Mills action.** For cubically consistent links of
a `u(N)` connection with the stated local regularity on a compact `s ⊇ S`, the lattice sum over
the actual D₄ sites in `S` converges to `∫_S (β/2) Σ ‖F_{μν}‖²_F`. `S` is any bounded measurable
region with null boundary (a box, a ball, …). -/
theorem site_action_limit {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s S : Set V4} (hs : IsCompact s)
    (hSs : S ⊆ s) (hSm : MeasurableSet S) (hSf : volume (frontier S) = 0)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA) {L K : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ s, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : ∀ x ∈ s, LinkConsistency.CubicConsistent U A x K) (β : ℝ) :
    Tendsto (fun n => siteAction U β S n) atTop
      (𝓝 (∫ y in S, UniformGaugeAction.yangMillsDensity A DA y β)) := by
  obtain ⟨C, hC, hb⟩ :=
    ClassicalYangMills.link_yang_mills_uniform hs hA hDA hL0 hL hskew U hU hK hc β
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hε : Tendsto (fun n : ℕ => C * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul C
  have h := site_sum_limit d4Map S (hs.isBounded.subset hSs) hSm hSf _
    (IntegratedGaugeAction.yang_mills_continuous A DA hAc hDA β)
    (fun n y => LinkConsistency.linkDensity U y β (1 / n)) _ hε (by
      filter_upwards [eventually_ge_atTop 1] with n hn y hy
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact hb y (hSs hy) (1 / n) (by positivity) (by rw [div_le_one (by linarith)]; exact hn'))
  rw [d4Map_det] at h
  exact h

/-- **Parallel transport of a `u(N)` connection is unitary.** `(T T*)' = T B T* + T (−B) T* = 0`,
so `T T* = 1`; in finite dimension this gives `T* T = 1`. Unitarity is derived, not assumed. -/
theorem transport_unitary {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    (hskew : ∀ y v, star (A y v) = -A y v) (T : ℝ → Matrix (Fin N) (Fin N) ℂ) (y v : V4)
    (hT0 : T 0 = 1) (hTd : ∀ s, HasDerivAt T (T s * A (y + s • v) v) s) (s : ℝ) :
    T s ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  have hd : ∀ t, HasDerivAt (fun t => T t * star (T t)) 0 t := by
    intro t
    have h1 := (hTd t).mul (hTd t).star
    convert h1 using 1
    rw [star_mul, hskew]
    noncomm_ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0
  simp only [hT0, star_one, mul_one] at hc
  exact Unitary.mem_iff.mpr ⟨mul_eq_one_comm.mp hc, hc⟩

/-- On a compact region, parallel-transport links of a connection whose derivative is Lipschitz
on compact sets satisfy every hypothesis of `site_action_limit`, with constants found by
compactness. -/
theorem transport_data {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {s : Set V4} (hs : IsCompact s)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    (hLL : ∀ S : Set V4, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ z₁ ∈ S, ∀ z₂ ∈ S, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
      (∀ x ∈ s, ∀ y, ‖y - x‖ ≤ 2 → ‖DA y - DA x‖ ≤ L * ‖y - x‖) ∧
      ∀ x ∈ s, LinkConsistency.CubicConsistent T A x K := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hK : IsCompact (Metric.cthickening 3 s) := hs.cthickening
  obtain ⟨L, hL0, hLip⟩ := hLL _ hK
  obtain ⟨MA, hMA⟩ := hK.exists_bound_of_continuousOn hAc.continuousOn
  have hK2 : IsCompact (Metric.cthickening 3 s ×ˢ Metric.closedBall (0 : V4) 2) :=
    hK.prod (isCompact_closedBall 0 2)
  have hDc : Continuous (fun p : V4 × V4 => DA p.1 p.2 p.2) := by fun_prop
  obtain ⟨MD, hMD⟩ := hK2.exists_bound_of_continuousOn hDc.continuousOn
  have hmem : ∀ x ∈ s, ∀ z, ‖z - x‖ ≤ 3 → z ∈ Metric.cthickening 3 s := fun x hx z hz =>
    Metric.mem_cthickening_of_dist_le z x 3 _ hx (by rw [dist_eq_norm]; exact hz)
  have hMA0 : 0 ≤ max MA 0 := le_max_right _ _
  have hMD0 : 0 ≤ max MD 0 := le_max_right _ _
  refine ⟨L, ParallelTransport.K (max MA 0) (max MD 0) L, hL0,
    by unfold ParallelTransport.K; positivity,
    fun x hx y hy => hLip y (hmem x hx y (by linarith)) x (Metric.self_subset_cthickening _ hx),
    fun x hx => ?_⟩
  exact ParallelTransport.transport_consistent hA hL0 hskew x
    (fun z₁ z₂ h₁ h₂ => hLip z₁ (hmem x hx z₁ h₁) z₂ (hmem x hx z₂ h₂)) hMA0 hMD0
    (fun z hz => (hMA z (hmem x hx z hz)).trans (le_max_left _ _))
    (fun z hz v hv => (hMD (z, v) ⟨hmem x hx z hz, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv⟩).trans (le_max_left _ _))
    T hT0 hTd hTu

/-- **Main theorem: PM's D₄ site action of parallel-transport links converges to the classical
Yang–Mills action.** Links are the parallel transports of a `u(N)` connection whose derivative
is Lipschitz on compact sets (every `C²` connection). Summed over the actual D₄ sites of any
bounded measurable region `S` with null boundary, with the D₄ cell volume `2h⁴`, the Wilson
action converges to `∫_S (β/2) Σ_{μν} ‖F_{μν}‖²_F` as the spacing `h = 1/n → 0`. No partition
choice, cubic-consistency or unitarity hypothesis, or global bound is assumed. -/
theorem d4_yang_mills_action {A : V4 → V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V4 → V4 →L[ℝ] (V4 →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {S : Set V4}
    (hSb : Bornology.IsBounded S) (hSm : MeasurableSet S) (hSf : volume (frontier S) = 0)
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hDA : Continuous DA)
    (hLL : ∀ S : Set V4, IsCompact S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ z₁ ∈ S, ∀ z₂ ∈ S, ‖DA z₁ - DA z₂‖ ≤ L * ‖z₁ - z₂‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s) (β : ℝ) :
    Tendsto (fun n => siteAction T β S n) atTop
      (𝓝 (∫ y in S, UniformGaugeAction.yangMillsDensity A DA y β)) := by
  have hs : IsCompact (closure S) := hSb.isCompact_closure
  have hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := fun y v s =>
    transport_unitary hskew (T y v) y v (hT0 y v) (hTd y v) s
  obtain ⟨L, K, hL0, hK0, hL, hc⟩ := transport_data hs hA hDA hLL hskew T hT0 hTd hTu
  exact site_action_limit hs subset_closure hSm hSf hA hDA hL0 hL hskew T hTu hK0 hc β

end PMAction.LatticeSiteAction
