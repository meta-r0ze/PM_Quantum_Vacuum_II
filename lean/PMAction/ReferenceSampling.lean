import PMAction.LinkConsistency
import PMAction.CommonResponse

/-!
# Reference-sampled event pricing of the D₄ gauge action

Paper II's common readout compares a transported state with its reference. Here the
refreshes of a gauge sector read an orthonormal set of `r` reference states, the columns of
an isometry `E`, instead of a uniform basis sample.

* `ref_flag`: the mean reference flag of a unitary holonomy `P` is `Re tr(Eᴴ(1 − P)E)/(2r)`.
* `ref_wilson`: `Σ|((P − 1)E)ᵢₖ|² = 2 Re tr(Eᴴ(1 − P)E)` for unitary `P` (any `E`).
* `ref_of_expansion`: a quadratic expansion `P = 1 + h² F + O(h³)` gives
  `Re tr(Eᴴ(1 − P)E)/h⁴ = Σ|(F E)ᵢₖ|²/2 + O(h)`.
* `triangle_ref`, `ref_limit`: for cubically consistent unitary links of a `C^{1,1}` `u(N)`
  connection, the reference-sampled D₄ density with `W` refreshes converges to
  `(toll·m·W/(4r)) Σ_{μν} ‖F_{μν} E‖²_F`.
* `ref_generators`: if `tr(Eᴴ Tᵃ Tᵇ E) = κ_R δᵃᵇ`, then `‖(g Σ_a f_a iTᵃ)E‖²_F = κ_R g² Σ_a f_a²`.

So the continuum stiffness of a refresh is the **reference's own response index** `κ_R`
times the ledger, not the packet trace. The pricing by the common readout, the reference
states, `W` and cubic link consistency are premises.
-/

noncomputable section
namespace PMAction.ReferenceSampling
open Matrix VaryingFields LinkConsistency CommonResponse
open scoped Matrix.Norms.L2Operator

variable {N r : ℕ}

/-! ## Readout flags on a reference subspace -/

/-- Mean readout flag over the `r` orthonormal reference states (columns of `E`). -/
def refFlag (E : Matrix (Fin N) (Fin r) ℂ) (P : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (∑ k, stateFlag P (fun i => E i k)) / r

lemma col_nsq (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) (k : Fin r) :
    nsq (fun i => E i k) = 1 := by
  have := congrFun (congrFun hE k) k
  simp only [mul_apply, conjTranspose_apply, one_apply_eq] at this
  simp only [nsq, dotProduct, Pi.star_apply]
  rw [this]; simp

lemma diag_entry (E : Matrix (Fin N) (Fin r) ℂ) (P : Matrix (Fin N) (Fin N) ℂ) (k : Fin r) :
    (Eᴴ * P * E) k k = star (fun i => E i k) ⬝ᵥ (P *ᵥ fun i => E i k) := by
  simp only [mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Reference flag.** For unitary `P` and an isometry `E`, the mean flag over the reference
states is `Re tr(Eᴴ(1 − P)E)/(2r)`. -/
theorem ref_flag (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    refFlag E P = (trace (Eᴴ * (1 - P) * E)).re / (2 * r) := by
  unfold refFlag
  simp_rw [state_flag_formula P hP _ (col_nsq E hE _)]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hE, trace_sub, trace_one]
  simp only [Complex.sub_re, trace, diag, diag_entry, Complex.re_sum, Fintype.card_fin,
    Complex.natCast_re]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp
  ring

/-- Squared Frobenius norm as a trace, for rectangular matrices. -/
lemma frob_trace (M : Matrix (Fin N) (Fin r) ℂ) :
    ∑ i, ∑ k, ‖M i k‖ ^ 2 = (trace (Mᴴ * M)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **Reference Wilson identity.** `Σ |((P − 1)E)ᵢₖ|² = 2 Re tr(Eᴴ(1 − P)E)` for unitary `P`
and any `E`. -/
theorem ref_wilson (E : Matrix (Fin N) (Fin r) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    ∑ i, ∑ k, ‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 = 2 * (trace (Eᴴ * (1 - P) * E)).re := by
  rw [frob_trace]
  have hPP : Pᴴ * P = 1 := hP.1
  have e : ((P - 1) * E)ᴴ * ((P - 1) * E) =
      Eᴴ * (1 - P) * E + (Eᴴ * (1 - P) * E)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, conjTranspose_conjTranspose]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P E, hPP, Matrix.one_mul]
    abel
  rw [e, trace_add, trace_conjTranspose, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- Matrix entries are bounded by the `L²` operator norm (rectangular). -/
lemma entry_le' (M : Matrix (Fin N) (Fin r) ℂ) (i : Fin N) (k : Fin r) : ‖M i k‖ ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (EuclideanSpace.single k 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin N) ℂ).symm
    (M *ᵥ (EuclideanSpace.single k (1 : ℂ)))) i
  convert this using 2
  simp

lemma isometry_norm (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) : ‖E‖ ≤ 1 := by
  have h := E.l2_opNorm_conjTranspose_mul_self
  rw [hE] at h
  have h1 : ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix (Fin r) (Fin r) ℂ) with hs | hs
    · rw [Subsingleton.elim (1 : Matrix (Fin r) (Fin r) ℂ) 0, norm_zero]; norm_num
    · rw [CStarRing.norm_one]
  nlinarith [norm_nonneg E]

/-- **Reference Wilson term from a quadratic expansion.** -/
theorem ref_of_expansion (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (P F : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ))
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 < h) (h1 : h ≤ 1)
    (he : ‖(P - 1) - h ^ 2 • F‖ ≤ K * h ^ 3) :
    |(trace (Eᴴ * (1 - P) * E)).re / h ^ 4 - (∑ i, ∑ k, ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 2| ≤
      (N * r : ℝ) * (K * (2 * ‖F‖ + K)) / 2 * h := by
  have hw := ref_wilson E P hP
  have hEn := isometry_norm E hE
  have hent : ∀ i k, |‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 / h ^ 4 - ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2| ≤
      K * (2 * ‖F‖ + K) * h := by
    intro i k
    have hik : ‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k - h ^ 2 • (F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ≤ K * h ^ 3 := by
      have e : ((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k - h ^ 2 • (F * E : Matrix (Fin N) (Fin r) ℂ) i k = (((P - 1) - h ^ 2 • F) * E : Matrix (Fin N) (Fin r) ℂ) i k := by
        simp [Matrix.sub_mul]
      rw [e]
      refine (entry_le' _ i k).trans ?_
      refine (l2_opNorm_mul _ _).trans ?_
      calc _ ≤ (K * h ^ 3) * 1 := mul_le_mul he hEn (norm_nonneg _) (by positivity)
        _ = _ := by ring
    refine (quartic_close hh h1 hK hik).trans ?_
    gcongr
    refine (entry_le' _ i k).trans ?_
    calc ‖F * E‖ ≤ ‖F‖ * ‖E‖ := l2_opNorm_mul _ _
      _ ≤ ‖F‖ * 1 := by gcongr
      _ = ‖F‖ := mul_one _
  have hre : (trace (Eᴴ * (1 - P) * E)).re = (∑ i, ∑ k, ‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 2 := by
    linarith
  rw [hre]
  have key : (∑ i, ∑ k, ‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 2 / h ^ 4 - (∑ i, ∑ k, ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 2 =
      (∑ i, ∑ k, (‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 / h ^ 4 - ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)) / 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]; ring
  rw [key, abs_div, abs_two]
  have hs : |∑ i, ∑ k, (‖((P - 1) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 / h ^ 4 - ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)| ≤
      (N * r : ℝ) * (K * (2 * ‖F‖ + K) * h) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hent i k).trans ?_
    simp [Finset.sum_const, Finset.card_univ]; ring_nf; rfl
  have : (N * r : ℝ) * (K * (2 * ‖F‖ + K)) / 2 * h = (N * r : ℝ) * (K * (2 * ‖F‖ + K) * h) / 2 := by
    ring
  rw [this]
  exact div_le_div_of_nonneg_right hs (by norm_num)

/-! ## The reference-sampled D₄ action -/

/-- Event-priced D₄ density whose refreshes read the reference states `E`: `W` refreshes per
triangle, each the mean reference flag repaired by `m` events at the common toll. -/
def refDensity (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (toll : ℝ) (m : ℕ) (W h : ℝ) : ℝ :=
  (1 / 12) * ∑ p ∈ D4Gauge.tri,
    W * responseCost toll m (refFlag E (holonomy U x (rv p.1) (rv p.2) h)) / h ^ 4

lemma holonomy_unitary (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x a b : V) (h : ℝ) :
    holonomy U x a b h ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  unfold holonomy
  exact (unitary _).mul_mem ((unitary _).mul_mem (hU _ _ _) (hU _ _ _)) (Unitary.star_mem (hU _ _ _))

theorem ref_density_eq (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ y v h, U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) (toll : ℝ) (m : ℕ) (W h : ℝ) :
    refDensity U x E toll m W h = (toll * m * W / (2 * r) / 12) *
      ∑ p ∈ D4Gauge.tri, (trace (Eᴴ * (1 - holonomy U x (rv p.1) (rv p.2) h) * E)).re / h ^ 4 := by
  unfold refDensity
  simp only [ref_flag E hE _ (holonomy_unitary U hU _ _ _ _), responseCost]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Per-triangle reference Wilson term, `O(h)` close to `Σ|(F(a,b)E)ᵢₖ|²/8`. -/
theorem triangle_ref {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(trace (Eᴴ * (1 - holonomy U x (rv p.1) (rv p.2) h) * E)).re / h ^ 4 -
        (∑ i, ∑ k, ‖(curvature A DA x (rv p.1) (rv p.2) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8|
        ≤ C * h := by
  have ha := rv_norm p.1
  have hb := rv_norm p.2
  have hba : ‖rv p.2 - rv p.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  obtain ⟨Cs, hCs, hs⟩ := triangle_stability hA hL0 hL hskew (rv p.1) (rv p.2) hK
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
  obtain ⟨C0, hC0, hexp⟩ := triangle_expand hA hL0 hL (rv p.1) (rv p.2)
  set F := curvature A DA x (rv p.1) (rv p.2)
  set F' : Matrix (Fin N) (Fin N) ℂ := (1 / 2 : ℝ) • F
  set K' := C0 + 3 * K
  refine ⟨(N * r : ℝ) * (K' * (2 * ‖F'‖ + K')) / 2, by positivity, fun h hh h1 => ?_⟩
  set P := holonomy U x (rv p.1) (rv p.2) h
  have hclose : ‖P - triangle A x (rv p.1) (rv p.2) h‖ ≤ 3 * K * h ^ 3 := (hs h hh h1).1
  have he : ‖(P - 1) - h ^ 2 • F'‖ ≤ K' * h ^ 3 := by
    have e : (P - 1) - h ^ 2 • F' = (P - triangle A x (rv p.1) (rv p.2) h) +
        (triangle A x (rv p.1) (rv p.2) h - (1 + (h ^ 2 / 2) • F)) := by
      simp only [F', smul_smul]; ring_nf; abel
    rw [e]
    have := hexp h hh.le h1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 3 * K * h ^ 3 + C0 * h ^ 3 := add_le_add hclose this
      _ = K' * h ^ 3 := by simp only [K']; ring
  have hw := ref_of_expansion E hE P F' (holonomy_unitary U hU _ _ _ _) (by positivity) hh h1 he
  have hF : (∑ i, ∑ k, ‖(F' * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 2 =
      (∑ i, ∑ k, ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8 := by
    have : ∀ i k, ‖(F' * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 =
        ‖(F * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 / 4 := fun i k => by
      simp only [F', Matrix.smul_mul, Matrix.smul_apply, norm_smul]; norm_num; ring
    simp only [this, ← Finset.sum_div]; ring
  rwa [hF] at hw

/-- Entries of `F(a,b)E` in field-strength components. -/
lemma curvature_ref_entry (A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)) (x a b : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (i : Fin N) (k : Fin r) :
    (curvature A DA x a b * E : Matrix (Fin N) (Fin r) ℂ) i k =
      ∑ μ, ∑ ν, ((a μ * b ν : ℝ) : ℂ) * (fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k := by
  rw [curvature_expand]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul]

/-- **Reference-sampled D₄ continuum limit.** -/
theorem ref_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (U : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _)
    (hK : 0 ≤ K) (hc : CubicConsistent U A x K) (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => refDensity U x E toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * r) / 2) *
        ∑ μ, ∑ ν, ∑ i, ∑ k,
          ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)) := by
  set β := toll * m * W / (2 * r)
  have hp := fun p => triangle_ref hA hL0 hL hskew U hU hK hc E hE p
  choose C hC0 hCb using hp
  -- D₄ isotropy for the reference entries
  have hsum : ∑ p ∈ D4Gauge.tri, ∑ i, ∑ k,
      ‖(curvature A DA x (rv p.1) (rv p.2) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 =
      48 * ∑ μ, ∑ ν, ∑ i, ∑ k,
        ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 := by
    have hentry : ∀ (i : Fin N) (k : Fin r), ∑ p ∈ D4Gauge.tri,
        ‖(curvature A DA x (rv p.1) (rv p.2) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 =
        48 * ∑ μ, ∑ ν, ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 := by
      intro i k
      simp only [curvature_ref_entry]
      exact tri_entry_sum (fun μ ν => (fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k)
        (fun μ ν => by
          show (fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k =
            -(fieldStrength A DA x ν μ * E : Matrix (Fin N) (Fin r) ℂ) i k
          rw [fieldStrength_antisymm, Matrix.neg_mul]; rfl)
    calc _ = ∑ i : Fin N, ∑ k : Fin r, ∑ p ∈ D4Gauge.tri,
          ‖(curvature A DA x (rv p.1) (rv p.2) * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin N, ∑ k : Fin r, 48 * ∑ μ, ∑ ν,
          ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hentry i k
      _ = 48 * ∑ i : Fin N, ∑ k : Fin r, ∑ μ, ∑ ν,
          ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ = _ := by
          congr 1
          calc _ = ∑ i : Fin N, ∑ μ, ∑ k : Fin r, ∑ ν,
                ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 :=
                Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ i : Fin N, ∑ μ, ∑ ν, ∑ k : Fin r,
                ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 :=
                Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
            _ = ∑ μ, ∑ i : Fin N, ∑ ν, ∑ k : Fin r,
                ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 :=
                Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
  have hbound : ∀ h, 0 < h → h ≤ 1 → |refDensity U x E toll m W h -
      β / 2 * ∑ μ, ∑ ν, ∑ i, ∑ k,
        ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2| ≤
      (|β| / 12 * ∑ p ∈ D4Gauge.tri, C p) * h := by
    intro h hh h1
    have e : refDensity U x E toll m W h - β / 2 * ∑ μ, ∑ ν, ∑ i, ∑ k,
        ‖(fieldStrength A DA x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 =
        (β / 12) * ∑ p ∈ D4Gauge.tri,
          ((trace (Eᴴ * (1 - holonomy U x (rv p.1) (rv p.2) h) * E)).re / h ^ 4 -
            (∑ i, ∑ k, ‖(curvature A DA x (rv p.1) (rv p.2) * E :
              Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8) := by
      have hs8 : ∑ p ∈ D4Gauge.tri, (∑ i, ∑ k, ‖(curvature A DA x (rv p.1) (rv p.2) * E :
            Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8 =
          (∑ p ∈ D4Gauge.tri, ∑ i, ∑ k, ‖(curvature A DA x (rv p.1) (rv p.2) * E :
            Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8 := (Finset.sum_div _ _ _).symm
      rw [ref_density_eq U hU x E hE, Finset.sum_sub_distrib, hs8, hsum]
      ring
    rw [e, abs_mul, show |β / 12| = |β| / 12 by rw [abs_div]; norm_num]
    have hs : |∑ p ∈ D4Gauge.tri,
        ((trace (Eᴴ * (1 - holonomy U x (rv p.1) (rv p.2) h) * E)).re / h ^ 4 -
          (∑ i, ∑ k, ‖(curvature A DA x (rv p.1) (rv p.2) * E :
            Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2) / 8)| ≤ (∑ p ∈ D4Gauge.tri, C p) * h := by
      rw [Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hCb p h hh h1)
    calc |β| / 12 * |_| ≤ |β| / 12 * ((∑ p ∈ D4Gauge.tri, C p) * h) := by gcongr
      _ = _ := by ring
  set Ct := |β| / 12 * ∑ p ∈ D4Gauge.tri, C p
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

/-- **Reference stiffness in generator components.** If `tr(Eᴴ Tᵃ Tᵇ E) = κ_R δᵃᵇ`, then
`‖(g Σ_a f_a i Tᵃ) E‖²_F = κ_R g² Σ_a f_a²`. -/
theorem ref_generators {G : Type*} [Fintype G] [DecidableEq G]
    (E : Matrix (Fin N) (Fin r) ℂ) (T : G → Matrix (Fin N) (Fin N) ℂ) (hT : ∀ a, (T a)ᴴ = T a)
    (κ : ℝ) (htr : ∀ a b, trace (Eᴴ * (T a * T b) * E) = if a = b then (κ : ℂ) else 0)
    (g : ℝ) (f : G → ℝ) :
    ∑ i, ∑ k, ‖((∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a)) * E :
        Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2 = κ * g ^ 2 * ∑ a, f a ^ 2 := by
  rw [frob_trace]
  have hM : (∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a))ᴴ =
      ∑ a, ((g * f a : ℝ) : ℂ) • (-Complex.I • T a) := by
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_smul, conjTranspose_smul, hT]
    simp [Complex.conj_ofReal, smul_smul]
  have e : ((∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a)) * E)ᴴ *
      ((∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a)) * E) =
      Eᴴ * ((∑ a, ((g * f a : ℝ) : ℂ) • (-Complex.I • T a)) *
        (∑ a, ((g * f a : ℝ) : ℂ) • (Complex.I • T a))) * E := by
    rw [conjTranspose_mul, hM]; simp only [Matrix.mul_assoc]
  rw [e]
  simp_rw [smul_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sum,
    trace_smul, htr]
  simp only [smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hI : (g * f a : ℂ) * -Complex.I * ((g * f a : ℂ) * Complex.I) = ((g * f a) ^ 2 : ℝ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  push_cast at hI ⊢
  rw [hI]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end PMAction.ReferenceSampling
