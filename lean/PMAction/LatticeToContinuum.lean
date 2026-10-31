import PMAction.LinkConsistency
import PMAction.ContinuumFields

noncomputable section
namespace PMAction.LatticeToContinuum
open PMAction.VaryingFields PMAction.LinkConsistency Matrix
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

local notation "Vec" => (Fin 4 → ℝ)
local notation "Mat" N => Matrix (Fin N) (Fin N) ℂ

/-- Precomposition with `t • id`, as a continuous linear map on connections at a point. -/
def scaleL (N : ℕ) (t : ℝ) : (Vec →L[ℝ] Mat N) →L[ℝ] (Vec →L[ℝ] Mat N) :=
  (ContinuousLinearMap.compL ℝ Vec Vec (Mat N)).flip (t • ContinuousLinearMap.id ℝ Vec)

@[simp] lemma scaleL_apply (t : ℝ) (C : Vec →L[ℝ] Mat N) (v : Vec) :
    scaleL N t C v = C (t • v) := rfl

/-- Background plus `t` times a fluctuation: `A_t(y) v = A(y) v + a(y)(t v)`. -/
def fam (A a : Vec → Vec →L[ℝ] Mat N) (t : ℝ) : Vec → Vec →L[ℝ] Mat N :=
  fun y => A y + scaleL N t (a y)

def dfam (DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)) (t : ℝ) :
    Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N) :=
  fun y => DA y + (scaleL N t).comp (Da y)

/-! ## 1. The family satisfies Paper II's hypotheses -/

section Family
variable {A a : Vec → Vec →L[ℝ] Mat N} {DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)}
  {x : Vec} {LA La : ℝ}

lemma fam_deriv (hA : ∀ y, HasFDerivAt A (DA y) y) (ha : ∀ y, HasFDerivAt a (Da y) y) (t : ℝ)
    (y : Vec) : HasFDerivAt (fam A a t) (dfam DA Da t y) y := by
  have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero (F := Vec →L[ℝ] Mat N)).mp (hA y)
  have h2 := (hasFDerivAt_iff_isLittleO_nhds_zero (F := Vec →L[ℝ] Mat N)).mp (ha y)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero (F := Vec →L[ℝ] Mat N)]
  have e : (fun h => fam A a t (y + h) - fam A a t y - dfam DA Da t y h) =
      fun h => (A (y + h) - A y - DA y h) + scaleL N t (a (y + h) - a y - Da y h) := by
    funext h
    simp only [fam, dfam, map_sub, _root_.add_apply, ContinuousLinearMap.comp_apply]
    abel
  rw [e]
  exact h1.add (((scaleL N t).isBigO_comp _ _).trans_isLittleO h2)

lemma fam_lip (hLA : ∀ y, ‖DA y - DA x‖ ≤ LA * ‖y - x‖) (hLa : ∀ y, ‖Da y - Da x‖ ≤ La * ‖y - x‖)
    (t : ℝ) (y : Vec) :
    ‖dfam DA Da t y - dfam DA Da t x‖ ≤ (LA + ‖scaleL N t‖ * La) * ‖y - x‖ := by
  have e : dfam DA Da t y - dfam DA Da t x = (DA y - DA x) + (scaleL N t).comp (Da y - Da x) := by
    simp only [dfam, ContinuousLinearMap.comp_sub]; abel
  rw [e]
  have h1 := norm_add_le (DA y - DA x) ((scaleL N t).comp (Da y - Da x))
  have h2 := ContinuousLinearMap.opNorm_comp_le (scaleL N t) (Da y - Da x)
  have h5 : ‖scaleL N t‖ * ‖Da y - Da x‖ ≤ ‖scaleL N t‖ * (La * ‖y - x‖) := by
    gcongr; exact hLa y
  have h3 := hLA y
  refine le_trans h1 ?_
  nlinarith

lemma fam_skew (sA : ∀ y v, star (A y v) = -A y v) (sa : ∀ y v, star (a y v) = -a y v) (t : ℝ)
    (y v : Vec) : star (fam A a t y v) = -fam A a t y v := by
  simp only [fam, _root_.add_apply, scaleL_apply, star_add, sA, sa, neg_add]

end Family

/-! ## 2. Field strength of the family -/

/-- The first-order term `D_μ a_ν − D_ν a_μ`, with `D_μ = ∂_μ + [A_μ, ·]`. -/
def Gc (A a : Vec → Vec →L[ℝ] Mat N) (Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)) (x : Vec)
    (μ ν : Fin 4) : Mat N :=
  (Da x (basis μ) (basis ν) + (A x (basis μ) * a x (basis ν) - a x (basis ν) * A x (basis μ))) -
    (Da x (basis ν) (basis μ) + (A x (basis ν) * a x (basis μ) - a x (basis μ) * A x (basis ν)))

/-- The second-order term `[a_μ, a_ν]`. -/
def Hc (a : Vec → Vec →L[ℝ] Mat N) (x : Vec) (μ ν : Fin 4) : Mat N :=
  a x (basis μ) * a x (basis ν) - a x (basis ν) * a x (basis μ)

theorem fieldStrength_fam (A a : Vec → Vec →L[ℝ] Mat N) (DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N))
    (t : ℝ) (x : Vec) (μ ν : Fin 4) :
    fieldStrength (fam A a t) (dfam DA Da t) x μ ν =
      fieldStrength A DA x μ ν + t • Gc A a Da x μ ν + (t ^ 2) • Hc a x μ ν := by
  simp only [fieldStrength, curvature, fam, dfam, _root_.add_apply, ContinuousLinearMap.comp_apply,
    scaleL_apply, map_smul, Gc, Hc]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, sq]
  module

/-! ## 3. Second difference of the Yang–Mills density -/

lemma normSq_second (f g k : ℂ) (s : ℝ) :
    ‖f + s • g + (s ^ 2) • k‖ ^ 2 + ‖f + (-s) • g + ((-s) ^ 2) • k‖ ^ 2 - 2 * ‖f‖ ^ 2 =
      2 * s ^ 2 * (‖g‖ ^ 2 + 2 * (star f * k).re) + 2 * s ^ 4 * ‖k‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The continuum Yang–Mills density of the family, `(β/2) Σ |F(t)_{μν,ij}|²`. -/
def ymDensity (A a : Vec → Vec →L[ℝ] Mat N) (DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N))
    (x : Vec) (β t : ℝ) : ℝ :=
  (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength (fam A a t) (dfam DA Da t) x μ ν i j‖ ^ 2

/-- The second-variation density `(β/2) Σ (|G|² + 2 Re⟨F, H⟩)`. -/
def q2 (A a : Vec → Vec →L[ℝ] Mat N) (DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)) (x : Vec)
    (β : ℝ) : ℝ :=
  (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, (‖Gc A a Da x μ ν i j‖ ^ 2 +
    2 * (star (fieldStrength A DA x μ ν i j) * Hc a x μ ν i j).re)

def q4 (a : Vec → Vec →L[ℝ] Mat N) (x : Vec) (β : ℝ) : ℝ :=
  (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖Hc a x μ ν i j‖ ^ 2

lemma sum4 (u v w p q : Fin 4 → Fin 4 → Fin N → Fin N → ℝ) (c1 c2 : ℝ)
    (h : ∀ μ ν i j, u μ ν i j + v μ ν i j - 2 * w μ ν i j = c1 * p μ ν i j + c2 * q μ ν i j) :
    (∑ μ, ∑ ν, ∑ i, ∑ j, u μ ν i j) + (∑ μ, ∑ ν, ∑ i, ∑ j, v μ ν i j) -
        2 * (∑ μ, ∑ ν, ∑ i, ∑ j, w μ ν i j) =
      c1 * (∑ μ, ∑ ν, ∑ i, ∑ j, p μ ν i j) + c2 * (∑ μ, ∑ ν, ∑ i, ∑ j, q μ ν i j) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, h]

/-- **The Yang–Mills density is a quartic in `t`.** Its symmetric second difference is
`2s² q₂ + 2s⁴ q₄`. -/
theorem ym_second_difference (A a : Vec → Vec →L[ℝ] Mat N)
    (DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)) (x : Vec) (β s : ℝ) :
    ymDensity A a DA Da x β s + ymDensity A a DA Da x β (-s) - 2 * ymDensity A a DA Da x β 0 =
      2 * s ^ 2 * q2 A a DA Da x β + 2 * s ^ 4 * q4 a x β := by
  have h := sum4 (fun μ ν i j => ‖fieldStrength (fam A a s) (dfam DA Da s) x μ ν i j‖ ^ 2)
    (fun μ ν i j => ‖fieldStrength (fam A a (-s)) (dfam DA Da (-s)) x μ ν i j‖ ^ 2)
    (fun μ ν i j => ‖fieldStrength (fam A a 0) (dfam DA Da 0) x μ ν i j‖ ^ 2)
    (fun μ ν i j => ‖Gc A a Da x μ ν i j‖ ^ 2 +
      2 * (star (fieldStrength A DA x μ ν i j) * Hc a x μ ν i j).re)
    (fun μ ν i j => ‖Hc a x μ ν i j‖ ^ 2) (2 * s ^ 2) (2 * s ^ 4) (fun μ ν i j => by
      simp only [fieldStrength_fam, Matrix.add_apply, Matrix.smul_apply, zero_smul, add_zero,
        zero_pow two_ne_zero, Matrix.zero_apply]
      exact normSq_second _ _ _ s)
  simp only [ymDensity, q2, q4]
  linear_combination (β / 2) * h

/-! ## 4. Skew-Hermitian components and the trace form -/

/-- Derivatives of skew-Hermitian connections are skew-Hermitian. -/
theorem deriv_skew {A : (Fin 4 → ℝ) → (Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {D : (Fin 4 → ℝ) →L[ℝ] ((Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : Fin 4 → ℝ}
    (hA : HasFDerivAt (F := (Fin 4 → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ) A D x)
    (sA : ∀ y v, (A y v)ᴴ = -A y v) (u v : Fin 4 → ℝ) : (D u v)ᴴ = -D u v := by
  have hlim := hA.lim u (c := fun n : ℕ => (n : ℝ)) (l := Filter.atTop)
    (by simpa using tendsto_natCast_atTop_atTop)
  have hv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) • (A (x + (n : ℝ)⁻¹ • u) - A x)) v)
      Filter.atTop (nhds (D u v)) :=
    ((ContinuousLinearMap.apply ℝ (Matrix (Fin N) (Fin N) ℂ) v).continuous.tendsto _).comp hlim
  have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => Mᴴ + M) :=
    (continuous_id.matrix_conjTranspose).add continuous_id
  have hz := (hcont.tendsto _).comp hv
  have hzero : (fun n : ℕ => (((n : ℝ) • (A (x + (n : ℝ)⁻¹ • u) - A x)) v)ᴴ +
      ((n : ℝ) • (A (x + (n : ℝ)⁻¹ • u) - A x)) v) = fun _ => 0 := by
    funext n
    rw [_root_.smul_apply, _root_.sub_apply, conjTranspose_smul, conjTranspose_sub, sA, sA]
    simp only [star_trivial]
    module
  have : (D u v)ᴴ + D u v = 0 := by
    have h0 : Filter.Tendsto (fun n : ℕ => (((n : ℝ) • (A (x + (n : ℝ)⁻¹ • u) - A x)) v)ᴴ +
      ((n : ℝ) • (A (x + (n : ℝ)⁻¹ • u) - A x)) v) Filter.atTop (nhds 0) := by
      rw [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hz h0
  exact eq_neg_of_add_eq_zero_left this

section Skew
variable {A a : Vec → Vec →L[ℝ] Mat N} {DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)} {x : Vec}

lemma skew_of_star {A : Vec → Vec →L[ℝ] Mat N} (sA : ∀ y v, star (A y v) = -A y v) :
    ∀ y v, (A y v)ᴴ = -A y v := sA

lemma comm_skew {X Y : Mat N} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) : (X * Y - Y * X)ᴴ = -(X * Y - Y * X) := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX, hY]; noncomm_ring

theorem F_skew (hA : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) A (DA y) y)
    (sA : ∀ y v, (A y v)ᴴ = -A y v) (μ ν : Fin 4) :
    (fieldStrength A DA x μ ν)ᴴ = -fieldStrength A DA x μ ν := by
  have d := deriv_skew (hA x) sA
  simp only [fieldStrength, curvature]
  rw [conjTranspose_add, conjTranspose_sub, d, d, comm_skew (sA x _) (sA x _)]
  abel

theorem G_skew (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y)
    (sA : ∀ y v, (A y v)ᴴ = -A y v) (sa : ∀ y v, (a y v)ᴴ = -a y v) (μ ν : Fin 4) :
    (Gc A a Da x μ ν)ᴴ = -Gc A a Da x μ ν := by
  have d := deriv_skew (ha x) sa
  simp only [Gc]
  rw [conjTranspose_sub, conjTranspose_add, conjTranspose_add, d, d,
    comm_skew (sA x _) (sa x _), comm_skew (sA x _) (sa x _)]
  abel

theorem H_skew (sa : ∀ y v, (a y v)ᴴ = -a y v) (μ ν : Fin 4) :
    (Hc a x μ ν)ᴴ = -Hc a x μ ν := comm_skew (sa x _) (sa x _)

end Skew

/-- Frobenius pairing: `Σ Re(conj X_ij Y_ij) = Re tr(Xᴴ Y)`. -/
lemma frob (X Y : Mat N) : ∑ i, ∑ j, (star (X i j) * Y i j).re = (trace (Xᴴ * Y)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  exact Finset.sum_comm

lemma frob_skew {X : Mat N} (hX : Xᴴ = -X) (Y : Mat N) :
    ∑ i, ∑ j, (star (X i j) * Y i j).re = ContinuumFields.traceForm N (X * Y) := by
  rw [frob, hX, ContinuumFields.traceForm_apply, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re]

lemma norm_sq_star (z : ℂ) : ‖z‖ ^ 2 = (star z * z).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]; ring

/-- **The second-variation density in trace form.** With `τ = −Re tr` (the pairing of
`ContinuumFields`), `q₂ = 2β · ¼ Σ_{μν} (τ(G_μν G_μν) + 2 τ(F_μν [a_μ, a_ν]))`. Here
`G_μν = D_μ a_ν − D_ν a_μ` (`Gc`). This is the pointwise integrand of
`ContinuumFields.quad2` without the gauge-fixing term. -/
theorem q2_trace (hA : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) A (DA y) y)
    (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y)
    (sA : ∀ y v, (A y v)ᴴ = -A y v) (sa : ∀ y v, (a y v)ᴴ = -a y v) (x : Vec) (β : ℝ) :
    q2 A a DA Da x β = 2 * β * ((1 / 4) * ∑ μ, ∑ ν,
      (ContinuumFields.traceForm N (Gc A a Da x μ ν * Gc A a Da x μ ν) +
        2 * ContinuumFields.traceForm N (fieldStrength A DA x μ ν * Hc a x μ ν))) := by
  have key : ∀ μ ν, ∑ i, ∑ j, (‖Gc A a Da x μ ν i j‖ ^ 2 +
      2 * (star (fieldStrength A DA x μ ν i j) * Hc a x μ ν i j).re) =
      ContinuumFields.traceForm N (Gc A a Da x μ ν * Gc A a Da x μ ν) +
        2 * ContinuumFields.traceForm N (fieldStrength A DA x μ ν * Hc a x μ ν) := by
    intro μ ν
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, norm_sq_star]
    rw [frob_skew (G_skew ha sA sa μ ν), frob_skew (F_skew hA sA μ ν)]
  simp only [q2, key]
  ring

/-- `∂_μ` of the component `a_ν` is `Da(e_μ)(e_ν)`: `Gc` is the curl of `ContinuumFields`. -/
theorem dir_component {a : Vec → Vec →L[ℝ] Mat N} {Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)}
    (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y) (μ ν : Fin 4)
    (x : Vec) : ContinuumFields.dir μ (fun p => a p (basis ν)) x = Da x (basis μ) (basis ν) := by
  have h := HasFDerivAt.comp (F := Vec →L[ℝ] Mat N) x
    (ContinuousLinearMap.apply ℝ (Mat N) (basis ν)).hasFDerivAt (ha x)
  simp only [ContinuumFields.dir]
  rw [show (fun p => a p (basis ν)) = (ContinuousLinearMap.apply ℝ (Mat N) (basis ν)) ∘ a from rfl,
    h.fderiv]
  rfl

/-! ## 5. The lattice second variation converges to the continuum one -/

section Limit
variable {A a : Vec → Vec →L[ℝ] Mat N} {DA Da : Vec → Vec →L[ℝ] (Vec →L[ℝ] Mat N)}
  {x : Vec} {LA La : ℝ}

lemma fam_tendsto (hA : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) A (DA y) y)
    (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y) (hLA0 : 0 ≤ LA) (hLa0 : 0 ≤ La)
    (hLA : ∀ y, ‖DA y - DA x‖ ≤ LA * ‖y - x‖) (hLa : ∀ y, ‖Da y - Da x‖ ≤ La * ‖y - x‖)
    (sA : ∀ y v, star (A y v) = -A y v) (sa : ∀ y v, star (a y v) = -a y v) (β t : ℝ) :
    Filter.Tendsto (fun h => d4Density (fam A a t) x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ymDensity A a DA Da x β t)) :=
  d4_yang_mills_tendsto (fam_deriv hA ha t) (by positivity) (fam_lip hLA hLa t)
    (fam_skew sA sa t) β

/-- **Lattice second variation.** For each fluctuation size `s`, the symmetric second
difference of Paper II's D₄ lattice density converges, as `h → 0`, to `2s² q₂ + 2s⁴ q₄`. -/
theorem lattice_second_difference (hA : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) A (DA y) y)
    (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y) (hLA0 : 0 ≤ LA) (hLa0 : 0 ≤ La)
    (hLA : ∀ y, ‖DA y - DA x‖ ≤ LA * ‖y - x‖) (hLa : ∀ y, ‖Da y - Da x‖ ≤ La * ‖y - x‖)
    (sA : ∀ y v, star (A y v) = -A y v) (sa : ∀ y v, star (a y v) = -a y v) (β s : ℝ) :
    Filter.Tendsto (fun h => d4Density (fam A a s) x β h + d4Density (fam A a (-s)) x β h -
        2 * d4Density (fam A a 0) x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * s ^ 2 * q2 A a DA Da x β + 2 * s ^ 4 * q4 a x β)) := by
  have h1 := fam_tendsto hA ha hLA0 hLa0 hLA hLa sA sa β s
  have h2 := fam_tendsto hA ha hLA0 hLa0 hLA hLa sA sa β (-s)
  have h3 := fam_tendsto hA ha hLA0 hLa0 hLA hLa sA sa β 0
  rw [← ym_second_difference]
  exact (h1.add h2).sub (h3.const_mul 2)

/-- **The continuum Hessian is the limit of the lattice Hessian.** Divide the lattice second
difference by `s²`. Its `h → 0` limit tends to `2q₂` as `s → 0`, and `q₂` is the trace-form
second-variation density (`q2_trace`). -/
theorem lattice_hessian (β : ℝ) :
    Filter.Tendsto (fun s : ℝ => (2 * s ^ 2 * q2 A a DA Da x β + 2 * s ^ 4 * q4 a x β) / s ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * q2 A a DA Da x β)) := by
  have hc : Filter.Tendsto (fun s : ℝ => 2 * q2 A a DA Da x β + 2 * s ^ 2 * q4 a x β)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * q2 A a DA Da x β)) := by
    have : Continuous (fun s : ℝ => 2 * q2 A a DA Da x β + 2 * s ^ 2 * q4 a x β) := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa using h
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  field_simp

/-- The same with Paper II's actual links: any unitary link families that are cubically
consistent with the three connections have the same second-difference limit. -/
theorem actual_links_second_difference
    (hA : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) A (DA y) y)
    (ha : ∀ y, HasFDerivAt (F := Vec →L[ℝ] Mat N) a (Da y) y) (hLA0 : 0 ≤ LA) (hLa0 : 0 ≤ La)
    (hLA : ∀ y, ‖DA y - DA x‖ ≤ LA * ‖y - x‖) (hLa : ∀ y, ‖Da y - Da x‖ ≤ La * ‖y - x‖)
    (sA : ∀ y v, star (A y v) = -A y v) (sa : ∀ y v, star (a y v) = -a y v) (β s K : ℝ)
    (hK : 0 ≤ K) (U : ℝ → Vec → Vec → ℝ → Mat N) (hU : ∀ t y v h, U t y v h ∈ unitary (Mat N))
    (hc : ∀ t, CubicConsistent (U t) (fam A a t) x K) :
    Filter.Tendsto (fun h => linkDensity (U s) x β h + linkDensity (U (-s)) x β h -
        2 * linkDensity (U 0) x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * s ^ 2 * q2 A a DA Da x β + 2 * s ^ 4 * q4 a x β)) := by
  have l := fun t => d4_link_tendsto (fam_deriv hA ha t) (by positivity) (fam_lip hLA hLa t)
    (fam_skew sA sa t) (U t) (hU t) hK (hc t) β
  rw [← ym_second_difference]
  exact ((l s).add (l (-s))).sub ((l 0).const_mul 2)

end Limit

end PMAction.LatticeToContinuum
