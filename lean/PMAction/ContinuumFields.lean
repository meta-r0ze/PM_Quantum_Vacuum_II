import PMAction.FluctuationPremises
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped ContDiff

noncomputable section
namespace PMAction.ContinuumFields
open Finset MeasureTheory PMAction.GaugeFluctuation

/-! ## 1. Hessian and Ward identity with the background in a larger space -/

section TwoSpace
variable {M Mb : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup Mb] [Module ℝ Mb] {n : ℕ}
  (B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (Bb : Mb →ₗ[ℝ] M →ₗ[ℝ] ℝ) (br : M →ₗ[ℝ] M →ₗ[ℝ] M)
  (ad : Mb →ₗ[ℝ] M →ₗ[ℝ] M) (D : Fin n → Module.End ℝ M) (F : Fin n → Fin n → Mb)

/-- The second variation of the gauge-fixed Yang–Mills action, with the background field
strength in a space `Mb` that may differ from the fluctuations (non-decaying backgrounds). -/
def quad2 (a : Fin n → M) : ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, (B (curl D a μ ν) (curl D a μ ν) + 2 * Bb (F μ ν) (br (a μ) (a ν))) +
    (1 / 2) * B (gdiv D a) (gdiv D a)

def hess2 (a : Fin n → M) (ν : Fin n) : M :=
  -(∑ μ, D μ (D μ (a ν))) + (2 : ℝ) • ∑ μ, ad (F μ ν) (a μ)

/-- With `Mb = M` this is `GaugeFluctuation.quad`. -/
theorem quad2_self (F' : Fin n → Fin n → M) (a : Fin n → M) :
    quad2 B B br D F' a = quad B br D F' a := rfl

theorem quad2_eq_hess2 (hB : ∀ x y, B x y = B y x)
    (hD : ∀ μ x y, B (D μ x) y = -B x (D μ y))
    (hinv : ∀ f x y, Bb f (br x y) = B (ad f x) y)
    (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = ad (F μ ν) x) (a : Fin n → M) :
    quad2 B Bb br D F a = (1 / 2) * ∑ ν, B (a ν) (hess2 ad D F a ν) := by
  set P : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D μ (D μ (a ν))) with hP
  set R : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D μ (D ν (a μ))) with hR
  set S : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D ν (D μ (a μ))) with hS
  set G : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (ad (F μ ν) (a μ)) with hG
  have e1 : ∀ μ ν, B (curl D a μ ν) (curl D a μ ν) = -P μ ν - P ν μ + R μ ν + R ν μ := by
    intro μ ν
    simp only [curl, map_sub, LinearMap.sub_apply, hD, hP, hR]
    ring
  have e2 : ∀ μ ν, Bb (F μ ν) (br (a μ) (a ν)) = G μ ν := by
    intro μ ν; rw [hinv, hB]
  have e3 : B (gdiv D a) (gdiv D a) = -∑ μ, ∑ ν, S μ ν := by
    simp only [gdiv, map_sum, LinearMap.sum_apply, hD, hS, sum_neg_distrib]
  have e4 : ∀ μ ν, R μ ν - S μ ν = G μ ν := by
    intro μ ν; simp only [hR, hS, hG, ← map_sub, hcurv]
  have cP : ∑ μ, ∑ ν, P ν μ = ∑ μ, ∑ ν, P μ ν := sum_comm
  have cR : ∑ μ, ∑ ν, R ν μ = ∑ μ, ∑ ν, R μ ν := sum_comm
  have cG : ∑ ν, ∑ μ, G μ ν = ∑ μ, ∑ ν, G μ ν := sum_comm
  have hRS : ∑ μ, ∑ ν, R μ ν = ∑ μ, ∑ ν, S μ ν + ∑ μ, ∑ ν, G μ ν := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun μ _ => ?_
    rw [← sum_add_distrib]; refine sum_congr rfl fun ν _ => ?_
    linarith [e4 μ ν]
  have rhs : ∑ ν, B (a ν) (hess2 ad D F a ν) =
      -∑ ν, ∑ μ, P μ ν + 2 * ∑ ν, ∑ μ, G μ ν := by
    simp only [hess2, map_add, map_neg, map_smul, map_sum, smul_eq_mul, hP, hG,
      sum_add_distrib, sum_neg_distrib, ← mul_sum]
  unfold quad2
  simp only [e1, e2, e3, sum_add_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  rw [rhs]
  simp only [cP, cR, cG]
  linear_combination (1 / 2 : ℝ) * hRS

/-- The unfixed operator with background in `Mb`. -/
def bare2 (a : Fin n → M) (ν : Fin n) : M :=
  -(∑ μ, D μ (D μ (a ν))) + ∑ μ, D μ (D ν (a μ)) + ∑ μ, ad (F μ ν) (a μ)

variable {ad D F}

/-- **Ward identity** with the background in `Mb`. -/
theorem gauge_null2 (Db : Fin n → Module.End ℝ Mb)
    (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = ad (F μ ν) x)
    (hleib : ∀ μ f x, D μ (ad f x) = ad (Db μ f) x + ad f (D μ x))
    (heom : ∀ ν, ∑ μ, Db μ (F μ ν) = 0) (w0 : M) (ν : Fin n) :
    bare2 ad D F (fun μ => D μ w0) ν = 0 := by
  have h1 : ∀ μ, D μ (D ν (D μ w0)) =
      D μ (D μ (D ν w0)) - ad (Db μ (F μ ν)) w0 - ad (F μ ν) (D μ w0) := by
    intro μ
    have e : D ν (D μ w0) = D μ (D ν w0) - ad (F μ ν) w0 := by rw [← hcurv μ ν w0]; abel
    rw [e, map_sub, hleib]; abel
  have h2 : ∑ μ, ad (Db μ (F μ ν)) w0 = 0 := by
    rw [← LinearMap.sum_apply, ← map_sum, heom, map_zero, LinearMap.zero_apply]
  simp only [bare2, h1, sum_sub_distrib, h2]
  abel

end TwoSpace

/-! ## 2. Smooth fields on `ℝⁿ` -/

section Calculus
variable {n : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- Coordinate direction `μ`. -/
def e (μ : Fin n) : Fin n → ℝ := Pi.single μ 1

/-- Directional derivative `∂_μ f`. -/
def dir (μ : Fin n) (f : (Fin n → ℝ) → 𝔸) : (Fin n → ℝ) → 𝔸 := fun p => fderiv ℝ f p (e μ)

lemma smooth_dir {f : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (μ : Fin n) :
    ContDiff ℝ ∞ (dir μ f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma compact_dir {f : (Fin n → ℝ) → 𝔸} (hf : HasCompactSupport f) (μ : Fin n) :
    HasCompactSupport (dir μ f) :=
  (hf.fderiv ℝ).comp_left (g := fun L : (Fin n → ℝ) →L[ℝ] 𝔸 => L (e μ)) rfl

lemma dir_mul {c d : (Fin n → ℝ) → 𝔸} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) (μ : Fin n)
    (p : Fin n → ℝ) :
    dir μ (fun q => c q * d q) p = c p * dir μ d p + dir μ c p * d p := by
  have := fderiv_mul' (𝕜 := ℝ) (x := p) ((hc.differentiable (by simp)) p)
    ((hd.differentiable (by simp)) p)
  simp only [dir]
  rw [show (fun q => c q * d q) = c * d from rfl, this]
  simp [MulOpposite.smul_eq_mul_unop]

lemma dir_add {f g : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin n)
    (p : Fin n → ℝ) : dir μ (fun q => f q + g q) p = dir μ f p + dir μ g p := by
  simp only [dir]
  rw [show (fun q => f q + g q) = f + g from rfl,
    fderiv_add ((hf.differentiable (by simp)) p) ((hg.differentiable (by simp)) p)]
  rfl

lemma dir_sub {f g : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin n)
    (p : Fin n → ℝ) : dir μ (fun q => f q - g q) p = dir μ f p - dir μ g p := by
  simp only [dir]
  rw [show (fun q => f q - g q) = f - g from rfl,
    fderiv_sub ((hf.differentiable (by simp)) p) ((hg.differentiable (by simp)) p)]
  rfl

lemma dir_smul {f : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (c : ℝ) (μ : Fin n)
    (p : Fin n → ℝ) : dir μ (fun q => c • f q) p = c • dir μ f p := by
  simp only [dir]
  rw [show (fun q => c • f q) = c • f from rfl, fderiv_const_smul ((hf.differentiable (by simp)) p)]
  rfl

lemma dir_add' {f g : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin n)
    (p : Fin n → ℝ) : dir μ (f + g) p = dir μ f p + dir μ g p := dir_add hf hg μ p

lemma dir_smul' {f : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (c : ℝ) (μ : Fin n)
    (p : Fin n → ℝ) : dir μ (c • f) p = c • dir μ f p := dir_smul hf c μ p

lemma dir_comm {f : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (μ ν : Fin n) (p : Fin n → ℝ) :
    dir μ (dir ν f) p = dir ν (dir μ f) p := by
  have hs : IsSymmSndFDerivAt ℝ f p :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have key : ∀ v w, dir v (dir w f) p = fderiv ℝ (fderiv ℝ f) p (e v) (e w) := by
    intro v w
    show fderiv ℝ (fun y => fderiv ℝ f y (e w)) p (e v) = _
    rw [fderiv_clm_apply (hd p) (differentiableAt_const _)]
    simp
  rw [key, key, hs]

end Calculus

/-! ## 3. The function-space instance -/

section Fields
variable {n : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

variable (n 𝔸) in
/-- Smooth fields on `ℝⁿ`: the space of backgrounds. -/
def smoothFields : Submodule ℝ ((Fin n → ℝ) → 𝔸) where
  carrier := {f | ContDiff ℝ ∞ f}
  add_mem' {a b} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) := ha.add hb
  zero_mem' := show ContDiff ℝ ∞ (fun _ => (0 : 𝔸)) from contDiff_const
  smul_mem' c x (h : ContDiff ℝ ∞ x) := h.const_smul c

variable (n 𝔸) in
/-- Smooth compactly supported fields: the space of fluctuations. -/
def testFields : Submodule ℝ ((Fin n → ℝ) → 𝔸) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const (c := (0 : 𝔸)), HasCompactSupport.zero⟩
  smul_mem' c _ h := ⟨h.1.const_smul c, h.2.comp_left (g := fun y : 𝔸 => c • y) (smul_zero c)⟩

lemma sm (f : smoothFields n 𝔸) : ContDiff ℝ ∞ (f : (Fin n → ℝ) → 𝔸) := f.2

/-- Pointwise commutator. -/
def cm (f g : (Fin n → ℝ) → 𝔸) : (Fin n → ℝ) → 𝔸 := fun p => f p * g p - g p * f p

/-- Covariant derivative `∂_μ f + [A, f]`. -/
def cov (A : (Fin n → ℝ) → 𝔸) (μ : Fin n) (f : (Fin n → ℝ) → 𝔸) : (Fin n → ℝ) → 𝔸 :=
  fun p => dir μ f p + (A p * f p - f p * A p)

lemma cm_smooth {f g : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cm f g) := (hf.mul hg).sub (hg.mul hf)

omit [NormedAlgebra ℝ 𝔸] in
lemma cm_compact {f g : (Fin n → ℝ) → 𝔸} (hg : HasCompactSupport g) :
    HasCompactSupport (cm f g) :=
  (hg.mul_left (f := f)).sub (hg.mul_right (f' := f))

lemma cov_smooth {A f : (Fin n → ℝ) → 𝔸} (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (μ : Fin n) :
    ContDiff ℝ ∞ (cov A μ f) := (smooth_dir hf μ).add (cm_smooth hA hf)

lemma cov_compact {A f : (Fin n → ℝ) → 𝔸} (hf : HasCompactSupport f) (μ : Fin n) :
    HasCompactSupport (cov A μ f) := (compact_dir hf μ).add (cm_compact hf)

lemma dir_cm {f g : (Fin n → ℝ) → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin n)
    (p : Fin n → ℝ) :
    dir μ (cm f g) p = f p * dir μ g p + dir μ f p * g p - (g p * dir μ f p + dir μ g p * f p) := by
  unfold cm
  rw [dir_sub (hf.mul hg) (hg.mul hf), dir_mul hf hg, dir_mul hg hf]

lemma dir_cov {A f : (Fin n → ℝ) → 𝔸} (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (μ ν : Fin n)
    (p : Fin n → ℝ) :
    dir μ (cov A ν f) p = dir μ (dir ν f) p +
      (A p * dir μ f p + dir μ A p * f p - (f p * dir μ A p + dir μ f p * A p)) := by
  unfold cov
  rw [show (fun p => dir ν f p + (A p * f p - f p * A p)) = (fun q => dir ν f q + cm A f q) from rfl,
    dir_add (smooth_dir hf ν) (cm_smooth hA hf), dir_cm hA hf]

/-- The bracket on fluctuations. -/
def brT : testFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 :=
  LinearMap.mk₂ ℝ (fun x y => ⟨cm x y, cm_smooth x.2.1 y.2.1, cm_compact y.2.2⟩)
    (fun x x' y => Subtype.ext <| funext fun p => by simp [cm]; noncomm_ring)
    (fun c x y => Subtype.ext <| funext fun p => by
      simp [cm, smul_sub])
    (fun x y y' => Subtype.ext <| funext fun p => by simp [cm]; noncomm_ring)
    (fun c x y => Subtype.ext <| funext fun p => by
      simp [cm, smul_sub])

/-- The background acting on fluctuations, `[f, x]`. -/
def adT : smoothFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 :=
  LinearMap.mk₂ ℝ (fun f x => ⟨cm f x, cm_smooth (sm f) x.2.1, cm_compact x.2.2⟩)
    (fun f f' x => Subtype.ext <| funext fun p => by simp [cm]; noncomm_ring)
    (fun c f x => Subtype.ext <| funext fun p => by
      simp [cm, smul_sub])
    (fun f x x' => Subtype.ext <| funext fun p => by simp [cm]; noncomm_ring)
    (fun c f x => Subtype.ext <| funext fun p => by
      simp [cm, smul_sub])

/-- Covariant derivative on fluctuations. -/
def covT (A : Fin n → smoothFields n 𝔸) (μ : Fin n) : Module.End ℝ (testFields n 𝔸) where
  toFun x := ⟨cov (A μ) μ x, cov_smooth (sm (A μ)) x.2.1 μ, cov_compact x.2.2 μ⟩
  map_add' x y := Subtype.ext <| funext fun p => by
    simp only [cov, Submodule.coe_add, Pi.add_apply]
    rw [dir_add' x.2.1 y.2.1]
    noncomm_ring
  map_smul' c x := Subtype.ext <| funext fun p => by
    simp only [cov, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [dir_smul' x.2.1]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_add]

/-- Covariant derivative on backgrounds. -/
def covS (A : Fin n → smoothFields n 𝔸) (μ : Fin n) : Module.End ℝ (smoothFields n 𝔸) where
  toFun f := ⟨cov (A μ) μ f, show ContDiff ℝ ∞ _ from cov_smooth (sm (A μ)) (sm f) μ⟩
  map_add' x y := Subtype.ext <| funext fun p => by
    simp only [cov, Submodule.coe_add, Pi.add_apply]
    rw [dir_add' (sm x) (sm y)]
    noncomm_ring
  map_smul' c x := Subtype.ext <| funext fun p => by
    simp only [cov, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [dir_smul' (sm x)]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_add]

/-- Field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`. -/
def curvS (A : Fin n → smoothFields n 𝔸) (μ ν : Fin n) : smoothFields n 𝔸 :=
  ⟨fun p => dir μ (A ν : (Fin n → ℝ) → 𝔸) p - dir ν (A μ : (Fin n → ℝ) → 𝔸) p +
      cm (A μ) (A ν) p,
    ((smooth_dir (sm (A ν)) μ).sub (smooth_dir (sm (A μ)) ν)).add
      (cm_smooth (sm (A μ)) (sm (A ν)))⟩

/-! ### The trace pairing and integration by parts -/

variable (τ : 𝔸 →L[ℝ] ℝ)

lemma int_left {f g : (Fin n → ℝ) → 𝔸} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport g) : Integrable (fun p => τ (f p * g p)) :=
  (τ.continuous.comp (hf.mul hg)).integrable_of_hasCompactSupport
    ((hc.mul_left (f := f)).comp_left (g := τ) (map_zero τ))

lemma int_right {f g : (Fin n → ℝ) → 𝔸} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun p => τ (f p * g p)) :=
  (τ.continuous.comp (hf.mul hg)).integrable_of_hasCompactSupport
    ((hc.mul_right (f' := g)).comp_left (g := τ) (map_zero τ))

/-- `∫ τ(f g)`. -/
def pr (f g : (Fin n → ℝ) → 𝔸) : ℝ := ∫ p, τ (f p * g p)

lemma pr_add_left {f f' g : (Fin n → ℝ) → 𝔸} (hf : Continuous f) (hf' : Continuous f')
    (hg : Continuous g) (hc : HasCompactSupport g) : pr τ (f + f') g = pr τ f g + pr τ f' g := by
  simp only [pr, Pi.add_apply, add_mul, map_add]
  exact integral_add (int_left τ hf hg hc) (int_left τ hf' hg hc)

lemma pr_add_right {f g g' : (Fin n → ℝ) → 𝔸} (hf : Continuous f) (hg : Continuous g)
    (hg' : Continuous g') (hc : HasCompactSupport g) (hc' : HasCompactSupport g') :
    pr τ f (g + g') = pr τ f g + pr τ f g' := by
  simp only [pr, Pi.add_apply, mul_add, map_add]
  exact integral_add (int_left τ hf hg hc) (int_left τ hf hg' hc')

lemma pr_smul_left (c : ℝ) (f g : (Fin n → ℝ) → 𝔸) : pr τ (c • f) g = c • pr τ f g := by
  simp only [pr, Pi.smul_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  exact integral_const_mul c _

lemma pr_smul_right (c : ℝ) (f g : (Fin n → ℝ) → 𝔸) : pr τ f (c • g) = c • pr τ f g := by
  simp only [pr, Pi.smul_apply, mul_smul_comm, map_smul, smul_eq_mul]
  exact integral_const_mul c _

/-- The pairing of fluctuations, `B(x, y) = ∫ τ(x y)`. -/
def pairT : testFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun (x y : testFields n 𝔸) => pr τ (x : (Fin n → ℝ) → 𝔸) y)
    (fun x x' y => pr_add_left τ x.2.1.continuous x'.2.1.continuous y.2.1.continuous y.2.2)
    (fun c x y => by rw [Submodule.coe_smul]; exact pr_smul_left τ c _ _)
    (fun x y y' => pr_add_right τ x.2.1.continuous y.2.1.continuous y'.2.1.continuous y.2.2 y'.2.2)
    (fun c x y => pr_smul_right τ c _ _)

/-- The pairing of a background with a fluctuation. -/
def pairS : smoothFields n 𝔸 →ₗ[ℝ] testFields n 𝔸 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun (f : smoothFields n 𝔸) (x : testFields n 𝔸) =>
    pr τ (f : (Fin n → ℝ) → 𝔸) x)
    (fun f f' x => pr_add_left τ (sm f).continuous (sm f').continuous x.2.1.continuous x.2.2)
    (fun c f x => by rw [Submodule.coe_smul]; exact pr_smul_left τ c _ _)
    (fun f x x' => pr_add_right τ (sm f).continuous x.2.1.continuous x'.2.1.continuous x.2.2 x'.2.2)
    (fun c f x => pr_smul_right τ c _ _)

/-- **Integration by parts** for the trace pairing: `∫ τ(x ∂_μ y) = −∫ τ(∂_μ x y)`. -/
lemma ibp {x y : (Fin n → ℝ) → 𝔸} (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hcx : HasCompactSupport x) (hcy : HasCompactSupport y) (μ : Fin n) :
    ∫ p, τ (x p * dir μ y p) = -∫ p, τ (dir μ x p * y p) := by
  let Bil : 𝔸 →L[ℝ] 𝔸 →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ 𝔸 𝔸 ℝ τ).comp
    (ContinuousLinearMap.mul ℝ 𝔸)
  have hBil : ∀ a b, Bil a b = τ (a * b) := fun a b => rfl
  have hdx : ∀ p, HasFDerivAt x (fderiv ℝ x p) p :=
    fun p => ((hx.differentiable (by simp)) p).hasFDerivAt
  have hdy : ∀ p, HasFDerivAt y (fderiv ℝ y p) p :=
    fun p => ((hy.differentiable (by simp)) p).hasFDerivAt
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := Bil) (v := e μ) (f := x) (g := y) (f' := fderiv ℝ x) (g' := fderiv ℝ y)
    (by simpa [hBil, dir] using (int_right τ (smooth_dir hx μ).continuous hy.continuous
      (compact_dir hcx μ)))
    (by simpa [hBil, dir] using (int_left τ hx.continuous (smooth_dir hy μ).continuous
      (compact_dir hcy μ)))
    (by simpa [hBil] using int_left τ hx.continuous hy.continuous hcy)
    (fun p _ => hdx p) (fun p _ => hdy p)
  simpa [hBil, dir] using h

end Fields

/-! ## 4. The hypotheses hold for smooth fields -/

section Instance
variable {n : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (τ : 𝔸 →L[ℝ] ℝ)

lemma cov_apply (A : (Fin n → ℝ) → 𝔸) (μ : Fin n) (f : (Fin n → ℝ) → 𝔸) (p : Fin n → ℝ) :
    cov A μ f p = dir μ f p + (A p * f p - f p * A p) := rfl

variable {τ}

theorem pair_symm (hτ : ∀ a b, τ (a * b) = τ (b * a)) (x y : testFields n 𝔸) :
    pairT τ x y = pairT τ y x := by
  simp only [pairT, LinearMap.mk₂_apply, pr]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => hτ _ _)

theorem pair_inv (hτ : ∀ a b, τ (a * b) = τ (b * a)) (f : smoothFields n 𝔸)
    (x y : testFields n 𝔸) : pairS τ f (brT x y) = pairT τ (adT f x) y := by
  simp only [pairS, pairT, brT, adT, LinearMap.mk₂_apply, pr, cm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have := hτ ((f : (Fin n → ℝ) → 𝔸) p * (y : (Fin n → ℝ) → 𝔸) p) ((x : (Fin n → ℝ) → 𝔸) p)
  simp only [mul_sub, sub_mul, map_sub, mul_assoc] at this ⊢
  rw [this]

/-- **Antisymmetry of the covariant derivative**, by integration by parts. -/
theorem cov_anti (hτ : ∀ a b, τ (a * b) = τ (b * a)) (A : Fin n → smoothFields n 𝔸) (μ : Fin n)
    (x y : testFields n 𝔸) : pairT τ (covT A μ x) y = -pairT τ x (covT A μ y) := by
  simp only [pairT, LinearMap.mk₂_apply, pr]
  show ∫ p, τ (cov (A μ) μ x p * y.1 p) = -∫ p, τ (x.1 p * cov (A μ) μ y p)
  set a : (Fin n → ℝ) → 𝔸 := ((A μ : smoothFields n 𝔸) : (Fin n → ℝ) → 𝔸)
  have ha : ContDiff ℝ ∞ a := sm (A μ)
  have hx := x.2.1; have hy := y.2.1; have cx := x.2.2; have cy := y.2.2
  have h1 : (fun p => τ (cov a μ x p * y.1 p)) = fun p =>
      τ (dir μ x.1 p * y.1 p) + τ ((a p * x.1 p - x.1 p * a p) * y.1 p) := by
    funext p; simp [cov_apply, add_mul, map_add]
  have h2 : (fun p => τ (x.1 p * cov a μ y p)) = fun p =>
      τ (x.1 p * dir μ y.1 p) - τ ((a p * x.1 p - x.1 p * a p) * y.1 p) := by
    funext p
    have := hτ (x.1 p * y.1 p) (a p)
    simp only [cov_apply, mul_add, map_add, mul_sub, sub_mul, map_sub, mul_assoc] at this ⊢
    rw [this]; ring
  have i1 := int_right τ (smooth_dir hx μ).continuous hy.continuous (compact_dir cx μ)
  have i2 := int_left τ ((ha.mul hx).sub (hx.mul ha)).continuous hy.continuous cy
  have i3 := int_left τ hx.continuous (smooth_dir hy μ).continuous (compact_dir cy μ)
  rw [h1, h2, integral_add i1 i2, integral_sub i3 i2, ibp τ hx hy cx cy μ]
  ring

/-- **Curvature.** `[D_μ, D_ν] x = [F_μν, x]` with `F_μν = ∂_μA_ν − ∂_νA_μ + [A_μ, A_ν]`. -/
theorem cov_curv (A : Fin n → smoothFields n 𝔸) (μ ν : Fin n) (x : testFields n 𝔸) :
    covT A μ (covT A ν x) - covT A ν (covT A μ x) = adT (curvS A μ ν) x := by
  have hx := x.2.1
  refine Subtype.ext (funext fun p => ?_)
  show cov (A μ) μ (cov (A ν) ν x) p - cov (A ν) ν (cov (A μ) μ x) p =
    cm (fun q => dir μ (A ν : (Fin n → ℝ) → 𝔸) q - dir ν (A μ : (Fin n → ℝ) → 𝔸) q +
      cm (A μ) (A ν) q) x p
  simp only [cov_apply]
  rw [dir_cov (sm (A ν)) hx μ ν, dir_cov (sm (A μ)) hx ν μ, dir_comm hx μ ν]
  simp only [cm]
  noncomm_ring

/-- **Leibniz rule.** `D_μ [f, x] = [D_μ f, x] + [f, D_μ x]`. -/
theorem cov_leib (A : Fin n → smoothFields n 𝔸) (μ : Fin n) (f : smoothFields n 𝔸)
    (x : testFields n 𝔸) :
    covT A μ (adT f x) = adT (covS A μ f) x + adT f (covT A μ x) := by
  have hx := x.2.1
  refine Subtype.ext (funext fun p => ?_)
  show cov (A μ) μ (cm (f : (Fin n → ℝ) → 𝔸) (x : (Fin n → ℝ) → 𝔸)) p =
    cm (cov (A μ) μ (f : (Fin n → ℝ) → 𝔸)) (x : (Fin n → ℝ) → 𝔸) p +
      cm (f : (Fin n → ℝ) → 𝔸) (cov (A μ) μ (x : (Fin n → ℝ) → 𝔸)) p
  simp only [cov_apply]
  rw [dir_cm (sm f) hx]
  simp only [cm, cov_apply]
  noncomm_ring

/-- **The Yang–Mills Hessian for smooth, `x`-dependent fields.** For any smooth background
`A_μ(x)` and compactly supported smooth fluctuations, the second variation is
`½ Σ_ν ⟨a_ν, −D²a_ν + 2[F_μν, a_μ]⟩`. -/
theorem continuum_hessian (hτ : ∀ a b, τ (a * b) = τ (b * a)) (A : Fin n → smoothFields n 𝔸)
    (a : Fin n → testFields n 𝔸) :
    quad2 (pairT τ) (pairS τ) brT (covT A) (curvS A) a =
      (1 / 2) * ∑ ν, pairT τ (a ν) (hess2 adT (covT A) (curvS A) a ν) :=
  quad2_eq_hess2 _ _ _ _ _ _ (pair_symm hτ) (cov_anti hτ A) (pair_inv hτ) (cov_curv A) a

/-- **The Ward identity for smooth fields.** If the background solves the Yang–Mills equation
`Σ_μ D_μ F_μν = 0`, pure-gauge fluctuations `D_μ ω` are null modes of the unfixed operator. -/
theorem continuum_ward (A : Fin n → smoothFields n 𝔸)
    (heom : ∀ ν, ∑ μ, covS A μ (curvS A μ ν) = 0) (w0 : testFields n 𝔸) (ν : Fin n) :
    bare2 adT (covT A) (curvS A) (fun μ => covT A μ w0) ν = 0 :=
  gauge_null2 (covS A) (cov_curv A) (cov_leib A) heom w0 ν

end Instance

/-! ## 5. Matrix gauge fields -/

section MatrixFields
open scoped Matrix.Norms.L2Operator

/-- The trace form `−Re tr` on complex matrices, as a continuous `ℝ`-linear functional. -/
def traceForm (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (-(Complex.reLm.comp (Matrix.traceLinearMap (Fin N) ℝ ℂ)))

theorem traceForm_apply {N : ℕ} (a : Matrix (Fin N) (Fin N) ℂ) :
    traceForm N a = -(Matrix.trace a).re := rfl

theorem traceForm_cyclic {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) :
    traceForm N (a * b) = traceForm N (b * a) := by
  rw [traceForm_apply, traceForm_apply, Matrix.trace_mul_comm]

/-- **The Yang–Mills Hessian for `x`-dependent matrix gauge fields** (the field type of Paper II's
links), with any smooth background `A_μ(x)`. -/
theorem matrix_continuum_hessian {N n : ℕ}
    (A : Fin n → smoothFields n (Matrix (Fin N) (Fin N) ℂ))
    (a : Fin n → testFields n (Matrix (Fin N) (Fin N) ℂ)) :
    quad2 (pairT (traceForm N)) (pairS (traceForm N)) brT (covT A) (curvS A) a =
      (1 / 2) * ∑ ν, pairT (traceForm N) (a ν) (hess2 adT (covT A) (curvS A) a ν) :=
  continuum_hessian traceForm_cyclic A a

/-- The Ward identity for `x`-dependent matrix gauge fields on a Yang–Mills background. -/
theorem matrix_continuum_ward {N n : ℕ} (A : Fin n → smoothFields n (Matrix (Fin N) (Fin N) ℂ))
    (heom : ∀ ν, ∑ μ, covS A μ (curvS A μ ν) = 0)
    (w0 : testFields n (Matrix (Fin N) (Fin N) ℂ)) (ν : Fin n) :
    bare2 adT (covT A) (curvS A) (fun μ => covT A μ w0) ν = 0 :=
  continuum_ward A heom w0 ν

end MatrixFields

end PMAction.ContinuumFields
