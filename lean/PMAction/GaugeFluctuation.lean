import PMAction.RunningResponse

noncomputable section
namespace PMAction.GaugeFluctuation
open Finset

/-! ## The gauge-fixed Yang–Mills Hessian about a background -/

section Hessian
variable {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ}
  (B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (br : M →ₗ[ℝ] M →ₗ[ℝ] M)
  (D : Fin n → Module.End ℝ M) (F : Fin n → Fin n → M)

/-- Covariant curl `D_μ a_ν − D_ν a_μ` of the fluctuation. -/
def curl (a : Fin n → M) (μ ν : Fin n) : M := D μ (a ν) - D ν (a μ)

/-- Background covariant divergence `Σ_μ D_μ a_μ` (the background gauge condition). -/
def gdiv (a : Fin n → M) : M := ∑ μ, D μ (a μ)

/-- Yang–Mills action of `A + a` about the background `A` (field strength `F`), with the
background Feynman gauge-fixing term `½‖D·a‖²`. -/
def action (a : Fin n → M) : ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, B (F μ ν + curl D a μ ν + br (a μ) (a ν))
      (F μ ν + curl D a μ ν + br (a μ) (a ν)) + (1 / 2) * B (gdiv D a) (gdiv D a)

def lin (a : Fin n → M) : ℝ := (1 / 4) * ∑ μ, ∑ ν, 2 * B (F μ ν) (curl D a μ ν)

/-- The quadratic part. The `2 B(F, [a, a])` cross term is the second source of `F`. -/
def quad (a : Fin n → M) : ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, (B (curl D a μ ν) (curl D a μ ν) + 2 * B (F μ ν) (br (a μ) (a ν))) +
    (1 / 2) * B (gdiv D a) (gdiv D a)

def cub (a : Fin n → M) : ℝ := (1 / 4) * ∑ μ, ∑ ν, 2 * B (curl D a μ ν) (br (a μ) (a ν))

def quart (a : Fin n → M) : ℝ := (1 / 4) * ∑ μ, ∑ ν, B (br (a μ) (a ν)) (br (a μ) (a ν))

/-- The fluctuation operator: `(K a)_ν = −Σ_μ D_μ D_μ a_ν + 2 Σ_μ [F_μν, a_μ]`. -/
def hess (a : Fin n → M) (ν : Fin n) : M :=
  -(∑ μ, D μ (D μ (a ν))) + (2 : ℝ) • ∑ μ, br (F μ ν) (a μ)

/-- **Expansion of the action in the fluctuation.** -/
theorem action_expansion (hB : ∀ x y, B x y = B y x) (a : Fin n → M) (t : ℝ) :
    action B br D F (t • a) = (1 / 4) * ∑ μ, ∑ ν, B (F μ ν) (F μ ν) + t * lin B D F a +
      t ^ 2 * quad B br D F a + t ^ 3 * cub B br D a + t ^ 4 * quart B br a := by
  have hc : ∀ μ ν, curl D (t • a) μ ν = t • curl D a μ ν := by
    intro μ ν; simp [curl, smul_sub]
  have hz : ∀ μ ν, br ((t • a) μ) ((t • a) ν) = (t ^ 2) • br (a μ) (a ν) := by
    intro μ ν; simp [smul_smul, sq]
  have hd : gdiv D (t • a) = t • gdiv D a := by simp [gdiv, smul_sum]
  have hpt : ∀ X Y Z : M, B (X + t • Y + t ^ 2 • Z) (X + t • Y + t ^ 2 • Z) =
      B X X + t * (2 * B X Y) + t ^ 2 * (B Y Y + 2 * B X Z) + t ^ 3 * (2 * B Y Z) +
        t ^ 4 * B Z Z := by
    intro X Y Z
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB Y X, hB Z X, hB Z Y]; ring
  unfold action lin quad cub quart
  simp only [hc, hz, hd, hpt, map_smul, LinearMap.smul_apply, smul_eq_mul, sum_add_distrib,
    ← mul_sum]
  ring

/-- **The fluctuation operator has spin coupling `2F`.** Antisymmetry of `D` (integration by
parts), invariance of the pairing, and curvature `[D_μ, D_ν] = [F_μν, ·]` turn the quadratic
part into `½ Σ_ν ⟨a_ν, (K a)_ν⟩`. One `F` comes from the commutator and one from the cross
term `2⟨F, [a, a]⟩`. -/
theorem quad_eq_hess (hB : ∀ x y, B x y = B y x)
    (hD : ∀ μ x y, B (D μ x) y = -B x (D μ y))
    (hinv : ∀ f x y, B f (br x y) = B (br f x) y)
    (hcurv : ∀ μ ν x, D μ (D ν x) - D ν (D μ x) = br (F μ ν) x) (a : Fin n → M) :
    quad B br D F a = (1 / 2) * ∑ ν, B (a ν) (hess br D F a ν) := by
  set P : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D μ (D μ (a ν))) with hP
  set R : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D μ (D ν (a μ))) with hR
  set S : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (D ν (D μ (a μ))) with hS
  set G : Fin n → Fin n → ℝ := fun μ ν => B (a ν) (br (F μ ν) (a μ)) with hG
  have e1 : ∀ μ ν, B (curl D a μ ν) (curl D a μ ν) = -P μ ν - P ν μ + R μ ν + R ν μ := by
    intro μ ν
    simp only [curl, map_sub, LinearMap.sub_apply, hD, hP, hR]
    ring
  have e2 : ∀ μ ν, B (F μ ν) (br (a μ) (a ν)) = G μ ν := by
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
  have rhs : ∑ ν, B (a ν) (hess br D F a ν) =
      -∑ ν, ∑ μ, P μ ν + 2 * ∑ ν, ∑ μ, G μ ν := by
    simp only [hess, map_add, map_neg, map_smul, map_sum, smul_eq_mul, hP, hG,
      sum_add_distrib, sum_neg_distrib, ← mul_sum]
  unfold quad
  simp only [e1, e2, e3, sum_add_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  rw [rhs]
  simp only [cP, cR, cG]
  linear_combination (1 / 2 : ℝ) * hRS

/-- **Ghost operator.** The background gauge condition varies along a gauge direction `D ω` by
`Σ_μ D_μ D_μ ω`. The Faddeev–Popov operator has no spin coupling. -/
theorem ghost_operator (ω : M) (t : ℝ) :
    gdiv D (fun μ => t • D μ ω) = t • ∑ μ, D μ (D μ ω) := by
  simp [gdiv, smul_sum]

end Hessian

/-! ## A constant field in one plane -/

/-- Field-strength pattern of a constant field in the `(0, 1)` plane. -/
def planar (l ν : Fin 4) : ℝ := if l = 0 ∧ ν = 1 then 1 else if l = 1 ∧ ν = 0 then -1 else 0

theorem planar_hess {M : Type*} [AddCommGroup M] [Module ℝ M]
    (br : M →ₗ[ℝ] M →ₗ[ℝ] M) (D : Fin 4 → Module.End ℝ M) (f : M) (a : Fin 4 → M) (ν : Fin 4) :
    hess br D (fun l ν => planar l ν • f) a ν =
      -(∑ μ, D μ (D μ (a ν))) + ∑ l, (2 * planar l ν) • br f (a l) := by
  simp [hess, smul_sum, smul_smul]

/-- The vector-index spin matrix of `K` on a charged mode, where `[f, ·]` acts as `c`. -/
def spinMatrix (c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := fun ν l => 2 * c * (planar l ν : ℂ)

/-- The helicity matrix in the `(0, 1)` plane. -/
def helicity : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- With `[f, ·] = i q b` on the charged mode, the spin coupling is `2 q b` times the helicity
matrix. -/
theorem charged_spin (qb : ℝ) : spinMatrix (Complex.I * qb) = ((2 * qb : ℝ) : ℂ) • helicity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinMatrix, planar, helicity] <;> ring

def basisU : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 1, 0, 0; Complex.I, -Complex.I, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def basisV : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1 / 2, -Complex.I / 2, 0, 0; 1 / 2, Complex.I / 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **Helicity spectrum `{+1, −1, 0, 0}`.** `basisU` is invertible and diagonalises the
helicity matrix. -/
theorem helicity_spectrum :
    basisV * basisU = 1 ∧ basisU * basisV = 1 ∧
      basisV * helicity * basisU = Matrix.diagonal ![1, -1, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [basisU, basisV, helicity, Matrix.mul_apply, Fin.sum_univ_four] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- The spin eigenvalues. -/
def helicityEig : Fin 4 → ℝ := ![1, -1, 0, 0]

/-! ## The spin-1 heat-kernel coefficient -/

open Real

/-- **Vector minus ghosts.** Four components with spin shifts `2 ε x` (`ε ∈ {1, −1, 0, 0}`),
minus the two Faddeev–Popov ghost components (no spin shift), leave one helicity pair with
`a = 2`. -/
theorem vector_kernel (x : ℝ) :
    (∑ i, x / sinh x * exp (2 * helicityEig i * x)) - 2 * (x / sinh x) =
      x / sinh x * (exp (2 * x) + exp (-(2 * x))) := by
  simp [Fin.sum_univ_four, helicityEig]; ring_nf

/-- The vector-plus-ghost kernel is the Landau level sum of a helicity pair with `a = 2`. -/
theorem vector_level_sum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 2 * x * (exp (-((2 * n + 1) * x) + 2 * x) +
        exp (-((2 * n + 1) * x) - 2 * x)))
      ((∑ i, x / sinh x * exp (2 * helicityEig i * x)) - 2 * (x / sinh x)) := by
  rw [vector_kernel]; exact RunningResponse.pair_kernel 2 hx

/-- **The spin-1 `B²` coefficient is `2² − 1/3 = 11/3`.** -/
theorem vector_coefficient :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
      |(∑ i, x / sinh x * exp (2 * helicityEig i * x)) - 2 * (x / sinh x) - 2 -
          11 / 3 * x ^ 2| ≤ C * x ^ 4 := by
  obtain ⟨C, hC, h⟩ := RunningResponse.pair_coefficient 2
  refine ⟨C, hC, fun x hx h1 => ?_⟩
  have := h x hx (by linarith) (by rw [abs_two]; linarith)
  rw [vector_kernel]
  convert this using 3; norm_num

/-- `spinTerm 2` is the bosonic sign times the derived spin-1 coefficient. -/
theorem spin_one_term :
    ((RunningCoefficients.spinTerm 2 : ℚ) : ℝ) = (2 : ℝ) ^ 2 - 1 / 3 := by
  rw [RunningResponse.spin_term_from_response]; norm_num

end PMAction.GaugeFluctuation
