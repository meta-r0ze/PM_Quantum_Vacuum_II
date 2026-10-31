import PMAction.LatticeGibbs

/-!
# Gauge invariance of PM's lattice action and its measure

`YANG-MILLS-STATUS.md` item 3 asks for gauge-invariant observables and a gauge-invariant measure.
A lattice gauge transformation assigns a unitary `g(y)` to every site and acts on links by
`U(y, v) ↦ g(y) U(y, v) g(y + h v)ᴴ`.

* `gauge_unitary`: gauge-transformed links are unitary.
* `holonomy_gauge`: every D₄ triangle holonomy transforms by conjugation at its base site,
  `U_△ ↦ g(x) U_△ g(x)ᴴ`.
* `wilson_gauge`: so each Wilson term `Re tr(1 − U_△)` (a Wilson loop) is gauge invariant.
* `action_gauge`, `weight_gauge`: PM's D₄ action and its survival weight `exp(−β S)` are gauge
  invariant. Not proved: invariance of the Gibbs measure itself (a pushforward statement needing
  two-sided Haar invariance on each link; `UnitaryHaar` provides left invariance only).
-/

noncomputable section
namespace PMAction.GaugeInvariance
open Matrix

variable {N : ℕ}
local notation "V4" => (Fin 4 → ℝ)

/-- A lattice gauge transformation of the links. -/
def gauge (g : V4 → Matrix (Fin N) (Fin N) ℂ) (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) :
    V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ :=
  fun y v h => g y * U y v h * (g (y + h • v))ᴴ

theorem gauge_unitary (g : V4 → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ y, g y ∈ unitary _)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ y v h, U y v h ∈ unitary _) :
    ∀ y v h, gauge g U y v h ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := fun y v h =>
  (unitary _).mul_mem ((unitary _).mul_mem (hg y) (hU y v h)) (Unitary.star_mem (hg _))

/-- **Triangle holonomies transform by conjugation.** -/
theorem holonomy_gauge (g : V4 → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ y, g y ∈ unitary _)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (x a b : V4) (h : ℝ) :
    LinkConsistency.holonomy (gauge g U) x a b h =
      g x * LinkConsistency.holonomy U x a b h * (g x)ᴴ := by
  have e : x + h • a + h • (b - a) = x + h • b := by
    rw [smul_sub]; abel
  have hu : ∀ y, (g y)ᴴ * g y = 1 := fun y => (Unitary.mem_iff.mp (hg y)).1
  have hu' : ∀ y (M : Matrix (Fin N) (Fin N) ℂ), (g y)ᴴ * (g y * M) = M := fun y M => by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  simp only [LinkConsistency.holonomy, gauge, e, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc, hu']

/-- **Wilson terms are gauge invariant.** -/
theorem wilson_gauge (g : V4 → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ y, g y ∈ unitary _)
    (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (x a b : V4) (h : ℝ) :
    trace (1 - LinkConsistency.holonomy (gauge g U) x a b h) =
      trace (1 - LinkConsistency.holonomy U x a b h) := by
  have hu : (g x)ᴴ * g x = 1 := (Unitary.mem_iff.mp (hg x)).1
  rw [holonomy_gauge g hg, trace_sub, trace_sub, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc, hu, Matrix.mul_one]

/-- **PM's D₄ action is gauge invariant.** -/
theorem action_gauge (g : V4 → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ y, g y ∈ unitary _)
    (X : Finset V4) (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (h : ℝ) :
    LatticeGibbs.action X (gauge g U) h = LatticeGibbs.action X U h := by
  unfold LatticeGibbs.action
  simp only [wilson_gauge g hg]

/-- **The survival weight is gauge invariant.** -/
theorem weight_gauge (g : V4 → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ y, g y ∈ unitary _)
    (X : Finset V4) (U : V4 → V4 → ℝ → Matrix (Fin N) (Fin N) ℂ) (h β : ℝ) :
    Real.exp (-β * LatticeGibbs.action X (gauge g U) h) =
      Real.exp (-β * LatticeGibbs.action X U h) := by
  rw [action_gauge g hg]

end PMAction.GaugeInvariance
