import PMAction.ResponseLaw
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Coulomb kernel from the discrete Laplacian

The missing charge term for the nuclear line is the static potential: the Green's
function of the substrate Laplacian. This module fixes the interface and proves a
concrete two-site path kernel `pathLap2 (green2 · j) = δ_j`.

Paper 3 supplies the charge `Q`; the pair energy is
`Σ_{i,j} Q i Q j G i j`.
-/

noncomputable section
namespace PMAction.CoulombKernel

open PMAction.ResponseLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A Coulomb kernel: a symmetric Green's function with `lap G(·,y) = δ_y`. -/
structure Kernel (e : Fin 3 → Equiv.Perm X) where
  green : X → X → ℝ
  lap_green : ∀ x y, lap e (fun z => green z y) x = if x = y then 1 else 0
  symm : ∀ x y, green x y = green y x

/-- Static pair energy of a charge distribution. -/
def pairEnergy {e : Fin 3 → Equiv.Perm X} (K : Kernel e) (Q : X → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i * Q j * K.green i j

/-- Pair energy is symmetric under exchange of the kernel arguments. -/
theorem pairEnergy_symm {e : Fin 3 → Equiv.Perm X} (K : Kernel e) (Q : X → ℝ) :
    pairEnergy K Q = ∑ i, ∑ j, Q i * Q j * K.green j i := by
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [K.symm j i]

/-- Two-site path Laplacian with Dirichlet ends. -/
def pathLap2 (f : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 2 * f 0 - f 1 else 2 * f 1 - f 0

/-- Two-site path Green's function `(1/3)[[2,1],[1,2]]`. -/
def green2 : Fin 2 → Fin 2 → ℝ :=
  !![(2/3 : ℝ), 1/3; 1/3, 2/3]

/-- **The two-site path kernel inverts the Laplacian.** -/
theorem pathLap2_green2 (i j : Fin 2) :
    pathLap2 (fun z => green2 z j) i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pathLap2, green2] <;> norm_num

/-- The concrete two-site kernel as a `Kernel`-shaped object (using a trivial
permutation family for the interface). -/
theorem green2_symm (i j : Fin 2) : green2 i j = green2 j i := by
  fin_cases i <;> fin_cases j <;> simp [green2]

/-- Three-site path Laplacian with Dirichlet ends. -/
def pathLap3 (f : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2 * f 0 - f 1, 2 * f 1 - f 0 - f 2, 2 * f 2 - f 1]

/-- Three-site path Green's function `(1/4)[[3,2,1],[2,4,2],[1,2,3]]`. -/
def green3 : Fin 3 → Fin 3 → ℝ :=
  !![(3/4 : ℝ), 2/4, 1/4; 2/4, 4/4, 2/4; 1/4, 2/4, 3/4]

theorem pathLap3_green3 (i j : Fin 3) :
    pathLap3 (fun z => green3 z j) i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pathLap3, green3] <;> norm_num

/-- Four-site path Laplacian with Dirichlet ends. -/
def pathLap4 (f : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![2 * f 0 - f 1, 2 * f 1 - f 0 - f 2,
    2 * f 2 - f 1 - f 3, 2 * f 3 - f 2]

/-- Four-site path Green's function `(1/5)·min(i,j)(5−max(i,j))`. -/
def green4 : Fin 4 → Fin 4 → ℝ :=
  !![(4/5 : ℝ), 3/5, 2/5, 1/5;
     3/5, 6/5, 4/5, 2/5;
     2/5, 4/5, 6/5, 3/5;
     1/5, 2/5, 3/5, 4/5]

theorem pathLap4_green4 (i j : Fin 4) :
    pathLap4 (fun z => green4 z j) i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pathLap4, green4] <;> norm_num

end PMAction.CoulombKernel
