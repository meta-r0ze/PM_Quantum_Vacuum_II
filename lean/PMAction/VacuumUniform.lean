import PMAction.VacuumSplit

/-! The zero-momentum preservation theorem also holds for actual finite-lattice states. -/
noncomputable section
namespace PMAction.VacuumSplit
open Matrix ConcreteFermion
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X]

def uniform (v : Sites → ℂ) : X × Sites → ℂ := fun z => v z.2

lemma perm_kronecker_uniform (e : Equiv.Perm X) (A : Matrix Sites Sites ℂ) (v : Sites → ℂ) :
    (e.permMatrix ℂ ⊗ₖ A)*ᵥuniform v = uniform (X := X) (A*ᵥv) := by
  ext ⟨x,a⟩
  simp [mulVec, dotProduct, uniform, Fintype.sum_prod_type, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

lemma coefficient_sum (j : Fin 3) : SplitUpdate.coefficient j+(SplitUpdate.coefficient j)ᴴ=beta8 := by
  have h := WilsonSplit.directionSymbol_phase j 0
  simpa [direction_zero] using h.symm

lemma neighbor_uniform (e : Equiv.Perm X) (j : Fin 3) (v : Sites → ℂ) :
    SplitUpdate.neighbor e j*ᵥuniform v = uniform (X := X) (beta8*ᵥv) := by
  rw [SplitUpdate.neighbor, add_mulVec, conjTranspose_permMatrix,
    perm_kronecker_uniform, perm_kronecker_uniform]
  have hc := congrArg (fun A : Matrix Sites Sites ℂ => A*ᵥv) (coefficient_sum j)
  ext z
  simpa [add_mulVec, uniform] using congrFun hc z.2

lemma direction_uniform (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) (v : Sites → ℂ) :
    SplitUpdate.direction e j τ*ᵥuniform v = uniform (X := X) (rotation τ*ᵥv) := by
  simp only [SplitUpdate.direction, rotation, LocalUnitary.rotation,
    add_mulVec, smul_mulVec, one_mulVec, neighbor_uniform]
  rfl

lemma onsite_uniform (Q : Matrix Sites Sites ℂ) (v : Sites → ℂ) :
    SplitUpdate.onsite (X := X) Q*ᵥuniform v = uniform (Q*ᵥv) := by
  simpa only [permMatrix_refl, SplitUpdate.onsite] using perm_kronecker_uniform (Equiv.refl X) Q v

/-- Constant states evolve by the actual zero-momentum matrix on every finite torus. -/
theorem update_uniform (N : ℕ) (τ : ℝ) (v : Sites → ℂ) :
    update N τ*ᵥuniform v = uniform (X := Fin 3 → Fin N) (momentumUpdate 0 τ*ᵥv) := by
  simp only [update, SplitUpdate.cubicUpdate, SplitUpdate.update, ← mulVec_mulVec,
    direction_uniform, onsite_uniform, momentumUpdate, Pi.zero_apply, direction_zero, rotation]

/-- The four-dimensional Hamiltonian vacuum is fixed as a spatially uniform lattice state. -/
theorem uniform_vacuum_preserved (N : ℕ) (τ : ℝ) (v : Sites → ℂ) (hv : wall*ᵥv=0) :
    update N τ*ᵥuniform v = uniform (X := Fin 3 → Fin N) v := by
  rw [update_uniform, vacuum_preserved τ v hv]

end PMAction.VacuumSplit
