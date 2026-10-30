import PMAction.CarrierVacuumEvolution

/-! Coordinate observations form a quotient by even background amplitudes.
No physical state is deleted: any initial amplitude is permitted. Dynamics on
unobserved modes may remain arbitrary if they do not feed the coordinate readout.
The coordinate-readout contract and linear-amplitude semantics remain inputs. -/
noncomputable section
namespace PMAction.CarrierReadoutQuotient
open Matrix CarrierVacuumSector
open scoped Matrix.Norms.Operator

def readout (c : Fin 3) := (embedding c)ᴴ

/-- Exactly the antipodally even amplitudes are invisible to coordinate readouts. -/
theorem invisible_iff_even (c : Fin 3) (ψ : Labels c → ℂ) :
    readout c *ᵥ ψ=0 ↔ parity c *ᵥ ψ=ψ := by
  have hr : readout c * oddProjector c=readout c := by
    rw [readout, ← projector, ← Matrix.mul_assoc, isometry, Matrix.one_mul]
  constructor
  · intro h
    have hz : oddProjector c *ᵥ ψ=0 := by
      rw [← projector, ← mulVec_mulVec, ← readout, h, mulVec_zero]
    have hh : ψ - parity c *ᵥ ψ=0 := by
      have hn : (1/2 : ℂ) ≠ 0 := by norm_num
      simpa only [oddProjector, smul_mulVec, sub_mulVec, one_mulVec,
        smul_eq_zero_iff_right hn] using hz
    exact (sub_eq_zero.mp hh).symm
  · intro h
    have hz : oddProjector c *ᵥ ψ=0 := by
      simp [oddProjector, smul_mulVec, sub_mulVec, h]
    rw [← hr, ← mulVec_mulVec, hz, mulVec_zero]

/-- This is the exact equivalence relation observed by the supplied readout. -/
theorem same_readout_iff (c : Fin 3) (ψ φ : Labels c → ℂ) :
    readout c *ᵥ ψ=readout c *ᵥ φ ↔ parity c *ᵥ (ψ-φ)=ψ-φ := by
  rw [← invisible_iff_even, Matrix.mulVec_sub, sub_eq_zero]

/-- Canonical odd representative; this is a mathematical representation, not
an asserted physical projection or erasure of even backgrounds. -/
theorem canonical_representative (c : Fin 3) (ψ : Labels c → ℂ) :
    embedding c *ᵥ (readout c *ᵥ ψ)=oddProjector c *ᵥ ψ ∧
      readout c *ᵥ (oddProjector c *ᵥ ψ)=readout c *ᵥ ψ := by
  constructor
  · rw [readout, mulVec_mulVec, projector]
  · rw [mulVec_mulVec, readout, ← projector, ← Matrix.mul_assoc, isometry, Matrix.one_mul]

lemma generator (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) :
    readout c * hamiltonian c p k δ = ConcreteFermion.hamiltonian k δ * readout c := by
  rw [readout, identification c p hp hp1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    isometry, Matrix.one_mul]

/-- The unobserved generator is free subject to the explicit no-feedback
condition. It need not vanish, and the initial amplitude need not be odd. -/
theorem observed_evolution (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (D : Matrix (Labels c) (Labels c) ℂ)
    (hD : readout c * D=0) (z : ℂ) (ψ : Labels c → ℂ) :
    readout c *ᵥ (NormedSpace.exp (z • (hamiltonian c p k δ + D)) *ᵥ ψ) =
      NormedSpace.exp (z • ConcreteFermion.hamiltonian k δ) *ᵥ (readout c *ᵥ ψ) := by
  have hg : ConcreteFermion.hamiltonian k δ * readout c =
      readout c * (hamiltonian c p k δ + D) := by
    rw [Matrix.mul_add, hD, add_zero, generator c p hp hp1]
  have he := RectangularEvolution.scaled _ _ _ hg z
  rw [mulVec_mulVec, ← he, ← mulVec_mulVec]

end PMAction.CarrierReadoutQuotient
