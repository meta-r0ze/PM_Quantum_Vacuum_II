import PMAction.RegisterPrograms

/-!
# Number-conserving register realization of a finite Hamiltonian

Matrix entries become hard-core hops between two registers of the first bank;
the second bank is untouched. On the one-occupation-per-bank sector this is
exactly the supplied Hamiltonian tensored with the payload identity. Hermitian
completion gives unitary evolution with exact readout on all configurations.

This specifies a higher-occupation completion, rather than setting all other
sectors to zero. Bank allocation, coherent hopping admission and prices are
inputs. In particular it does not derive fermionic statistics or E8 gate costs.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.RegisterHamiltonian
open Matrix NativeObservation IndependentRegisters
open scoped Kronecker
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def number (i : a) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  diagonal (fun q => if q (.inl i) then 1 else 0)

def modeNumber (i : a) : Matrix (a × b) (a × b) ℂ :=
  diagonal (fun p => if p.1 = i then 1 else 0)

omit [DecidableEq a] [DecidableEq b] in
theorem number_hermitian (i : a) : (number (b := b) i).IsHermitian := by
  unfold IsHermitian number
  rw [diagonal_conjTranspose]
  congr 1
  funext q
  simp

omit [Fintype a] [Fintype b] in
theorem modeNumber_hermitian (i : a) : (modeNumber (b := b) i).IsHermitian := by
  unfold IsHermitian modeNumber
  rw [diagonal_conjTranspose]
  congr 1
  funext p
  simp

theorem number_observed (i : a) : Obs embedding (number (b := b) i) (modeNumber i) := by
  have h : number (b := b) i * embedding = embedding * modeNumber i := by
    ext q p
    by_cases hq : q = encode p
    · subst q
      by_cases hi : i = p.1
      · simp [number, modeNumber, diagonal_mul, mul_diagonal,
          IndependentRegisters.embedding, FiniteEncoding.matrix, encode, hi]
      · have hi' := Ne.symm hi
        simp [number, modeNumber, diagonal_mul, mul_diagonal,
          IndependentRegisters.embedding, FiniteEncoding.matrix, encode, hi, hi']
    · simp [number, modeNumber, diagonal_mul, mul_diagonal,
        IndependentRegisters.embedding, FiniteEncoding.matrix, hq]
  refine ⟨h, ?_⟩
  have hh := congrArg conjTranspose h
  simpa only [conjTranspose_mul, (number_hermitian (b := b) i).eq,
    (modeNumber_hermitian (b := b) i).eq] using hh

def hop (i j : a) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  if i = j then number i else
    number i * (1 - number j) * (update (Equiv.swap i j) (Equiv.refl b)).permMatrix ℂ

def elementary (i j : a) : Matrix (a × b) (a × b) ℂ := fun p q =>
  if p.1 = i ∧ q.1 = j ∧ p.2 = q.2 then 1 else 0

private theorem mode_hop (i j : a) :
    (if i = j then modeNumber (b := b) i else
      modeNumber i * (1 - modeNumber j) *
        ((Equiv.swap i j).permMatrix ℂ ⊗ₖ (1 : Matrix b b ℂ))) = elementary i j := by
  ext p q
  by_cases hij : i = j
  · subst j
    by_cases hp : p.1 = i <;> by_cases hq : q.1 = i <;> by_cases hb : p.2 = q.2 <;>
      simp [modeNumber, elementary, hp, hq, hb, Prod.ext_iff, diagonal_apply]
    all_goals aesop
  · by_cases hp : p.1 = i
    · by_cases hq : q.1 = j <;> by_cases hb : p.2 = q.2 <;>
        simp [hij, modeNumber, elementary, mul_sub, diagonal_mul_diagonal,
          diagonal_mul, hp, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          one_apply, hq, hb]
      all_goals aesop
    · simp [hij, modeNumber, elementary, mul_sub, diagonal_mul_diagonal,
        diagonal_mul, hp]

theorem hop_observed (i j : a) : Obs embedding (hop (b := b) i j) (elementary i j) := by
  have hh : Obs embedding (hop (b := b) i j)
      (if i = j then modeNumber i else
        modeNumber i * (1 - modeNumber j) *
          ((Equiv.swap i j).permMatrix ℂ ⊗ₖ (1 : Matrix b b ℂ))) := by
    by_cases hij : i = j
    · simp only [hop, hij, ↓reduceIte]
      exact number_observed (b := b) j
    · simp only [hop, hij, ↓reduceIte]
      have hs := tensor_observed (Equiv.swap i j) (Equiv.refl b)
      simp only [permMatrix_refl] at hs
      exact NativeObservation.mul
        (NativeObservation.mul (number_observed (b := b) i)
          (NativeObservation.sub NativeObservation.one (number_observed (b := b) j))) hs
  rw [mode_hop] at hh
  exact hh

def raw (A : Matrix a a ℂ) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  ∑ i, ∑ j, A i j • hop i j

private theorem hop_zero_of_not_step (i j : a) (q r : Configuration a b)
    (hne : q ≠ r) (hs : update (Equiv.swap i j) (Equiv.refl b) q ≠ r) : hop i j q r = 0 := by
  by_cases hij : i = j
  · simp [hop, hij, number, hne]
  · simp [hop, hij, number, mul_sub, diagonal_mul_diagonal, diagonal_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hs]

/-- No elementary matrix entry connects different total-occupation sectors. -/
theorem hop_occupation_zero (i j : a) (q r : Configuration a b)
    (h : occupied q ≠ occupied r) : hop i j q r = 0 := by
  apply hop_zero_of_not_step
  · intro he
    exact h (congrArg occupied he)
  · intro he
    exact h ((occupied_update (Equiv.swap i j) (Equiv.refl b) q).symm.trans
      (congrArg occupied he))

/-- No elementary hop changes any bit in the payload bank. -/
theorem hop_payload_zero (i j : a) (q r : Configuration a b) (k : b)
    (h : q (.inr k) ≠ r (.inr k)) : hop i j q r = 0 := by
  apply hop_zero_of_not_step
  · intro he
    exact h (congrFun he (.inr k))
  · intro he
    exact h ((right_untouched (Equiv.swap i j) q k).symm.trans (congrFun he (.inr k)))

theorem raw_occupation_zero (A : Matrix a a ℂ) (q r : Configuration a b)
    (h : occupied q ≠ occupied r) : raw A q r = 0 := by
  simp [raw, Matrix.sum_apply, Matrix.smul_apply, hop_occupation_zero _ _ q r h]

theorem raw_payload_zero (A : Matrix a a ℂ) (q r : Configuration a b) (k : b)
    (h : q (.inr k) ≠ r (.inr k)) : raw A q r = 0 := by
  simp [raw, Matrix.sum_apply, Matrix.smul_apply, hop_payload_zero _ _ q r k h]

omit [Fintype b] in
private theorem elementary_sum (A : Matrix a a ℂ) :
    (∑ i, ∑ j, A i j • elementary (b := b) i j) = A ⊗ₖ (1 : Matrix b b ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, elementary]
  simp [ite_and, one_apply, eq_comm]

theorem raw_observed (A : Matrix a a ℂ) :
    Obs embedding (raw (b := b) A) (A ⊗ₖ (1 : Matrix b b ℂ)) := by
  rw [← elementary_sum]
  unfold raw
  constructor
  · simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      (hop_observed (b := b) _ _).1]
  · simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      (hop_observed (b := b) _ _).2]

/-- Hermitian hard-core completion on every occupation sector. -/
def generator (A : Matrix a a ℂ) : Matrix (Configuration a b) (Configuration a b) ℂ :=
  (1/2 : ℂ) • (raw A + (raw A)ᴴ)

theorem generator_occupation_zero (A : Matrix a a ℂ) (q r : Configuration a b)
    (h : occupied q ≠ occupied r) : generator A q r = 0 := by
  simp [generator, Matrix.smul_apply, Matrix.add_apply, conjTranspose_apply,
    raw_occupation_zero A q r h, raw_occupation_zero A r q (Ne.symm h)]

theorem generator_payload_zero (A : Matrix a a ℂ) (q r : Configuration a b) (k : b)
    (h : q (.inr k) ≠ r (.inr k)) : generator A q r = 0 := by
  simp [generator, Matrix.smul_apply, Matrix.add_apply, conjTranspose_apply,
    raw_payload_zero A q r k h, raw_payload_zero A r q k (Ne.symm h)]

private theorem diagonal_conserved {s : Type*} (label : Configuration a b → s)
    (weight : s → ℂ) (A : Matrix a a ℂ)
    (h : ∀ q r, label q ≠ label r → generator A q r = 0) :
    generator A * diagonal (fun q => weight (label q)) =
      diagonal (fun q => weight (label q)) * generator A := by
  classical
  ext q r
  rw [mul_diagonal, diagonal_mul]
  by_cases he : label q = label r
  · rw [he, mul_comm]
  · rw [h q r he, zero_mul, mul_zero]

/-- Total occupation is conserved by the complete coherent evolution. -/
theorem evolution_occupation (A : Matrix a a ℂ) (z : ℂ) :
    NormedSpace.exp (z • generator (b := b) A) * diagonal (fun q => (occupied q : ℂ)) =
      diagonal (fun q => (occupied q : ℂ)) * NormedSpace.exp (z • generator A) :=
  RectangularEvolution.scaled _ _ _
    (diagonal_conserved occupied (fun n => (n : ℂ)) A (generator_occupation_zero A)) z

/-- Every payload bit is conserved by evolution, on all occupation sectors. -/
theorem evolution_payload (A : Matrix a a ℂ) (z : ℂ) (k : b) :
    NormedSpace.exp (z • generator A) * diagonal (fun q : Configuration a b => if q (.inr k) then (1 : ℂ) else 0) =
      diagonal (fun q : Configuration a b => if q (.inr k) then (1 : ℂ) else 0) *
        NormedSpace.exp (z • generator A) :=
  RectangularEvolution.scaled _ _ _
    (diagonal_conserved (fun q : Configuration a b => q (.inr k)) (fun t => if t then 1 else 0) A
      (fun q r => generator_payload_zero A q r k)) z

theorem generator_hermitian (A : Matrix a a ℂ) : (generator (b := b) A).IsHermitian := by
  unfold IsHermitian generator
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  norm_num

theorem generator_observed (A : Matrix a a ℂ) (hA : A.IsHermitian) :
    Obs embedding (generator (b := b) A) (A ⊗ₖ (1 : Matrix b b ℂ)) := by
  apply NativeObservation.herm (raw_observed A)
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, conjTranspose_one]

theorem evolution_readout (A : Matrix a a ℂ) (hA : A.IsHermitian) (z : ℂ)
    (ψ : Configuration a b → ℂ) :
    embeddingᴴ *ᵥ (NormedSpace.exp (z • generator A) *ᵥ ψ) =
      NormedSpace.exp (z • (A ⊗ₖ (1 : Matrix b b ℂ))) *ᵥ (embeddingᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (generator_observed A hA) z) ψ

theorem evolution_unitary (A : Matrix a a ℂ) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • generator (b := b) A) ∈
      unitary (Matrix (Configuration a b) (Configuration a b) ℂ) := by
  exact NativeObservation.exp_unitary (generator (b := b) A) (generator_hermitian A) t

end PMAction.RegisterHamiltonian
