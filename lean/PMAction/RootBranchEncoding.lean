import PMAction.RootTransferAccounting

/-!
# A coherent branch encoded in an actual moving root orbit

Two distinct actual carrier labels, not an extra abstract register, encode one
amplitude doublet. The root exchanges the branches; its reconstructed phase
preserves this subspace. This identifies the internal branch action, not a
physical phase implementation, a payload tensor factor or a primitive tariff.
-/
noncomputable section
namespace PMAction.RootBranchEncoding
open Matrix CommonResponse
variable {n : Type*} [Fintype n] [DecidableEq n]

def embed (e : Equiv.Perm n) (a : n) (x : Fin 2 → ℂ) : n → ℂ :=
  x 0 • Pi.single a 1 + x 1 • Pi.single (e a) 1

omit [Fintype n] in
lemma coordinates (e : Equiv.Perm n) (a : n) (ha : e a ≠ a) (x : Fin 2 → ℂ) :
    embed e a x a = x 0 ∧ embed e a x (e a) = x 1 := by
  simp [embed, ha, Ne.symm ha]

omit [Fintype n] in
theorem injective (e : Equiv.Perm n) (a : n) (ha : e a ≠ a) :
    Function.Injective (embed e a) := by
  intro x y h
  have h0 := congrFun h a
  have h1 := congrFun h (e a)
  rw [(coordinates e a ha x).1, (coordinates e a ha y).1] at h0
  rw [(coordinates e a ha x).2, (coordinates e a ha y).2] at h1
  funext j
  fin_cases j <;> assumption

theorem population (e : Equiv.Perm n) (a : n) (ha : e a ≠ a) (x : Fin 2 → ℂ) :
    nsq (embed e a x) = nsq x := by
  rw [LinkExpansion.nsq_eq, LinkExpansion.nsq_eq]
  have h (i : n) : Complex.normSq (embed e a x i) =
      (if i = a then Complex.normSq (x 0) else 0) +
      (if i = e a then Complex.normSq (x 1) else 0) := by
    by_cases h0 : i = a
    · subst i
      simp [embed, Ne.symm ha]
    · by_cases h1 : i = e a
      · subst i
        simp [embed, ha]
      · simp [embed, h0, h1]
  simp_rw [h]
  simp [Finset.sum_add_distrib, Fin.sum_univ_two]

def swap (x : Fin 2 → ℂ) : Fin 2 → ℂ := ![x 1, x 0]

theorem root_action (e : Equiv.Perm n) (he : Function.Involutive e) (a : n)
    (x : Fin 2 → ℂ) :
    e.permMatrix ℂ *ᵥ embed e a x = embed e a (swap x) := by
  rw [embed, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    RootTransferAccounting.basis_move e he, RootTransferAccounting.basis_move e he, he a]
  simp only [embed, swap, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

def mix (θ : ℝ) (x : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(Real.cos θ : ℂ) * x 0 + (Complex.I * (Real.sin θ : ℂ)) * x 1,
    (Complex.I * (Real.sin θ : ℂ)) * x 0 + (Real.cos θ : ℂ) * x 1]

theorem rotation_action (e : Equiv.Perm n) (he : Function.Involutive e)
    (a : n) (θ : ℝ) (x : Fin 2 → ℂ) :
    LocalUnitary.rotation (e.permMatrix ℂ) θ *ᵥ embed e a x =
      embed e a (mix θ x) := by
  rw [LocalUnitary.rotation, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, root_action e he]
  simp only [embed, swap, mix, Matrix.cons_val_zero, Matrix.cons_val_one]
  module

omit [Fintype n] in
lemma embed_smul (e : Equiv.Perm n) (a : n) (z : ℂ) (x : Fin 2 → ℂ) :
    embed e a (z • x) = z • embed e a x := by
  simp only [embed, Pi.smul_apply, smul_eq_mul]
  module

open scoped Matrix.Norms.Operator in
/-- The full reconstructed dynamics restricts to the actual root branch,
with its scalar phase retained. -/
theorem phase_action (e : Equiv.Perm n) (he : Function.Involutive e)
    (a : n) (p t : ℝ) (x : Fin 2 → ℂ) :
    RootTransferPhase.phase e p t *ᵥ embed e a x =
      embed e a (Complex.exp (-(RootTransferPhase.gap p*t/2 : ℝ)*Complex.I) •
        mix (RootTransferPhase.gap p*t/2) x) := by
  have h := InvolutionSpectral.phase_rotation (e.permMatrix ℂ)
    (RootTransferPhase.gap p*t/2)
  rw [show 2*(RootTransferPhase.gap p*t/2)=RootTransferPhase.gap p*t by ring] at h
  rw [RootTransferPhase.phase_formula e he, h, smul_mulVec, rotation_action e he, embed_smul]

/-- Every actual glue class has a moved pair carrying this faithful isometric branch. -/
theorem actual_branch (c : Fin 3) :
    ∃ a : CarrierEvents.Carrier c, CarrierEvents.reflect c a ≠ a ∧
      Function.Injective (embed (CarrierEvents.reflect c) a) ∧
      ∀ x, nsq (embed (CarrierEvents.reflect c) a x) = nsq x := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < (CarrierEvents.active c).card by
    rw [CarrierEvents.active_card]; norm_num)
  have hm := (Finset.mem_filter.mp ha).2
  exact ⟨a,hm,injective _ _ hm,population _ _ hm⟩

end PMAction.RootBranchEncoding
