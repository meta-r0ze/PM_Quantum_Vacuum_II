import PMAction.Dirac
import PMAction.DomainWall
import PMAction.DetuningMass
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Real.Pi.Bounds

/-! The squared full two-sector Hamiltonian, before choosing a spinor basis.
This connects the actual inter-sector matrix to the reduced detuning blocks.
No state counting, spectrum multiplicities or continuum limit is assumed. -/
noncomputable section
namespace PMAction.DomainWallSpectrum
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Spin" => Matrix n n ℂ

def plus (Γ : Spin) : Spin := (1/2 : ℝ) • (1+Γ)
def minus (Γ : Spin) : Spin := (1/2 : ℝ) • (1-Γ)
def hop (β Γ : Spin) : Spin := -(β*plus Γ)
def back (β Γ : Spin) : Spin := -(β*minus Γ)

def H (K β Γ : Spin) (δ : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks (K+δ • β) (hop β Γ) (back β Γ) (K+δ • β)

lemma hop_relations (β Γ : Spin) (hβ : β*β=1) (hΓ : Γ*Γ=1)
    (hac : β*Γ = -(Γ*β)) :
    hop β Γ*back β Γ = minus Γ ∧ back β Γ*hop β Γ = plus Γ ∧
      β*hop β Γ+hop β Γ*β = -1 := by
  exact DetuningMass.hop_products_over (𝕜 := ℝ) β Γ hβ hΓ hac

omit [Fintype n] in
lemma plus_add_minus (Γ : Spin) : plus Γ+minus Γ = 1 := by
  simp only [plus, minus, ← smul_add]
  rw [show (1+Γ+(1-Γ) : Spin) = (2 : ℝ) • (1 : Spin) by module]
  simp [smul_smul]

lemma hop_add_back (β Γ : Spin) : hop β Γ+back β Γ = -β := by
  rw [hop, back, ← neg_add, ← mul_add, plus_add_minus, mul_one]

lemma back_anticomm (β Γ : Spin) (hβ : β*β=1) (hΓ : Γ*Γ=1)
    (hac : β*Γ = -(Γ*β)) : β*back β Γ+back β Γ*β = -1 := by
  have hh := (hop_relations β Γ hβ hΓ hac).2.2
  have hs := hop_add_back β Γ
  have ht : β*(hop β Γ+back β Γ)+(hop β Γ+back β Γ)*β = -2 := by
    rw [hs]
    simp only [mul_neg, neg_mul, hβ]
    norm_num
  calc
    _ = (β*(hop β Γ+back β Γ)+(hop β Γ+back β Γ)*β) -
      (β*hop β Γ+hop β Γ*β) := by noncomm_ring
    _ = -2-(-1) := by rw [ht, hh]
    _ = -1 := by norm_num

lemma momentum_anticomm_hops (K β Γ : Spin)
    (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K) :
    K*hop β Γ+hop β Γ*K=0 ∧ K*back β Γ+back β Γ*K=0 := by
  have hp : K*plus Γ = plus Γ*K := by
    simp only [plus, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hg]
  have hm : K*minus Γ = minus Γ*K := by
    simp only [minus, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hg]
  constructor
  · simp only [hop, mul_neg, neg_mul, ← mul_assoc, hb, neg_mul, neg_neg]
    rw [mul_assoc, hp, ← mul_assoc]; abel
  · simp only [back, mul_neg, neg_mul, ← mul_assoc, hb, neg_mul, neg_neg]
    rw [mul_assoc, hm, ← mul_assoc]; abel

/-- The full squared matrix has the two claimed chirality projectors, with
no omitted momentum-hop cross terms. -/
theorem hamiltonian_square (K β Γ : Spin) (δ s : ℝ)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=s • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K) :
    H K β Γ δ*H K β Γ δ =
      fromBlocks ((s+δ^2) • 1+minus Γ) ((-δ) • 1)
        ((-δ) • 1) ((s+δ^2) • 1+plus Γ) := by
  have hh := hop_relations β Γ hβ hΓ hac
  have hbh := back_anticomm β Γ hβ hΓ hac
  have hk := momentum_anticomm_hops K β Γ hb hg
  have hd : (K+δ • β)*(K+δ • β) = (s+δ^2) • (1 : Spin) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hK, hβ, hb,
      pow_two, add_smul]
    module
  unfold H
  rw [fromBlocks_multiply]
  congr 1
  · rw [hd, hh.1]
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    calc
      _ = (K*hop β Γ+hop β Γ*K)+δ • (β*hop β Γ+hop β Γ*β) := by module
      _ = _ := by rw [hk.1, hh.2.2]; simp
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    calc
      _ = (K*back β Γ+back β Γ*K)+δ • (β*back β Γ+back β Γ*β) := by module
      _ = _ := by rw [hk.2, hbh]; simp
  · rw [hd, hh.2.1]; abel

lemma projector_orthogonal (Γ : Spin) (hΓ : Γ*Γ=1) :
    minus Γ*plus Γ=0 ∧ plus Γ*minus Γ=0 := by
  constructor <;> simp only [minus, plus, smul_mul_smul_comm, sub_mul, mul_add,
    add_mul, mul_sub, one_mul, mul_one, hΓ] <;> module

omit [Fintype n] in
lemma block_shift (Γ : Spin) (δ a t : ℝ) :
    fromBlocks (a • 1+minus Γ) ((-δ) • 1) ((-δ) • 1) (a • 1+plus Γ) -
      t • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
    fromBlocks ((a-t) • 1+minus Γ) ((-δ) • 1) ((-δ) • 1) ((a-t) • 1+plus Γ) := by
  have hi : t • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      fromBlocks (t • (1 : Spin)) 0 0 (t • (1 : Spin)) := by
    rw [← fromBlocks_one, fromBlocks_smul]; simp
  rw [hi, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  congr 1 <;> module

/-- The full operator obeys the reduced-block polynomial, not merely an
independently postulated scalar characteristic equation. -/
theorem hamiltonian_polynomial (K β Γ : Spin) (δ s : ℝ)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=s • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K) :
    (H K β Γ δ*H K β Γ δ-(s+δ^2) • 1) *
      (H K β Γ δ*H K β Γ δ-(s+δ^2+1) • 1) = δ^2 • 1 := by
  rw [hamiltonian_square K β Γ δ s hβ hΓ hac hK hb hg,
    block_shift, block_shift]
  have hm : (-1 : ℝ) • (1 : Spin)+minus Γ = -plus Γ := by
    simp only [plus, minus]; module
  have hp : (-1 : ℝ) • (1 : Spin)+plus Γ = -minus Γ := by
    simp only [plus, minus]; module
  have hd : s+δ^2-(s+δ^2+1) = (-1 : ℝ) := by ring
  simp only [sub_self, zero_smul, zero_add, hd, hm, hp]
  rw [fromBlocks_multiply]
  have hi : δ^2 • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      fromBlocks (δ^2 • (1 : Spin)) 0 0 (δ^2 • (1 : Spin)) := by
    rw [← fromBlocks_one, fromBlocks_smul]; simp
  rw [hi]
  have ho := projector_orthogonal Γ hΓ
  congr 1
  · simp only [mul_neg, ho.1, neg_zero, zero_add, smul_mul_smul_comm, one_mul]; module
  · simp only [mul_smul_comm, smul_mul_assoc, one_mul, mul_one, mul_neg]; module
  · simp only [mul_smul_comm, smul_mul_assoc, one_mul, mul_one, mul_neg]; module
  · simp only [mul_neg, ho.2, neg_zero, add_zero, smul_mul_smul_comm, one_mul]; module

/-- Every real-energy eigenpair of the full Hamiltonian satisfies the derived
operator polynomial. No reduced block is assumed as an extra premise. -/
theorem energy_constraint (K β Γ : Spin) (δ s E : ℝ)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=s • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (he : H K β Γ δ *ᵥ v = E • v) :
    (E^2-s-δ^2)*(E^2-s-δ^2-1)=δ^2 := by
  have hs : (H K β Γ δ*H K β Γ δ)*ᵥ v = E^2 • v := by
    rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, he, smul_smul, pow_two]
  have hleft : (H K β Γ δ*H K β Γ δ-(s+δ^2) • 1)*ᵥ v =
      (E^2-(s+δ^2)) • v := by
    rw [Matrix.sub_mulVec, hs, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hright : (H K β Γ δ*H K β Γ δ-(s+δ^2+1) • 1)*ᵥ v =
      (E^2-(s+δ^2+1)) • v := by
    rw [Matrix.sub_mulVec, hs, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hp := congrArg (fun M => M*ᵥ v) (hamiltonian_polynomial K β Γ δ s hβ hΓ hac hK hb hg)
  rw [← Matrix.mulVec_mulVec, hright, Matrix.mulVec_smul, hleft, smul_smul,
    Matrix.smul_mulVec, Matrix.one_mulVec] at hp
  have hz : ((E^2-(s+δ^2+1))*(E^2-(s+δ^2))-δ^2) • v = 0 := by
    rw [sub_smul, hp, sub_self]
  have hc := (smul_eq_zero.mp hz).resolve_right hv
  nlinarith

/-- All real energies lie on the light or heavy squared branch. This does not
yet assert existence or multiplicity of each branch in a chosen representation. -/
theorem energy_branches (K β Γ : Spin) (δ s E : ℝ)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=s • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (he : H K β Γ δ *ᵥ v = E • v) :
    E^2=s+(DetuningMass.lightMass δ)^2 ∨
      E^2=s+(DetuningMass.lightMass δ+1)^2 := by
  have hp := energy_constraint K β Γ δ s E hβ hΓ hac hK hb hg v hv he
  have hm := DetuningMass.mass_relation δ
  have hd : δ^2=(DetuningMass.lightMass δ)^2+DetuningMass.lightMass δ := by nlinarith
  rw [hd] at hp
  have hf : (E^2-s-(DetuningMass.lightMass δ)^2)*
      (E^2-s-(DetuningMass.lightMass δ+1)^2)=0 := by linear_combination hp
  rcases mul_eq_zero.mp hf with h | h
  · left; linarith
  · right; linarith

/-- With nonnegative momentum square, a nonzero zero mode requires both zero
momentum square and zero Wilson detuning. -/
theorem kernel_requires_zero (K β Γ : Spin) (δ s : ℝ) (hs : 0 ≤ s)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=s • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (he : H K β Γ δ *ᵥ v = 0) :
    s=0 ∧ δ=0 := by
  have h0 : H K β Γ δ*ᵥ v=(0 : ℝ) • v := by simpa using he
  have hp := energy_constraint K β Γ δ s 0 hβ hΓ hac hK hb hg v hv h0
  norm_num at hp
  have hcross := mul_nonneg hs (sq_nonneg δ)
  have hd4 := sq_nonneg (δ^2)
  have hss := sq_nonneg s
  have hd4eq : (δ^2)^2=0 := by nlinarith
  have hd2eq : δ^2=0 := (sq_eq_zero_iff).mp hd4eq
  have hd0 : δ=0 := (sq_eq_zero_iff).mp hd2eq
  refine ⟨?_, hd0⟩
  rw [hd0] at hp
  nlinarith

def wilson (k : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, (1-Real.cos (k j))
def kineticNorm (k : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, (Real.sin (k j)^2)

theorem kinetic_nonnegative (k : Fin 3 → ℝ) : 0 ≤ kineticNorm k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem wilson_zero (k : Fin 3 → ℝ) : wilson k=0 ↔ ∀ j, Real.cos (k j)=1 := by
  constructor
  · intro h j
    have ht : 1-Real.cos (k j) ≤ wilson k :=
      Finset.single_le_sum (fun i _ => sub_nonneg.mpr (Real.cos_le_one _)) (Finset.mem_univ j)
    linarith [Real.cos_le_one (k j)]
  · intro h; simp [wilson, h]

/-- There are no extra zero modes anywhere in the momentum cell, not merely
at its corners, for the stated Wilson-point Hamiltonian hypotheses. -/
theorem no_extra_zero_modes (K β Γ : Spin) (k : Fin 3 → ℝ)
    (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi)
    (hβ : β*β=1) (hΓ : Γ*Γ=1) (hac : β*Γ = -(Γ*β))
    (hK : K*K=kineticNorm k • 1) (hb : K*β = -(β*K)) (hg : K*Γ=Γ*K)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (he : H K β Γ (wilson k)*ᵥ v=0) :
    k=0 := by
  have hz := kernel_requires_zero K β Γ (wilson k) (kineticNorm k)
    (kinetic_nonnegative k) hβ hΓ hac hK hb hg v hv he
  have hc := (wilson_zero k).mp hz.2
  funext j
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [(hcell j).1, Real.pi_pos])
    (by linarith [(hcell j).2, Real.pi_pos])).mp (hc j)

def momentum (α : Fin 3 → Spin) (k : Fin 3 → ℝ) : Spin :=
  ∑ j, Real.sin (k j) • α j

/-- The actual sine-momentum operator supplies the hypotheses used above. -/
theorem kinetic_relations (α : Fin 3 → Spin) (β Γ : Spin) (k : Fin 3 → ℝ)
    (hc : Dirac.Clifford α β) (hg : ∀ j, α j*Γ=Γ*α j) :
    momentum α k*momentum α k=kineticNorm k • 1 ∧
    momentum α k*β=-(β*momentum α k) ∧ momentum α k*Γ=Γ*momentum α k := by
  have hab : ∀ j, α j*β=-(β*α j) := fun j => eq_neg_of_add_eq_zero_left (hc.2.2.2 j)
  refine ⟨?_, ?_, ?_⟩
  · have h := (Dirac.dispersion_iff_clifford α β).mpr hc (fun j => Real.sin (k j)) 0
    simpa [momentum, Dirac.H, kineticNorm, Fin.sum_univ_three] using h
  · simp only [momentum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      hab, smul_neg, Finset.sum_neg_distrib]
  · simp only [momentum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hg]

/-- Specialization to the displayed Wilson-point sine-momentum Hamiltonian. -/
theorem wilson_point_zero_only_at_origin (α : Fin 3 → Spin) (β Γ : Spin) (k : Fin 3 → ℝ)
    (hc : Dirac.Clifford α β) (hΓ : Γ*Γ=1) (hac : β*Γ=-(Γ*β))
    (hg : ∀ j, α j*Γ=Γ*α j) (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0)
    (he : H (momentum α k) β Γ (wilson k)*ᵥ v=0) : k=0 := by
  have hk := kinetic_relations α β Γ k hc hg
  exact no_extra_zero_modes (momentum α k) β Γ k hcell hc.2.1 hΓ hac
    hk.1 hk.2.1 hk.2.2 v hv he

theorem wilson_bounds (k : Fin 3 → ℝ) : 0 ≤ wilson k ∧ wilson k ≤ 6 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (Real.cos_le_one (k j)))
  · calc
      wilson k ≤ ∑ _j : Fin 3, (2 : ℝ) := Finset.sum_le_sum
        (fun j _ => by linarith [Real.neg_one_le_cos (k j)])
      _ = 6 := by norm_num

theorem kinetic_upper (k : Fin 3 → ℝ) : kineticNorm k ≤ 3 := by
  calc
    kineticNorm k ≤ ∑ _j : Fin 3, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => Real.sin_sq_le_one (k j))
    _ = 3 := by norm_num

/-- A coarse uniform bound is enough for phase alias control. It does not
select a physical clock step or prove finite-range locality of an exponential. -/
theorem energy_bandwidth (α : Fin 3 → Spin) (β Γ : Spin) (k : Fin 3 → ℝ)
    (hc : Dirac.Clifford α β) (hΓ : Γ*Γ=1) (hac : β*Γ=-(Γ*β))
    (hg : ∀ j, α j*Γ=Γ*α j) (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (E : ℝ)
    (he : H (momentum α k) β Γ (wilson k)*ᵥ v=E • v) : |E|<8 := by
  have hk := kinetic_relations α β Γ k hc hg
  have hbranch := energy_branches (momentum α k) β Γ (wilson k) (kineticNorm k) E
    hc.2.1 hΓ hac hk.1 hk.2.1 hk.2.2 v hv he
  have hw := wilson_bounds k
  have hms := DetuningMass.mass_relation (wilson k)
  have hm0 := (DetuningMass.mass_le (wilson k)).1
  have hw2 : (wilson k)^2 ≤ 36 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hm6 : DetuningMass.lightMass (wilson k) ≤ 6 := by
    nlinarith [sq_nonneg (DetuningMass.lightMass (wilson k)-6)]
  have hm2 : (DetuningMass.lightMass (wilson k))^2 ≤ 36 := by
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm6)]
  have he2 : E^2<64 := by
    rcases hbranch with h | h <;> nlinarith [kinetic_upper k]
  apply abs_lt.mpr
  constructor <;> nlinarith [sq_nonneg (E-8), sq_nonneg (E+8)]

/-- For an explicitly bounded time step, no nonzero real eigenenergy aliases
to the unit phase. This completes the scalar bandwidth premise on all momenta. -/
theorem eigenphase_one_only_at_origin (α : Fin 3 → Spin) (β Γ : Spin) (k : Fin 3 → ℝ)
    (hc : Dirac.Clifford α β) (hΓ : Γ*Γ=1) (hac : β*Γ=-(Γ*β))
    (hg : ∀ j, α j*Γ=Γ*α j) (hcell : ∀ j, -Real.pi ≤ k j ∧ k j ≤ Real.pi)
    (v : (n ⊕ n) → ℂ) (hv : v ≠ 0) (E τ : ℝ)
    (he : H (momentum α k) β Γ (wilson k)*ᵥ v=E • v)
    (hτ : τ ≠ 0) (hstep : |τ| ≤ 1/2)
    (hphase : Complex.exp (-(τ*E : ℝ)*Complex.I)=1) : k=0 := by
  have hb := energy_bandwidth α β Γ k hc hΓ hac hg v hv E he
  have hphasebound : |τ*E|<2*Real.pi := by
    rw [abs_mul]
    have hm := mul_le_mul_of_nonneg_right hstep (abs_nonneg E)
    nlinarith [Real.pi_gt_three]
  have hE := DomainWall.update_zero_mode hτ hphasebound hphase
  rw [hE, zero_smul] at he
  exact wilson_point_zero_only_at_origin α β Γ k hc hΓ hac hg hcell v hv he

end PMAction.DomainWallSpectrum
