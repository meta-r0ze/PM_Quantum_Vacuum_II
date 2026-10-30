import PMAction.CarrierEvents
import PMAction.FullCarrierIdentification

/-!
# The intrinsic antipodal-odd sector of actual carrier amplitudes

Negation pairs the eight actual minimal vectors into four antipodal pairs.
Linear coordinate readouts span the odd sector. The certified D4 root words
preserve it; invariance under the full E8 Weyl group is not claimed. This is
not yet a uniquely selected physical state space or a derivation of amplitudes.
-/
noncomputable section
namespace PMAction.CarrierParity
open Matrix CarrierEvents

def negateBox (k : Box) : Box := fun i => (k i).rev

lemma negate_valid : ∀ (c : Fin 3) (k : Box), valid c k → valid c (negateBox k) := by
  decide +kernel

def antipode (c : Fin 3) : Equiv.Perm (Carrier c) where
  toFun v := ⟨negateBox v.1,negate_valid c v.1 v.2⟩
  invFun v := ⟨negateBox v.1,negate_valid c v.1 v.2⟩
  left_inv v := by apply Subtype.ext; funext i; simp [negateBox]
  right_inv v := by apply Subtype.ext; funext i; simp [negateBox]

lemma antipode_involutive (c : Fin 3) : Function.Involutive (antipode c) := by
  intro v; apply Subtype.ext; funext i; simp [antipode,negateBox]

lemma antipode_vector : ∀ (c : Fin 3) (v : Carrier c), vector (antipode c v) = -vector v := by
  decide +kernel

lemma no_fixed_antipode : ∀ (c : Fin 3) (v : Carrier c), antipode c v ≠ v := by
  decide +kernel

/-- Tight coordinate frame; no carrier class or axis is fitted to a physical value. -/
lemma coordinate_gram : ∀ (c : Fin 3) (i j : Fin 4),
    (∑ v : Carrier c, vector v i * vector v j) = if i=j then 8 else 0 := by
  decide +kernel

/-- Distinct non-antipodal carriers in any one class are orthogonal. -/
lemma carrier_gram : ∀ (c : Fin 3) (v w : Carrier c),
    (∑ i, vector v i * vector w i) =
      (if v=w then 4 else 0) - (if antipode c v=w then 4 else 0) := by
  decide +kernel

def scale : ℂ := ((1 / Real.sqrt 8 : ℝ) : ℂ)
def embedding (c : Fin 3) : Matrix (Carrier c) (Fin 4) ℂ :=
  fun v i => scale * (vector v i : ℂ)

lemma scale_sq : star scale * scale = (1/8 : ℂ) := by
  have hr : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 8 ≠ 0 := by positivity
  have h : (1 / Real.sqrt 8 : ℝ) * (1 / Real.sqrt 8) = 1/8 := by
    field_simp
    nlinarith
  calc
    _ = ((1 / Real.sqrt 8 * (1 / Real.sqrt 8) : ℝ) : ℂ) := by simp [scale]
    _ = (1/8 : ℂ) := by rw [h]; norm_num

/-- The eight label amplitudes contain a canonical four-coordinate contrast sector. -/
theorem isometry (c : Fin 3) : (embedding c)ᴴ * embedding c = 1 := by
  ext i j
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (coordinate_gram c i j)
  push_cast at hg
  have he (v : Carrier c) : star (embedding c v i) * embedding c v j =
      (1/8 : ℂ) * ((vector v i : ℂ) * (vector v j : ℂ)) := by
    simp only [embedding,star_mul,star_intCast]
    calc
      _ = (star scale*scale)*((vector v i : ℂ)*(vector v j : ℂ)) := by ring
      _ = _ := by rw [scale_sq]
  simp only [mul_apply,conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum,hg]
  by_cases h:i=j <;> simp [h,Matrix.one_apply]

/-- The orthogonal projector is fixed intrinsically by antipodal oddness. -/
theorem projector (c : Fin 3) : embedding c * (embedding c)ᴴ =
    (1/2 : ℂ) • (1-(antipode c).permMatrix ℂ) := by
  ext v w
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (carrier_gram c v w)
  push_cast at hg
  have he (i : Fin 4) : embedding c v i * star (embedding c w i) =
      (1/8 : ℂ) * ((vector v i : ℂ)*(vector w i : ℂ)) := by
    simp only [embedding,star_mul,star_intCast]
    calc
      _ = (star scale*scale)*((vector v i : ℂ)*(vector w i : ℂ)) := by ring
      _ = _ := by rw [scale_sq]
  simp only [mul_apply,conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum,hg]
  by_cases hv:v=w
  · subst w
    norm_num [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,no_fixed_antipode]
  · by_cases ha:antipode c v=w <;>
      norm_num [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,hv,ha]

lemma odd_image (c : Fin 3) (x : Fin 4 → ℂ) :
    (antipode c).permMatrix ℂ *ᵥ (embedding c *ᵥ x) = -(embedding c *ᵥ x) := by
  rw [Matrix.permMatrix_mulVec]
  ext v
  simp [embedding,mulVec,dotProduct,antipode_vector]

/-- Complete sector identification, not just a sufficient family of vectors. -/
theorem range_iff_odd (c : Fin 3) (ψ : Carrier c → ℂ) :
    (∃ x : Fin 4 → ℂ, embedding c *ᵥ x=ψ) ↔
      (antipode c).permMatrix ℂ *ᵥ ψ = -ψ := by
  constructor
  · rintro ⟨x,rfl⟩; exact odd_image c x
  · intro h
    refine ⟨(embedding c)ᴴ *ᵥ ψ,?_⟩
    rw [mulVec_mulVec,projector,smul_mulVec,sub_mulVec,one_mulVec,h]
    module

lemma recover (c : Fin 3) (x : Fin 4 → ℂ) :
    (embedding c)ᴴ *ᵥ (embedding c *ᵥ x) = x := by
  rw [mulVec_mulVec,isometry,one_mulVec]

lemma coordinate_sum : ∀ (c : Fin 3) (i : Fin 4), (∑ v : Carrier c, vector v i)=0 := by
  decide +kernel

/-- Coordinate readouts carry no uniform carrier-amplitude component. -/
theorem uniform_excluded (c : Fin 3) : (embedding c)ᴴ *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  ext i
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (coordinate_sum c i)
  push_cast at hg
  simp only [mulVec,dotProduct,conjTranspose_apply,embedding,star_mul,star_intCast,mul_one]
  rw [← Finset.sum_mul,hg,zero_mul]
  rfl

end PMAction.CarrierParity
