import PMAction.FiniteEncoding
import PMAction.StateIdentification

/-!
# Independent labels carried by disjoint occupied register banks

Two finite banks of Boolean registers, with exactly one occupied register in
each, realize a product of label spaces. Relabeling either bank is an actual
reversible configuration update, fixes the other bank, and has the corresponding
tensor-product action on coherent encoded amplitudes. The readout holds on all
ambient amplitudes. This supplies a finite configuration construction rather
than reusing spinor coordinates as internal labels.

The banks, the occupancy sector and admission of these relabelings/coherent
amplitudes remain supplied. No preparation, spatial locality, statistics or
primitive price is inferred, and this is not an E8 gate-selection theorem.
-/

noncomputable section
namespace PMAction.IndependentRegisters
open Matrix NativeObservation
open scoped Kronecker
variable {a b : Type*} [DecidableEq a] [DecidableEq b]
attribute [local instance] Classical.propDecidable

abbrev Configuration (a b : Type*) := (a ⊕ b) → Bool

def encode (p : a × b) : Configuration a b :=
  Sum.elim (fun i => decide (i = p.1)) (fun j => decide (j = p.2))

/-- Exactly one occupied register in each bank, stated without a product label. -/
def Valid (q : Configuration a b) : Prop :=
  (∃ i : a, ∀ j, q (.inl j) = decide (j = i)) ∧
  (∃ i : b, ∀ j, q (.inr j) = decide (j = i))

theorem encode_injective : Function.Injective (encode (a := a) (b := b)) := by
  intro p q h
  apply Prod.ext
  · have hh := congrFun h (.inl p.1)
    simpa [encode] using hh.symm
  · have hh := congrFun h (.inr p.2)
    simpa [encode] using hh.symm

theorem valid_iff (q : Configuration a b) : Valid q ↔ ∃ p, encode p = q := by
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨(i,j), ?_⟩
    funext x
    cases x with
    | inl k => exact (hi k).symm
    | inr k => exact (hj k).symm
  · rintro ⟨⟨i,j⟩, rfl⟩
    exact ⟨⟨i, fun _ => rfl⟩, ⟨j, fun _ => rfl⟩⟩

def sectorEquiv : (a × b) ≃ {q : Configuration a b // Valid q} :=
  Equiv.ofBijective (fun p => ⟨encode p, (valid_iff _).mpr ⟨p,rfl⟩⟩) (by
    constructor
    · intro p q h
      exact encode_injective (congrArg Subtype.val h)
    · intro q
      obtain ⟨p,hp⟩ := (valid_iff q.val).mp q.property
      exact ⟨p, Subtype.ext hp⟩)

variable [Fintype a] [Fintype b]

theorem sector_card : Fintype.card {q : Configuration a b // Valid q} =
    Fintype.card a * Fintype.card b := by
  classical
  rw [← Fintype.card_congr (sectorEquiv (a := a) (b := b)), Fintype.card_prod]

omit [DecidableEq a] [DecidableEq b] in
theorem register_count : Fintype.card (a ⊕ b) = Fintype.card a + Fintype.card b :=
  Fintype.card_sum

/-- Reindexing existing registers, on every configuration including invalid ones. -/
def update (e : Equiv.Perm a) (f : Equiv.Perm b) : Equiv.Perm (Configuration a b) where
  toFun q := fun x => q ((Equiv.sumCongr e f).symm x)
  invFun q := fun x => q ((Equiv.sumCongr e f) x)
  left_inv q := by funext x; simp
  right_inv q := by funext x; simp

omit [Fintype a] [Fintype b] in
theorem update_encode (e : Equiv.Perm a) (f : Equiv.Perm b) (p : a × b) :
    update e f (encode p) = encode ((Equiv.prodCongr e f) p) := by
  funext x
  cases x <;> simp [update, encode, Equiv.symm_apply_eq]

omit [Fintype a] [Fintype b] in
theorem update_valid (e : Equiv.Perm a) (f : Equiv.Perm b)
    (q : Configuration a b) (hq : Valid q) : Valid (update e f q) := by
  obtain ⟨p, rfl⟩ := (valid_iff q).mp hq
  rw [update_encode]
  exact (valid_iff _).mpr ⟨_, rfl⟩

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
/-- A first-bank operation leaves every second-bank bit unchanged. -/
theorem right_untouched (e : Equiv.Perm a) (q : Configuration a b) (j : b) :
    update e (Equiv.refl b) q (.inr j) = q (.inr j) := rfl

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem left_untouched (f : Equiv.Perm b) (q : Configuration a b) (i : a) :
    update (Equiv.refl a) f q (.inl i) = q (.inl i) := rfl

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem updates_commute (e : Equiv.Perm a) (f : Equiv.Perm b) :
    update e (Equiv.refl b) * update (Equiv.refl a) f =
      update (Equiv.refl a) f * update e (Equiv.refl b) := by
  ext q x
  cases x <;> rfl

/-- Number of occupied physical registers, on any configuration. -/
def occupied (q : Configuration a b) : ℕ := ∑ x, if q x then 1 else 0

theorem occupied_encode (p : a × b) : occupied (encode p) = 2 := by
  simp [occupied, encode, Fintype.sum_sum_type]

omit [DecidableEq a] [DecidableEq b] in
/-- Every bank relabeling conserves occupation, including outside the encoded sector. -/
theorem occupied_update (e : Equiv.Perm a) (f : Equiv.Perm b) (q : Configuration a b) :
    occupied (update e f q) = occupied q := by
  exact (Equiv.sumCongr e f).symm.sum_comp (fun x => if q x then 1 else 0)

def embedding : Matrix (Configuration a b) (a × b) ℂ := FiniteEncoding.matrix encode

theorem isometry : (embedding (a := a) (b := b))ᴴ * embedding (a := a) (b := b) = 1 :=
  FiniteEncoding.isometry encode encode_injective

theorem pairing (ψ φ : a × b → ℂ) :
    star (embedding *ᵥ ψ) ⬝ᵥ (embedding *ᵥ φ) = star ψ ⬝ᵥ φ :=
  FiniteEncoding.pairing encode encode_injective ψ φ

theorem observed (e : Equiv.Perm a) (f : Equiv.Perm b) :
    Obs embedding ((update e f).permMatrix ℂ) (Equiv.Perm.permMatrix ℂ (Equiv.prodCongr e f)) :=
  ⟨FiniteEncoding.intertwining encode _ _ (update_encode e f),
   FiniteEncoding.readout_intertwining encode _ _ (update_encode e f)⟩

omit [Fintype a] [Fintype b] in
theorem tensor_permutation (e : Equiv.Perm a) (f : Equiv.Perm b) :
    Equiv.Perm.permMatrix ℂ (Equiv.prodCongr e f) = e.permMatrix ℂ ⊗ₖ f.permMatrix ℂ := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : e i = k <;> by_cases h' : f j = l <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Prod.ext_iff, h, h']

/-- Exact independent-factor dynamics, with no unobserved feedback. -/
theorem tensor_observed (e : Equiv.Perm a) (f : Equiv.Perm b) :
    Obs embedding ((update e f).permMatrix ℂ) (e.permMatrix ℂ ⊗ₖ f.permMatrix ℂ) := by
  rw [← tensor_permutation]
  exact observed e f

end PMAction.IndependentRegisters
