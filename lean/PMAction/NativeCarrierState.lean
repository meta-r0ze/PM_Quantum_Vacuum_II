import PMAction.NativeCarrierProtocol

/-!
# An explicit finite state contract for the native reference routing

Finite-alphabet registers are indexed by spatial sites and actual carrier
labels. Their update is a reversible coordinate permutation with the proved
neighbour bound. The one-hot Boolean sector is exactly the location/carrier
state space whose complex-linear lift gives the reference walk. It is not
the entire configuration space, nor a derivation of quantum amplitudes/statistics.
-/
noncomputable section
namespace PMAction.NativeCarrierState
open Matrix NativeCarrierProtocol
abbrev C := ActualRootRepair.C
variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev Config (X A : Type*) := X × C → A

/-- Actual finite register evolution; no coherent frame operation is executed. -/
def tick {A : Type*} (o : X) (e : Equiv.Perm X) : Equiv.Perm (Config X A) where
  toFun s := s ∘ lookup o e
  invFun s := s ∘ (lookup o e).symm
  left_inv s := by funext p; simp
  right_inv s := by funext p; simp

theorem state_count (A : Type*) [Fintype A] :
    Fintype.card (Config X A) = (Fintype.card A) ^ (8 * Fintype.card X) := by
  simp [Config, Fintype.card_prod, CarrierEvents.carrier_card, mul_comm]

/-- Every additive observation of register contents is retained by routing. -/
theorem conserved {A M : Type*} [AddCommMonoid M] (o : X) (e : Equiv.Perm X)
    (s : Config X A) (f : A → M) :
    (∑ p, f (tick o e s p)) = ∑ p, f (s p) := by
  change (∑ p, (fun q => f (s q)) (lookup o e p)) = _
  exact Equiv.sum_comp (lookup o e) (fun q => f (s q))

omit [Fintype X] in
/-- Agreement on the three allowed cells is sufficient to predict an output register. -/
theorem local_dependency {A : Type*} (o : X) (e : Equiv.Perm X) (s t : Config X A) (x : X) (c : C)
    (h : ∀ y d, y=x ∨ y=e x ∨ y=e⁻¹ x → s (y,d)=t (y,d)) :
    tick o e s (x,c) = tick o e t (x,c) := by
  exact h _ _ (causal_lookup o e (x,c))

def occupation (s : Config X Bool) : ℕ := ∑ p, if s p then 1 else 0

theorem occupation_preserved (o : X) (e : Equiv.Perm X) (s : Config X Bool) :
    occupation (tick o e s) = occupation s := conserved o e s (fun b => if b then 1 else 0)

def oneHot (p : X × C) : Config X Bool := fun q => if q=p then true else false

omit [Fintype X] in
lemma oneHot_injective : Function.Injective (oneHot (X := X)) := by
  intro p q h
  have hh := congrFun h p
  simpa [oneHot] using hh

lemma oneHot_occupation (p : X × C) : occupation (oneHot p) = 1 := by
  simp [occupation, oneHot]

/-- The finite sector, not an assumption that every register configuration has one excitation. -/
theorem occupation_one (s : Config X Bool) (hs : occupation s=1) : ∃ p, s=oneHot p := by
  have hc : (Finset.univ.filter (fun p => s p=true)).card = 1 := by
    calc
      _ = occupation s := by
        unfold occupation
        rw [Finset.card_filter]
      _ = 1 := hs
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hc
  refine ⟨p, ?_⟩
  funext q
  have hh : s q=true ↔ q=p := by
    have he := congrArg (fun S : Finset (X × C) => q ∈ S) hp
    simpa using he
  by_cases hq:q=p
  · simpa only [oneHot, hq, ↓reduceIte] using hh.mpr hq
  · have hf : s q=false := by cases hv:s q <;> simp_all
    simp [oneHot, hq, hf]

abbrev SingleSector (X : Type*) [Fintype X] [DecidableEq X] := {s : Config X Bool // occupation s=1}

def oneExcitationEquiv : (X × C) ≃ SingleSector X := Equiv.ofBijective
  (fun p => ⟨oneHot p,oneHot_occupation p⟩)
  ⟨fun p q h => oneHot_injective (congrArg Subtype.val h), fun s => by
    obtain ⟨p,hp⟩ := occupation_one s.1 s.2
    exact ⟨p,Subtype.ext hp.symm⟩⟩

theorem single_sector_count : Fintype.card (SingleSector X) = 8 * Fintype.card X := by
  rw [← Fintype.card_congr (oneExcitationEquiv (X := X))]
  simp [Fintype.card_prod, CarrierEvents.carrier_card, mul_comm]

omit [Fintype X] in
/-- An occupied mode moves by the inverse of the matrix's row-to-input lookup. -/
theorem oneHot_step (o : X) (e : Equiv.Perm X) (p : X × C) :
    tick o e (oneHot p) = oneHot ((lookup o e).symm p) := by
  ext q
  simp only [tick, Equiv.coe_fn_mk, Function.comp_apply, oneHot,
    ← Equiv.eq_symm_apply]

/-- The existing reference walk is exactly the linear lift of that single-sector action. -/
theorem amplitude_basis_action (o : X) (e : Equiv.Perm X) (p : X × C) :
    RootCarrierWalk.update o e *ᵥ Pi.single p 1 = Pi.single ((lookup o e).symm p) 1 := by
  rw [NativeCarrierProtocol.matrix_eq, Matrix.permMatrix_mulVec]
  ext q
  simp [Pi.single_apply, ← Equiv.eq_symm_apply]

/-- Once the native finite action and linear-amplitude lift are specified,
there is no further matrix choice. Linearity itself remains a modeling input. -/
theorem unique_linear_lift (o : X) (e : Equiv.Perm X)
    (U : Matrix (X × C) (X × C) ℂ)
    (h : ∀ p, U *ᵥ Pi.single p 1 = Pi.single ((lookup o e).symm p) 1) :
    U = RootCarrierWalk.update o e := by
  apply Matrix.ext_of_mulVec_single
  intro p
  rw [h, amplitude_basis_action]

end PMAction.NativeCarrierState
