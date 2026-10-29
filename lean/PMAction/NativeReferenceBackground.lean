import PMAction.NativeCarrierState
import PMAction.WalkReferenceCycle

/-!
# Stationary backgrounds of the native finite reference protocol

For a connected neighbour orbit, stationarity forces the two streams to carry
one common reference per payload label. Positive sitewise value-change prices
select exactly stationary configurations, but do not select a reference value,
nonzero population, the physical update, or that price rule. A common clock
baseline can be retained separately. This is not indefinite restoration of
arbitrary independent incoming disturbances in a finite closed system.
-/
noncomputable section
namespace PMAction.NativeReferenceBackground
open Matrix NativeCarrierProtocol NativeCarrierState
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Each cell is reached from the coupling site by the supplied neighbour permutation. -/
def Connected (o : X) (e : Equiv.Perm X) : Prop := ∀ x, ∃ n : ℕ, e^[n] o=x

omit [DecidableEq X] in
lemma close_missing_edge {A : Type*} (o : X) (e : Equiv.Perm X) (f : X → A)
    (h : ∀ x, x ≠ o → f (e x)=f x) : f (e o)=f o := by
  classical
  let g : X → ℤ := fun x => if f x=f o then 1 else 0
  have hs : (∑ x, (g (e x)-g x)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp]
    simp
  have ho : (∑ x, (g (e x)-g x)) = g (e o)-g o := by
    apply Finset.sum_eq_single o
    · intro x _ hx
      simp [g,h x hx]
    · simp
  have he : g (e o)=g o := sub_eq_zero.mp (ho.symm.trans hs)
  by_contra hn
  simp [g,hn] at he

lemma invariant_of_except {A : Type*} (o : X) (e : Equiv.Perm X) (f : X → A)
    (h : ∀ x, x ≠ o → f (e x)=f x) : ∀ x, f (e x)=f x := by
  intro x
  by_cases hx:x=o
  · subst x; exact close_missing_edge o e f h
  · exact h x hx

omit [Fintype X] [DecidableEq X] in
lemma orbit_constant {A : Type*} (o : X) (e : Equiv.Perm X) (hc : Connected o e)
    (f : X → A) (h : ∀ x, f (e x)=f x) : ∀ x, f x=f o := by
  intro x
  obtain ⟨n,rfl⟩ := hc x
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h, ih]

def advance {A : Type*} (o : X) (e : Equiv.Perm X) (s : X → A × A) : X → A × A :=
  fun x => if x=o then ((s (e x)).2,(s (e⁻¹ x)).1)
    else ((s (e⁻¹ x)).1,(s (e x)).2)

/-- This generic statement concerns register contents, not a chosen reference value. -/
theorem streams_fixed_iff {A : Type*} (o : X) (e : Equiv.Perm X) (hc : Connected o e)
    (s : X → A × A) : advance o e s=s ↔ ∃ r, s=fun _ => (r,r) := by
  constructor
  · intro hs
    have hr : ∀ x, (s (e x)).2=(s x).2 := by
      apply invariant_of_except o e (fun x => (s x).2)
      intro x hx
      have h := congrArg (fun p : A × A => p.2) (congrFun hs x)
      simpa [advance,hx] using h
    have hlInv : ∀ x, (s (e⁻¹ x)).1=(s x).1 := by
      apply invariant_of_except o e⁻¹ (fun x => (s x).1)
      intro x hx
      have h := congrArg (fun p : A × A => p.1) (congrFun hs x)
      simpa [advance,hx] using h
    have hl : ∀ x, (s (e x)).1=(s x).1 := by
      intro x
      simpa using (hlInv (e x)).symm
    have hR := orbit_constant o e hc (fun x => (s x).2) hr
    have hL := orbit_constant o e hc (fun x => (s x).1) hl
    have h0 : (s o).1=(s o).2 := by
      have h := congrArg (fun p : A × A => p.1) (congrFun hs o)
      have hh : (s (e o)).2=(s o).1 := by simpa [advance] using h
      exact hh.symm.trans (hr o)
    refine ⟨(s o).2, ?_⟩
    funext x
    exact Prod.ext ((hL x).trans h0) (hR x)
  · rintro ⟨r,rfl⟩
    funext x
    simp [advance]

def readPair {A : Type*} (s : Config X A) (i : Fin 2) : X → A × A :=
  fun x => (s (x,ActualRootRepair.label (.inl i)), s (x,ActualRootRepair.label (.inr i)))

omit [Fintype X] in
lemma readPair_step {A : Type*} (o : X) (e : Equiv.Perm X) (s : Config X A) (i : Fin 2) :
    readPair (tick o e s) i = advance o e (readPair s i) := by
  funext x
  apply Prod.ext <;> by_cases hx:x=o <;>
    simp [readPair, tick, lookup_label, portStep, couple, stream, advance, hx]

/-- Active references are shared across both streams. Unused fields remain free. -/
theorem stationary_iff {A : Type*} (o : X) (e : Equiv.Perm X) (hc : Connected o e)
    (s : Config X A) : tick o e s=s ↔ ∃ r : Fin 2 → A, ∀ x i,
      s (x,ActualRootRepair.label (.inl i))=r i ∧
      s (x,ActualRootRepair.label (.inr i))=r i := by
  constructor
  · intro hs
    refine ⟨fun i => s (o,ActualRootRepair.label (.inr i)), ?_⟩
    intro x i
    have hi : advance o e (readPair s i)=readPair s i := by rw [← readPair_step,hs]
    obtain ⟨r,hr⟩ := (streams_fixed_iff o e hc (readPair s i)).mp hi
    have hx := congrFun hr x
    have ho := congrFun hr o
    exact ⟨(congrArg Prod.fst hx).trans (congrArg Prod.snd ho).symm,
      (congrArg Prod.snd hx).trans (congrArg Prod.snd ho).symm⟩
  · rintro ⟨r,hr⟩
    funext p
    rcases p with ⟨x,c⟩
    change s (lookup o e (x,c))=s (x,c)
    by_cases hmem:c ∈ Set.range ActualRootRepair.label
    · obtain ⟨j,rfl⟩ := hmem
      rw [lookup_label]
      have hL : ∀ y i, s (y,ActualRootRepair.label (.inl i))=r i := fun y i => (hr y i).1
      have hR : ∀ y i, s (y,ActualRootRepair.label (.inr i))=r i := fun y i => (hr y i).2
      rcases j with i | i <;> by_cases hx:x=o <;>
        simp [portStep,couple,stream,hx,hL,hR]
    · rw [lookup_unused o e x c hmem]

/-- Every nonempty finite ring satisfies the connectivity hypothesis. -/
theorem ring_connected (R : ℕ) : Connected (0 : Fin (R+1)) (finRotate (R+1)) := by
  intro x
  refine ⟨x.val, ?_⟩
  exact WalkReferenceCycle.rotate_zero R x.val x.isLt

/-- The matching coherent background belongs to the already proved first-wall
zero kernel. This does not identify it with the full physical vacuum. -/
theorem background_zero_mode (r : Fin 2 → ℂ) :
    ConcreteFermion.hamiltonian 0 0 *ᵥ
      Sum.elim (WalkReferenceCoupling.pack (Sum.elim r r)) (fun _ => 0) = 0 := by
  rw [ConcreteFermion.kernel_coordinates]
  simp [WalkReferenceCoupling.pack,WalkReferenceCoupling.raw,WalkReferenceCoupling.backward,
    WalkRecordTransport.encode]

omit [Fintype X] in
/-- A concrete reversible finite history need not be stationary. -/
theorem single_carrier_not_fixed (o : X) (e : Equiv.Perm X) :
    tick o e (oneHot (o,ActualRootRepair.label (.inl 0))) ≠
      oneHot (o,ActualRootRepair.label (.inl 0)) := by
  intro h
  rw [oneHot_step] at h
  have hp := oneHot_injective h
  have hf : lookup o e (o,ActualRootRepair.label (.inl 0)) =
      (o,ActualRootRepair.label (.inl 0)) := by
    have hh := congrArg (lookup o e) hp
    simpa using hh.symm
  have hi := internal_root o e o (ActualRootRepair.label (.inl 0))
  rw [hf] at hi
  have hm := ActualRootRepair.label_moves (Sum.inl (0 : Fin 2))
  exact hm (by simpa using hi.symm)

def referenceField (r : Fin 2 → ℂ) : X × ActualRootRepair.C → ℂ :=
  RootCarrierWalk.field (fun _ => r) (fun _ => r)

theorem referenceField_fixed (o : X) (e : Equiv.Perm X) (r : Fin 2 → ℂ) :
    RootCarrierWalk.update o e *ᵥ referenceField r = referenceField r := by
  rw [referenceField,RootCarrierWalk.field_step]
  congr 1 <;> funext x <;> split_ifs <;> rfl

/-- No new independent source is asserted: this describes a perturbation of
an already stationary background and preserves the complete discrepancy. -/
theorem discrepancy_evolution (o : X) (e : Equiv.Perm X) (r : Fin 2 → ℂ)
    (d : X × ActualRootRepair.C → ℂ) :
    RootCarrierWalk.update o e *ᵥ (referenceField r+d) - referenceField r =
      RootCarrierWalk.update o e *ᵥ d := by
  rw [Matrix.mulVec_add,referenceField_fixed]
  abel

theorem discrepancy_population (o : X) (e : Equiv.Perm X) (r : Fin 2 → ℂ)
    (d : X × ActualRootRepair.C → ℂ) :
    CommonResponse.nsq (RootCarrierWalk.update o e *ᵥ (referenceField r+d)-referenceField r) =
      CommonResponse.nsq d := by
  rw [discrepancy_evolution]
  exact congrArg Complex.re (CommonResponse.unitary_nsq _ (RootCarrierWalk.update_unitary o e) d)

section Economy
variable {A : Type*} [DecidableEq A]

def changed (o : X) (e : Equiv.Perm X) (s : Config X A) : Finset (X × ActualRootRepair.C) :=
  Finset.univ.filter (fun p => tick o e s p ≠ s p)

def price (o : X) (e : Equiv.Perm X) (toll : ℝ) (s : Config X A) : ℝ :=
  toll * (changed o e s).card

lemma changed_zero_iff (o : X) (e : Equiv.Perm X) (s : Config X A) :
    (changed o e s).card=0 ↔ tick o e s=s := by
  constructor
  · intro h
    have he := Finset.card_eq_zero.mp h
    funext p
    have hn : p ∉ changed o e s := by rw [he]; simp
    simpa [changed] using hn
  · intro h
    simp [changed,h]

theorem price_zero_iff (o : X) (e : Equiv.Perm X) (toll : ℝ) (ht : 0<toll) (s : Config X A) :
    price o e toll s=0 ↔ tick o e s=s := by
  simp only [price,mul_eq_zero,ne_of_gt ht,false_or,Nat.cast_eq_zero]
  exact changed_zero_iff o e s

/-- Economy selects stationary fields under this explicit positive excess-price rule.
It does not select this rule from persistence or fix the reference value. -/
theorem minimum_iff_fixed (o : X) (e : Equiv.Perm X) (toll : ℝ) (ht : 0<toll)
    (a : A) (s : Config X A) :
    (∀ t : Config X A, price o e toll s ≤ price o e toll t) ↔ tick o e s=s := by
  have hn (t : Config X A) : 0 ≤ price o e toll t := mul_nonneg ht.le (Nat.cast_nonneg _)
  have hc : tick o e (fun _ => a) = (fun _ => a) := by funext p; rfl
  have hz := (price_zero_iff o e toll ht (fun _ => a)).mpr hc
  constructor
  · intro h
    apply (price_zero_iff o e toll ht s).mp
    exact le_antisymm (by simpa only [hz] using h (fun _ => a)) (hn s)
  · intro h t
    rw [(price_zero_iff o e toll ht s).mpr h]
    exact hn t

/-- Selection must respect the admissible/conserved family. A zero-excess
stationary witness within that family is required; it cannot be borrowed from
an inaccessible occupation sector. The common clock baseline remains counted. -/
theorem minimum_in_family_iff (o : X) (e : Equiv.Perm X) (toll baseline : ℝ) (ht : 0<toll)
    (F : Set (Config X A)) (w : Config X A) (hw : w ∈ F) (hfixed : tick o e w=w)
    (s : Config X A) :
    (s ∈ F ∧ ∀ t ∈ F, baseline+price o e toll s ≤ baseline+price o e toll t) ↔
      s ∈ F ∧ tick o e s=s := by
  have hn (t : Config X A) : 0 ≤ price o e toll t := mul_nonneg ht.le (Nat.cast_nonneg _)
  have hz := (price_zero_iff o e toll ht w).mpr hfixed
  constructor
  · rintro ⟨hs,h⟩
    refine ⟨hs,(price_zero_iff o e toll ht s).mp ?_⟩
    have hh := h w hw
    rw [hz] at hh
    linarith [hn s]
  · rintro ⟨hs,h⟩
    refine ⟨hs,?_⟩
    intro t _
    rw [(price_zero_iff o e toll ht s).mpr h]
    linarith [hn t]

end Economy
end PMAction.NativeReferenceBackground
