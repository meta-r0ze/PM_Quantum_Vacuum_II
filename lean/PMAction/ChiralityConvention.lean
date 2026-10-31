import PMAction.WallChiralCurrent
import PMAction.WallExchange
import PMAction.NativeReferenceBackground

/-!
# "Left-handed" is a convention fixed by the charged current

`WallChiralCurrent` shows the charged projector `(1 − Γ)/2` selects one wall on the zero kernel,
and leaves calling it left-handed as an input. Here that label is a convention, not physics.

* `orientation_flips_gammaFive`: reversing the spatial orientation (`γʲ ↦ −γʲ`, `j = 1, 2, 3`)
  turns `γ⁵ = i γ⁰γ¹γ²γ³` into `−γ⁵`.
* `axis_swap_flips_gammaFive`: exchanging two spatial axes does the same.
* `exchange_flips_chirality`: the wall-parity exchange `P = [[0, β], [β, 0]]` conjugates the
  wall chirality to its negative. It therefore exchanges the two chiral projectors
  (`exchange_swaps_projectors`).
* `exchange_hamiltonian`: the same `P` maps the actual lattice Hamiltonian
  (`ConcreteFermion.hamiltonian`) to itself with `k ↦ −k`. It is the parity symmetry.

* `projector_kills_background`, `opposite_keeps_background`, `exchanged_background`: Paper II's
  stationary reference background lies on the first wall. The posited projector `(1 − Γ)/2`
  annihilates it and `(1 + Γ)/2` keeps it. After the wall-parity exchange, `(1 − Γ)/2` keeps the
  exchanged background. Weak repairs the reference (`FrameOwnership`, Contract C), so its current
  must act on the reference's wall. The weak representation is therefore attached to the wall
  carrying the reference, and "left" names that wall. In Paper II's displayed coordinates this
  means using `(1 + Γ)/2`, or equivalently the exchanged description.

* `displayed_placement_excluded`, `physicalBackground_kernel`, `weak_acts_on_reference`: **the
  decision.** Paper II's Dirac algebra fixes `γ⁵ = Γ` and the charged projector `(1 − Γ)/2`
  (`VATrace.L = 1 − Γ`, `WeakVertex`). With that projector, the first-wall placement of the
  reference is excluded: the weak current maps it to zero. The exchanged placement
  `physicalBackground` is still a stationary zero mode, because the exchange is a symmetry, and
  the weak current keeps it. So the physical reference is the second-wall (`−Γ`) zero mode, and
  the existing projector is correct as written.

So which wall is called left depends on the orientation convention. The parity-related
description is an equivalent theory with the labels swapped. The physical content is that the
charged current couples to exactly one wall, which `WallChiralCurrent.selected_iff` derives;
"left-handed" names that wall. Still inputs: attaching the weak representation, and extending the
identification away from the zero kernel.
-/

noncomputable section
namespace PMAction.ChiralityConvention
open Matrix ConcreteFermion WallChiralCurrent

/-- Dirac gammas in the reversed spatial orientation. -/
def reversedGamma : Fin 4 → Spin :=
  ![beta, -(beta * alpha 0), -(beta * alpha 1), -(beta * alpha 2)]

/-- Dirac gammas with spatial axes `0` and `1` exchanged. -/
def swappedGamma : Fin 4 → Spin := ![beta, beta * alpha 1, beta * alpha 0, beta * alpha 2]

def gammaFiveOf (G : Fin 4 → Spin) : Spin := Complex.I • (G 0 * G 1 * G 2 * G 3)

theorem orientation_flips_gammaFive : gammaFiveOf reversedGamma = -gamma := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gammaFiveOf, reversedGamma, beta, alpha, gamma, mul_apply, Fin.sum_univ_four]

theorem axis_swap_flips_gammaFive : gammaFiveOf swappedGamma = -gamma := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gammaFiveOf, swappedGamma, beta, alpha, gamma, mul_apply, Fin.sum_univ_four]

/-- The displayed orientation gives `+Γ`. -/
theorem displayed_gammaFive : gammaFiveOf diracGamma = gamma := gammaFive_eq

/-- Wall exchange with spinor parity on the eight wall components. -/
def exchange : Matrix Sites Sites ℂ := fromBlocks 0 beta beta 0

theorem exchange_sq : exchange * exchange = 1 := by
  rw [exchange, fromBlocks_multiply]
  simp [beta_square, ← fromBlocks_one]

theorem exchange_flips_chirality : exchange * chirality * exchange = -chirality := by
  rw [exchange, chirality, fromBlocks_multiply, fromBlocks_multiply]
  have h : beta * gamma * beta = -gamma := by
    rw [beta_gamma, neg_mul, mul_assoc, beta_square, mul_one]
  simp [h, fromBlocks_neg]

/-- **The exchange swaps the two chiral projectors.** -/
theorem exchange_swaps_projectors :
    exchange * projector * exchange = (1 / 2 : ℂ) • (1 + chirality) := by
  rw [projector, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one,
    exchange_flips_chirality, exchange_sq, sub_neg_eq_add]

set_option maxHeartbeats 4000000 in
/-- **The exchange is a symmetry of the actual lattice Hamiltonian**, with momentum reversed. -/
theorem exchange_hamiltonian (k : Fin 3 → ℝ) (δ : ℝ) :
    exchange * hamiltonian k δ * exchange = hamiltonian (-k) δ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [exchange, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum,
      DomainWallSpectrum.hop, DomainWallSpectrum.back, DomainWallSpectrum.plus,
      DomainWallSpectrum.minus, beta, gamma, alpha, mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_three, Fintype.sum_sum_type, Real.sin_neg, Matrix.vecMul, dotProduct,
      Matrix.sub_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring

/-! ## The charged current must act on the reference's wall -/

/-- Paper II's stationary reference background on the wall sites
(`NativeReferenceBackground.background_zero_mode`). -/
def background (r : Fin 2 → ℂ) : Sites → ℂ :=
  Sum.elim (WalkReferenceCoupling.pack (Sum.elim r r)) (fun _ => 0)

theorem background_kernel (r : Fin 2 → ℂ) : hamiltonian 0 0 *ᵥ background r = 0 :=
  NativeReferenceBackground.background_zero_mode r

/-- **The posited projector `(1 − Γ)/2` annihilates the reference background.** -/
theorem projector_kills_background (r : Fin 2 → ℂ) : projector *ᵥ background r = 0 := by
  rw [kernel_projector _ (background_kernel r)]
  funext c; rcases c with a | a <;> simp [secondWall, background]

/-- **`(1 + Γ)/2` keeps the reference background.** -/
theorem opposite_keeps_background (r : Fin 2 → ℂ) :
    ((1 / 2 : ℂ) • (1 + chirality)) *ᵥ background r = background r := by
  have h : ((1 / 2 : ℂ) • (1 + chirality)) = 1 - projector := by
    rw [projector]; ext i j; simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h, sub_mulVec, one_mulVec, projector_kills_background, sub_zero]

/-- **In the exchanged description the posited projector acts on the reference.** The wall-parity
exchange (a symmetry, `exchange_hamiltonian`) moves the background to the second wall, where
`(1 − Γ)/2` keeps it. -/
theorem exchanged_background (r : Fin 2 → ℂ) :
    projector *ᵥ (exchange *ᵥ background r) = exchange *ᵥ background r := by
  have hsw := exchange_swaps_projectors
  have e : projector = exchange * ((1 / 2 : ℂ) • (1 + chirality)) * exchange := by
    rw [← hsw, ← mul_assoc, ← mul_assoc, exchange_sq, one_mul, mul_assoc, exchange_sq, mul_one]
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (v := background r) (M := exchange) (N := exchange), exchange_sq,
    one_mulVec, opposite_keeps_background]

/-! ## The decision: place the reference where the weak current acts -/

lemma background_ne_zero (r : Fin 2 → ℂ) (hr : r ≠ 0) : background r ≠ 0 := by
  intro h
  have hp : WalkReferenceCoupling.pack (Sum.elim r r) = 0 := by
    funext a; have := congrFun h (.inl a); simpa [background] using this
  have hraw : WalkReferenceCoupling.raw (Sum.elim r r) = 0 := by
    have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; positivity
    have := hp
    rw [WalkReferenceCoupling.pack] at this
    exact (smul_eq_zero.mp this).resolve_left hc
  have h2 := WalkReferenceCoupling.recover_raw (Sum.elim r r)
  rw [hraw] at h2
  have h0 : WalkReferenceCoupling.recover 0 = 0 := by
    funext m; rcases m with i | i <;> fin_cases i <;> simp [WalkReferenceCoupling.recover]
  rw [h0] at h2
  apply hr
  funext i
  have := congrFun h2 (.inl i)
  simp at this
  simpa using this

/-- **The displayed placement is excluded.** For a nonzero reference, the charged projector
`(1 − Γ)/2` of Paper II's Dirac algebra (`γ⁵ = Γ`, `VATrace.L = 1 − Γ`) does not act on the
first-wall background: it maps it to zero. -/
theorem displayed_placement_excluded (r : Fin 2 → ℂ) (hr : r ≠ 0) :
    projector *ᵥ background r ≠ background r := by
  rw [projector_kills_background]; exact (background_ne_zero r hr).symm

/-- The physical reference: the stationary background in the wall-exchanged placement. -/
def physicalBackground (r : Fin 2 → ℂ) : Sites → ℂ := exchange *ᵥ background r

/-- It is still a zero mode, because the exchange is a symmetry of the Hamiltonian at `k = 0`. -/
theorem physicalBackground_kernel (r : Fin 2 → ℂ) :
    hamiltonian 0 0 *ᵥ physicalBackground r = 0 := by
  have h := exchange_hamiltonian 0 0
  rw [neg_zero] at h
  have hH : hamiltonian 0 0 = exchange * hamiltonian 0 0 * exchange := by
    rw [h]
  rw [physicalBackground, hH, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (v := background r) (M := exchange) (N := exchange), exchange_sq, one_mulVec,
    background_kernel, mulVec_zero]

/-- **The weak current acts on the physical reference.** -/
theorem weak_acts_on_reference (r : Fin 2 → ℂ) :
    projector *ᵥ physicalBackground r = physicalBackground r := exchanged_background r

theorem physicalBackground_ne_zero (r : Fin 2 → ℂ) (hr : r ≠ 0) : physicalBackground r ≠ 0 := by
  intro h
  apply background_ne_zero r hr
  have := congrArg (exchange *ᵥ ·) h
  simp only [physicalBackground, mulVec_mulVec, exchange_sq, one_mulVec, mulVec_zero] at this
  exact this

end PMAction.ChiralityConvention
