import PMAction.LinkConsistency
import PMAction.CommonResponse
import PMAction.GaugeRecordLinks

/-!
# Microscopic gauge transport: record update → links → curvature → gauge action

The update is primary. A *hop update* is a supplied linear update of continuum-indexed
packet fields whose output at `y` reads only the packet at `y + h v`. This is a
single-source-hop contract, stronger than general finite-neighbour causality. No
link field is supplied. A finite E8 payload/record implementation is not selected
by this model. The connection theorem retains the inherited global differentiability
and derivative-at-base-point bound, plus cubic consistency across spacings.

The uniform basis sampler and event-price/readout convention are supplied. Their
probability/cost interpretation requires N > 0 and nonnegative physical price and
refresh parameters; the algebraic identities below also allow degenerate/sign-free
parameters. No physical group, representation, primitive tariff or budget is selected.

* `extract`, `extract_spec`, `extract_unique`: every hop update is transport by a unique
  link field, read off from its response to unit packets; `update_is_record_transport`
  identifies it with `GaugeRecordLinks.transport`.
* `unitary_of_norm`, `extract_unitary`: local norm conservation (the conservation premise)
  makes every extracted link unitary.
* `framed_extract`, `framed_is_transformed`, `framed_conserving`: changing local frames
  transforms the links by the existing `GaugeRecordLinks.transformed` law;
  `holonomy_framed`, `framed_density`: holonomies conjugate at the base point and the D₄
  action density is invariant for arbitrary (not necessarily smooth) unitary frames.
* `update_to_action`: if the extracted links are cubically consistent with a `C^{1,1}`
  `u(N)` connection (explicit premise), the D₄ density of the update's own links converges
  to the Yang–Mills density; `midpoint_chain` shows the premises are satisfiable.
* `avg_flag`, `eventDensity`, `update_event_limit`, `framed_event_density`: pricing the update's
  holonomies by the common readout event (uniform carrier sampler) gives the D₄ density with
  `β = toll·m·W/(2N)` and its Yang–Mills limit, frame invariantly.
* What the update and its cost force: `cost_bounds_holonomy` (bounded density gives
  `Σ|(P−1)ᵢⱼ|² ≤ 24 D h⁴/β` on every triangle).
* What they do not force: `ofLinks_conserving` (every unitary link field is realized by a
  conserving single-hop update), `refinement_not_determined` (exact midpoint consistency at
  every single spacing, but with spacing-dependent connection, gives no limit), and
  `LinkConsistency.flip_*` (unitarity gives no consistency).
-/

noncomputable section
namespace PMAction.GaugeTransport
open Matrix VaryingFields LinkConsistency CommonResponse
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- Packet fields on the continuum point set. -/
abbrev Field (N : ℕ) := V → Fin N → ℂ

/-- One record-transport hop for direction `v` at spacing `h`: a linear update of packet
fields whose output at `y` reads only the packet arriving from `y + h v`. -/
structure HopUpdate (N : ℕ) (v : V) (h : ℝ) where
  T : Field N →ₗ[ℂ] Field N
  hop : ∀ ψ φ : Field N, ∀ y, ψ (y + h • v) = φ (y + h • v) → T ψ y = T φ y

/-- A packet `e_j` placed at the single point `z`. -/
def probe (z : V) (j : Fin N) : Field N := fun w => if w = z then Pi.single j 1 else 0

variable {v : V} {h : ℝ}

/-- The link actually used by the update at `y`: its response to unit packets. -/
def extract (S : HopUpdate N v h) (y : V) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => S.T (probe (y + h • v) j) y i

/-- **Link extraction.** Every hop update is transport by its extracted links. -/
theorem extract_spec (S : HopUpdate N v h) (ψ : Field N) (y : V) :
    S.T ψ y = extract S y *ᵥ ψ (y + h • v) := by
  set c := ψ (y + h • v)
  set φ : Field N := ∑ j, c j • probe (y + h • v) j
  have hφ : φ (y + h • v) = c := by
    funext i
    simp [φ, probe, Finset.sum_apply, Pi.single_apply]
  rw [S.hop ψ φ y hφ.symm, map_sum]
  funext i
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, extract]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Uniqueness.** Links that realize the update are the extracted ones. -/
theorem extract_unique (S : HopUpdate N v h) (M : V → Matrix (Fin N) (Fin N) ℂ)
    (hM : ∀ ψ y, S.T ψ y = M y *ᵥ ψ (y + h • v)) (y : V) : M y = extract S y := by
  ext i j
  have := congrFun (hM (probe (y + h • v) j) y) i
  simp only [probe] at this
  rw [extract, this]
  simp [mulVec, dotProduct, Pi.single_apply]

/-! ## Local conservation gives unitary links -/

/-- Polarization: a matrix preserving every packet norm is unitary. -/
theorem unitary_of_norm (M : Matrix (Fin N) (Fin N) ℂ) (hM : ∀ c, nsq (M *ᵥ c) = nsq c) :
    M ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  set Q := Mᴴ * M - 1
  have hQh : Qᴴ = Q := by simp [Q, conjTranspose_sub, conjTranspose_mul]
  have hq : ∀ c : Fin N → ℂ, (star c ⬝ᵥ (Q *ᵥ c)).re = 0 := by
    intro c
    have h1 : nsq (M *ᵥ c) = (star c ⬝ᵥ ((Mᴴ * M) *ᵥ c)).re := by
      rw [nsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    have := hM c
    rw [h1, nsq] at this
    simp only [Q, sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re]
    linarith
  have qe : ∀ (i j : Fin N) (z : ℂ), (star (Pi.single i 1 + z • Pi.single j 1 : Fin N → ℂ) ⬝ᵥ
      (Q *ᵥ (Pi.single i 1 + z • Pi.single j 1))) =
      Q i i + z * Q i j + star z * Q j i + star z * z * Q j j := by
    intro i j z
    have sI : ∀ (p : Prop) [Decidable p] (a b : ℂ),
        star (if p then a else b) = if p then star a else star b :=
      fun p _ a b => by split_ifs <;> rfl
    simp only [dotProduct, mulVec, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add,
      Pi.single_apply, smul_eq_mul, add_mul, mul_add, Finset.sum_add_distrib, sI, star_one,
      star_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have hentry : ∀ i j, Q i j = 0 := by
    intro i j
    have hii : ∀ k, (Q k k).re = 0 := fun k => by
      have := hq (Pi.single k 1 + (0 : ℂ) • Pi.single k 1)
      rw [qe k k 0] at this
      simpa using this
    have hherm : Q j i = star (Q i j) := by
      have := congrFun (congrFun hQh j) i
      simpa [conjTranspose_apply] using this.symm
    have hdiag : ∀ k, Q k k = 0 := fun k => by
      have hk := congrFun (congrFun hQh k) k
      simp only [conjTranspose_apply] at hk
      apply Complex.ext
      · exact hii k
      · have := congrArg Complex.im hk
        simp at this ⊢; linarith
    have r1 := hq (Pi.single i 1 + (1 : ℂ) • Pi.single j 1)
    have r2 := hq (Pi.single i 1 + Complex.I • Pi.single j 1)
    rw [qe, hherm, hdiag i, hdiag j] at r1 r2
    simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.zero_re,
      Complex.zero_im, Complex.mul_im, map_one, Complex.conj_I, Complex.neg_re,
      Complex.neg_im] at r1 r2
    norm_num at r1 r2
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp only [Complex.zero_im]; linarith
  have hQ : Q = 0 := by ext i j; exact hentry i j
  have h1 : Mᴴ * M = 1 := sub_eq_zero.mp hQ
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

/-- Local norm conservation of the transported packet. -/
def Conserving (S : HopUpdate N v h) : Prop :=
  ∀ ψ : Field N, ∀ y, nsq (S.T ψ y) = nsq (ψ (y + h • v))

/-- **Unitary links.** A conserving hop update has unitary extracted links. -/
theorem extract_unitary (S : HopUpdate N v h) (hc : Conserving S) (y : V) :
    extract S y ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  apply unitary_of_norm
  intro c
  have := hc (fun _ => c) y
  rwa [extract_spec] at this

/-! ## Every unitary link field is realized: persistence constraints leave the law free -/

/-- The hop update transporting by a prescribed link field. -/
def ofLinks (v : V) (h : ℝ) (M : V → Matrix (Fin N) (Fin N) ℂ) : HopUpdate N v h where
  T := { toFun := fun ψ y => M y *ᵥ ψ (y + h • v)
         map_add' := fun ψ φ => by funext y; simp [mulVec_add]
         map_smul' := fun z ψ => by funext y; simp [mulVec_smul] }
  hop := fun ψ φ y hy => by simp [hy]

theorem ofLinks_extract (M : V → Matrix (Fin N) (Fin N) ℂ) (y : V) :
    extract (ofLinks v h M) y = M y :=
  (extract_unique _ M (fun _ _ => rfl) y).symm

/-- **Freedom.** Every unitary link field is the link field of a linear, hop-local,
norm-conserving update. Linearity, locality, reversibility and conservation therefore
do not select the link law. -/
theorem ofLinks_conserving (M : V → Matrix (Fin N) (Fin N) ℂ)
    (hM : ∀ y, M y ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) : Conserving (ofLinks v h M) := by
  intro ψ y
  change nsq (M y *ᵥ ψ (y + h • v)) = _
  have h1 : (M y)ᴴ * M y = 1 := (hM y).1
  rw [nsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1, one_mulVec, nsq]

/-! ## Local frames -/

/-- A change of local frames applied to a hop update. -/
def framed (g : V → Matrix (Fin N) (Fin N) ℂ) (S : HopUpdate N v h) : HopUpdate N v h where
  T := { toFun := fun ψ y => g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ ψ z) y
         map_add' := fun ψ φ => by
           funext y
           have : (fun z => (g z)ᴴ *ᵥ (ψ + φ) z) =
               (fun z => (g z)ᴴ *ᵥ ψ z) + (fun z => (g z)ᴴ *ᵥ φ z) := by
             funext z; simp [mulVec_add]
           change g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ (ψ + φ) z) y =
             g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ ψ z) y + g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ φ z) y
           rw [this, map_add, Pi.add_apply, mulVec_add]
         map_smul' := fun c ψ => by
           funext y
           have : (fun z => (g z)ᴴ *ᵥ (c • ψ) z) = c • (fun z => (g z)ᴴ *ᵥ ψ z) := by
             funext z; simp [mulVec_smul]
           change g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ (c • ψ) z) y =
             c • (g y *ᵥ S.T (fun z => (g z)ᴴ *ᵥ ψ z) y)
           rw [this, map_smul, Pi.smul_apply, mulVec_smul] }
  hop := fun ψ φ y hy => by
    change g y *ᵥ S.T _ y = g y *ᵥ S.T _ y
    rw [S.hop _ (fun z => (g z)ᴴ *ᵥ φ z) y (by simp [hy])]

/-- **Frame covariance.** The framed update's links are `g(y) U(y) g(y + h v)ᴴ`, the link law
of `GaugeRecordLinks.transformed`. -/
theorem framed_extract (g : V → Matrix (Fin N) (Fin N) ℂ) (S : HopUpdate N v h) (y : V) :
    extract (framed g S) y = g y * extract S y * (g (y + h • v))ᴴ := by
  symm
  apply extract_unique (framed g S) (fun y => g y * extract S y * (g (y + h • v))ᴴ)
  intro ψ y
  change g y *ᵥ S.T _ y = _
  rw [extract_spec]
  simp [mulVec_mulVec, Matrix.mul_assoc]

theorem framed_conserving (g : V → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ y, g y ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (S : HopUpdate N v h)
    (hc : Conserving S) : Conserving (framed g S) := by
  intro ψ y
  have hu : ∀ (U : Matrix (Fin N) (Fin N) ℂ), U ∈ unitary _ → ∀ c, nsq (U *ᵥ c) = nsq c := by
    intro U hU c
    have h1 : Uᴴ * U = 1 := hU.1
    rw [nsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1, one_mulVec, nsq]
  change nsq (g y *ᵥ S.T _ y) = _
  have hs : (g (y + h • v))ᴴ ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := Unitary.star_mem (hg _)
  rw [hu _ (hg y), hc, hu _ hs]

/-! ## The edge family of an explicit update and the controlled gauge action -/

/-- An update family: one hop update per direction and spacing. -/
abbrev Updates (N : ℕ) := (v : V) → (h : ℝ) → HopUpdate N v h

/-- The directed-edge links actually used by the updates: `U y v h` transports from
`y + h v` to `y`. -/
def linksOf (S : Updates N) : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ :=
  fun y v h => extract (S v h) y

/-- **The chain.** Conserving hop updates have unitary links; if those links are cubically
consistent with a `C^{1,1}` `u(N)` connection (an explicit premise), the D₄ action density
of the update's own links converges to the Yang–Mills density. -/
theorem update_to_action {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (S : Updates N) (hS : ∀ v h, Conserving (S v h))
    (hK : 0 ≤ K) (hc : CubicConsistent (linksOf S) A x K) (β : ℝ) :
    Filter.Tendsto (fun h => linkDensity (linksOf S) x β h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) :=
  d4_link_tendsto hA hL0 hL hskew (linksOf S) (fun y v h => extract_unitary _ (hS v h) y) hK hc β

/-- The framed update family. -/
def framedUpdates (g : V → Matrix (Fin N) (Fin N) ℂ) (S : Updates N) : Updates N :=
  fun v h => framed g (S v h)

lemma holonomy_framed (g : V → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ y, g y ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (S : Updates N) (x a b : V) (h : ℝ) :
    holonomy (linksOf (framedUpdates g S)) x a b h =
      g x * holonomy (linksOf S) x a b h * (g x)ᴴ := by
  have hp : x + h • a + h • (b - a) = x + h • b := by module
  have ha : (g (x + h • a))ᴴ * g (x + h • a) = 1 := (hg _).1
  have hb : (g (x + h • b))ᴴ * g (x + h • b) = 1 := (hg _).1
  simp only [holonomy, linksOf, framedUpdates, framed_extract, conjTranspose_mul,
    conjTranspose_conjTranspose, hp]
  calc _ = g x * extract (S a h) x * ((g (x + h • a))ᴴ * g (x + h • a)) *
        extract (S (b - a) h) (x + h • a) * ((g (x + h • b))ᴴ * g (x + h • b)) *
        (extract (S b h) x)ᴴ * (g x)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha, hb]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- **Frame invariance of the action.** Arbitrary unitary local frames, smooth or not,
leave the update's D₄ density unchanged. -/
theorem framed_density (g : V → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ y, g y ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (S : Updates N) (x : V) (β h : ℝ) :
    linkDensity (linksOf (framedUpdates g S)) x β h = linkDensity (linksOf S) x β h := by
  unfold linkDensity
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [holonomy_framed g hg]
  have hgg : g x * (g x)ᴴ = 1 := (hg x).2
  have e : (1 : Matrix (Fin N) (Fin N) ℂ) - g x * holonomy (linksOf S) x (rv p.1) (rv p.2) h * (g x)ᴴ =
      g x * ((1 - holonomy (linksOf S) x (rv p.1) (rv p.2) h) * (g x)ᴴ) := by
    symm
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hgg, Matrix.mul_assoc]
  have hgg' : (g x)ᴴ * g x = 1 := (hg x).1
  rw [e, trace_mul_comm, Matrix.mul_assoc, hgg', Matrix.mul_one]

/-! ## What the cost does force: small triangle holonomy -/

lemma wilson_nonneg (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    0 ≤ (trace (1 - P)).re := by
  have := wilson_sum P hP.1
  have h0 : 0 ≤ ∑ i, ∑ j, ‖(P - 1) i j‖ ^ 2 := by positivity
  linarith

lemma holonomy_unitary (S : Updates N) (hS : ∀ v h, Conserving (S v h)) (x a b : V) (h : ℝ) :
    holonomy (linksOf S) x a b h ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  unfold holonomy linksOf
  exact (unitary _).mul_mem ((unitary _).mul_mem (extract_unitary _ (hS _ _) _)
    (extract_unitary _ (hS _ _) _)) (Unitary.star_mem (extract_unitary _ (hS _ _) _))

/-- **Bounded action forces `O(h²)` holonomy on every triangle** (gauge invariantly). If the
update's D₄ density is at most `D` with `β > 0`, each triangle satisfies
`Σ |(P − 1)ᵢⱼ|² ≤ 24 D h⁴ / β`. -/
theorem cost_bounds_holonomy (S : Updates N) (hS : ∀ v h, Conserving (S v h)) (x : V)
    {β D h : ℝ} (hβ : 0 < β) (hh : 0 < h) (hD : linkDensity (linksOf S) x β h ≤ D)
    (p : (Fin 4 → Fin 3) × (Fin 4 → Fin 3)) (hp : p ∈ D4Gauge.tri) :
    ∑ i, ∑ j, ‖(holonomy (linksOf S) x (rv p.1) (rv p.2) h - 1) i j‖ ^ 2 ≤ 24 * D * h ^ 4 / β := by
  set w : (Fin 4 → Fin 3) × (Fin 4 → Fin 3) → ℝ :=
    fun q => (trace (1 - holonomy (linksOf S) x (rv q.1) (rv q.2) h)).re
  have hw : ∀ q, 0 ≤ w q := fun q => wilson_nonneg _ (holonomy_unitary S hS _ _ _ _)
  have h4 : 0 < h ^ 4 := by positivity
  have hsum : w p ≤ ∑ q ∈ D4Gauge.tri, w q :=
    Finset.single_le_sum (f := w) (fun q _ => hw q) hp
  have hden : linkDensity (linksOf S) x β h = (β / 12) * (∑ q ∈ D4Gauge.tri, w q) / h ^ 4 := by
    simp only [linkDensity, w, ← Finset.sum_div]; ring
  have htot : ∑ q ∈ D4Gauge.tri, w q ≤ 12 * D * h ^ 4 / β := by
    rw [hden] at hD
    rw [le_div_iff₀ hβ]
    have := (div_le_iff₀ h4).mp hD
    nlinarith
  have hws := wilson_sum _ (holonomy_unitary S hS x (rv p.1) (rv p.2) h).1
  have : w p ≤ 12 * D * h ^ 4 / β := hsum.trans htot
  calc _ = 2 * w p := hws
    _ ≤ 2 * (12 * D * h ^ 4 / β) := by linarith
    _ = 24 * D * h ^ 4 / β := by ring

/-! ## Refinement is not fixed by the update at each spacing -/

/-- Midpoint-link updates of a connection. -/
def midpointUpdates (A : ℝ → V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) : Updates N :=
  fun v h => ofLinks v h (fun y => link (A h) y v h)

lemma midpoint_holonomy (A : ℝ → V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (hskew : ∀ h y v, star (A h y v) = -A h y v) (x a b : V) (h : ℝ) :
    holonomy (linksOf (midpointUpdates A)) x a b h = triangle (A h) x a b h := by
  simp only [holonomy, linksOf, midpointUpdates, ofLinks_extract, triangle,
    reverse_eq (hskew h)]

lemma midpoint_density (A : ℝ → V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (hskew : ∀ h y v, star (A h y v) = -A h y v) (x : V) (β h : ℝ) :
    linkDensity (linksOf (midpointUpdates A)) x β h = d4Density (A h) x β h := by
  simp only [linkDensity, d4Density, midpoint_holonomy A hskew]

theorem midpoint_conserving (A : ℝ → V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)
    (hskew : ∀ h y v, star (A h y v) = -A h y v) (v : V) (h : ℝ) :
    Conserving (midpointUpdates A v h) :=
  ofLinks_conserving _ fun y => link_unitary (hskew h) y v h

lemma zero_triangle_density (x : V) (β h : ℝ) :
    d4Density (0 : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) x β h = 0 := by
  simp [d4Density, triangle, link]

/-- The connection switched on at even `⌊1/h⌋` and off at odd. -/
def switched (A0 : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ) (h : ℝ) :
    V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  if Even ⌊1 / h⌋₊ then A0 else 0

/-- **Refinement freedom.** At every spacing the switched update is linear, hop-local,
conserving, unitary and exactly midpoint-consistent with a smooth `u(N)` connection
(`A0` or `0`). Yet if `A0`'s Yang–Mills density `L0` is nonzero, the action density has no
limit. Consistency across spacings is therefore an additional premise. -/
theorem refinement_not_determined {A0 : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A0 (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A0 y v) = -A0 y v) (β : ℝ)
    (hne : (β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A0 DA x μ ν i j‖ ^ 2 ≠ 0) :
    ¬ ∃ Λ, Filter.Tendsto (fun h => linkDensity (linksOf (midpointUpdates (switched A0))) x β h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Λ) := by
  rintro ⟨Λ, hΛ⟩
  have hsk : ∀ h y v, star (switched A0 h y v) = -switched A0 h y v := by
    intro h y v; unfold switched; split_ifs
    · exact hskew y v
    · simp
  have hlim := d4_yang_mills_tendsto hA hL0 hL hskew β
  -- spacing sequences with even and odd `⌊1/h⌋`
  set u : ℕ → ℝ := fun k => 1 / ((2 * k + 2 : ℕ) : ℝ)
  set w : ℕ → ℝ := fun k => 1 / ((2 * k + 1 : ℕ) : ℝ)
  have hseq : ∀ m : ℕ → ℕ, (∀ k, k + 1 ≤ m k) →
      Filter.Tendsto (fun k => 1 / ((m k : ℕ) : ℝ)) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    intro m hm
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall fun k => ?_⟩
    · have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) h0
      have : ((k : ℝ) + 1) ≤ (m k : ℝ) := by exact_mod_cast hm k
      exact one_div_le_one_div_of_le (by positivity) this
    · have : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast (Nat.succ_pos k).trans_le (hm k)
      exact one_div_pos.mpr this
  have hu := hseq (fun k => 2 * k + 2) (fun k => by omega)
  have hw := hseq (fun k => 2 * k + 1) (fun k => by omega)
  have hfloor : ∀ m : ℕ, ⌊1 / (1 / ((m : ℕ) : ℝ))⌋₊ = m := fun m => by
    rw [one_div_one_div, Nat.floor_natCast]
  have hdu : ∀ k, linkDensity (linksOf (midpointUpdates (switched A0))) x β (u k) =
      d4Density A0 x β (u k) := by
    intro k
    rw [midpoint_density _ hsk]
    simp only [switched, u, hfloor, show Even (2 * k + 2) from ⟨k + 1, by ring⟩, ite_true]
  have hdw : ∀ k, linkDensity (linksOf (midpointUpdates (switched A0))) x β (w k) = 0 := by
    intro k
    rw [midpoint_density _ hsk]
    have hodd : ¬ Even (2 * k + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩
    simp only [switched, w, hfloor, hodd, ite_false]
    exact zero_triangle_density x β _
  have t1 := (hΛ.comp hu)
  have t2 := (hlim.comp hu)
  have e1 : (fun h => linkDensity (linksOf (midpointUpdates (switched A0))) x β h) ∘
      (fun k => 1 / ((2 * k + 2 : ℕ) : ℝ)) = (fun h => d4Density A0 x β h) ∘
      (fun k => 1 / ((2 * k + 2 : ℕ) : ℝ)) := by
    funext k; exact hdu k
  rw [e1] at t1
  have hΛ0 := tendsto_nhds_unique t1 t2
  have t3 := (hΛ.comp hw)
  have e2 : (fun h => linkDensity (linksOf (midpointUpdates (switched A0))) x β h) ∘
      (fun k => 1 / ((2 * k + 1 : ℕ) : ℝ)) = fun _ => 0 := by
    funext k; exact hdw k
  rw [e2] at t3
  have hz := tendsto_nhds_unique t3 tendsto_const_nhds
  exact hne (hΛ0 ▸ hz.symm ▸ rfl)

/-! ## Identification with the existing record-transport link law -/

/-- The update of a link field is `GaugeRecordLinks.transport` along the translation `y ↦ y + h v`. -/
theorem ofLinks_is_record_transport (M : V → Matrix (Fin N) (Fin N) ℂ) (ψ : Field N) :
    (ofLinks v h M).T ψ = GaugeRecordLinks.transport (Equiv.addRight (h • v)) M ψ := rfl

/-- Every hop update is record transport by its own extracted links. -/
theorem update_is_record_transport (S : HopUpdate N v h) (ψ : Field N) :
    S.T ψ = GaugeRecordLinks.transport (Equiv.addRight (h • v)) (extract S) ψ := by
  funext y; exact extract_spec S ψ y

/-- Frame change of an update is the existing `GaugeRecordLinks.transformed` link law. -/
theorem framed_is_transformed (g : V → Matrix (Fin N) (Fin N) ℂ) (S : HopUpdate N v h) :
    extract (framed g S) =
      GaugeRecordLinks.transformed (Equiv.addRight (h • v)) g g (extract S) := by
  funext y; exact framed_extract g S y

/-! ## The chain is not vacuous -/

/-- Midpoint updates of one fixed `C^{1,1}` `u(N)` connection satisfy every premise of
`update_to_action` with consistency constant `0`. -/
theorem midpoint_chain {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v) (β : ℝ) :
    Filter.Tendsto (fun h => linkDensity (linksOf (midpointUpdates (fun _ => A))) x β h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((β / 2) * ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) := by
  refine update_to_action hA hL0 hL hskew _ (fun v h => midpoint_conserving _ (fun _ => hskew) v h)
    le_rfl (fun y v h _ _ _ _ => ?_) β
  simp [linksOf, midpointUpdates, ofLinks_extract]

/-! ## Pricing the update's holonomies by the common readout event -/

/-- Uniformly sampled readout flag over the `N` basis carriers. -/
def avgFlag (P : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (∑ a : Fin N, stateFlag P (Pi.single a 1)) / N

theorem avg_flag (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    avgFlag P = (trace (1 - P)).re / (2 * N) := by
  unfold avgFlag
  simp_rw [basis_case P hP, InterferenceReadout.flag_formula P hP]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp [trace, Finset.sum_sub_distrib, Complex.re_sum]
  ring

/-- Event-priced D₄ density of an update family: `W` refreshes per triangle, each a sampled
readout flag repaired by `m` events at the common toll; per-volume weight `1/12`. -/
def eventDensity (S : Updates N) (x : V) (toll : ℝ) (m : ℕ) (W h : ℝ) : ℝ :=
  (1 / 12) * ∑ p ∈ D4Gauge.tri,
    W * responseCost toll m (avgFlag (holonomy (linksOf S) x (rv p.1) (rv p.2) h)) / h ^ 4

theorem event_density_eq (S : Updates N) (hS : ∀ v h, Conserving (S v h)) (x : V) (toll : ℝ)
    (m : ℕ) (W h : ℝ) :
    eventDensity S x toll m W h = linkDensity (linksOf S) x (toll * m * W / (2 * N)) h := by
  unfold eventDensity linkDensity
  simp only [avg_flag _ (holonomy_unitary S hS _ _ _ _), responseCost]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Record update → event-priced gauge action.** The common-readout price of the update's
own holonomies has the Yang–Mills limit with `β = toll·m·W/(2N)`. Paper III's
`PMNested.GaugeGroupFactor` turns this into the coupling/group-factor statements. -/
theorem update_event_limit {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L K : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    (hskew : ∀ y v, star (A y v) = -A y v)
    (S : Updates N) (hS : ∀ v h, Conserving (S v h))
    (hK : 0 ≤ K) (hc : CubicConsistent (linksOf S) A x K) (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => eventDensity S x toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * N) / 2) *
        ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A DA x μ ν i j‖ ^ 2)) := by
  have := update_to_action hA hL0 hL hskew S hS hK hc (toll * m * W / (2 * N))
  simpa only [event_density_eq S hS] using this

/-- Frame invariance of the event-priced action. -/
theorem framed_event_density (g : V → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ y, g y ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (S : Updates N)
    (hS : ∀ v h, Conserving (S v h)) (x : V) (toll : ℝ) (m : ℕ) (W h : ℝ) :
    eventDensity (framedUpdates g S) x toll m W h = eventDensity S x toll m W h := by
  have hF : ∀ v h, Conserving (framedUpdates g S v h) := fun v h => framed_conserving g hg _ (hS v h)
  rw [event_density_eq _ hF, event_density_eq S hS, framed_density g hg]

end PMAction.GaugeTransport
