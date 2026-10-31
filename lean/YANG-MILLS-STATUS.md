# Yang–Mills: what PM proves, and the open quantum problem

## Proved: the classical continuum limit with canonical normalization

Audited 2026-10-31 against `PM-1-Arch/calculations/lean_review.tex`; the full catalog is
`LEAN-AUDIT-YANG-MILLS.md`. Standard axioms only.

- **Main theorem: `LatticeSiteAction.d4_yang_mills_action`.** Let `A` be a `u(N)`-valued
  connection on `ℝ⁴` whose derivative is Lipschitz on compact sets (every `C²` connection). Let
  the links be its parallel transports along the D₄ edges. Sum the Wilson density
  `(β/12) Σ_△ Re tr(1 − U_△)/h⁴` over the actual D₄ sites of any bounded measurable region `S`
  with null boundary, each weighted by the D₄ cell volume `2h⁴`. Then as `h = 1/n → 0` the sum
  converges to `∫_S (β/2) Σ_{μν} ‖F_{μν}‖²_F`, the classical Yang–Mills action.
  - The sites are proved to be exactly D₄ (`d4_sites`: integer vectors with even coordinate sum),
    with cell volume 2 (`d4Map_det`).
  - Unitarity of the transport is derived (`transport_unitary`), not assumed.
  - No cubic-consistency hypothesis, no global derivative bound, no free choice of partition.
- **Earlier forms, still valid.** `ClassicalYangMills.pm_lattice_yang_mills` (any links cubically
  consistent with `A`, Riemann sums over arbitrary tagged partitions of a box) and
  `ParallelTransport.pm_yang_mills_locally_lipschitz`. Their derivative hypotheses are now local
  (within distance two or three of the region); they previously required a global Lipschitz
  bound, which excluded every connection with growing derivative.
- **Normalization: `canonical_from_generators`.** For `F = −i g Σ_a F^a T^a` with Hermitian
  `tr T^a T^b = δ^{ab}/2`, the Frobenius identity `‖F‖²_F = (g²/2) Σ (F^a)²` is proved
  (`generator_norm`), so at `β = 1/g²` the limit is `(1/4) Σ_{μν a} (F^a_{μν})²`. This matches a
  convention; it does not determine `g`.
- **The coupling is an input.** `SummedReference.sum_canonical_iff` only rewrites "the
  coefficient is `1/4`" as `g² = 1/(κ·toll·m·W)`. It fixes `g` only if `κ`, `toll`, `m` and `W`
  are independently fixed, which they are not. Earlier wording that "event pricing fixes `β`" is
  withdrawn.
- **Supporting results:**
  - `link_yang_mills_uniform`: one error constant on any compact region.
  - `IntegratedScalarAction`: the same limit for the scalar action.
  - Perturbative inputs: the one-loop `b₀` from spin-½, spin-0 and spin-1 response
    (`RunningResponse`, `GaugeFluctuation`), the ghost determinant power (`FluctuationClosure`), the
    Landau degeneracy, and the pointwise lattice Hessian (`LatticeToContinuum`).

- **Transport existence and literal C²: now constructed.**
  `TransportExistence.exists_transport` solves the matrix ODE globally for every
  continuous skew coefficient and proves unitarity. `connection_reciprocal` derives
  the reverse-edge adjoint law. `ConnectionRegularity.c2_data` turns literal C²
  regularity into the existing compact-Lipschitz hypotheses; the combined theorem
  `exists_yang_mills_transport_c2` constructs a link family and proves its site-action
  limit without assuming a transport solution.
- **Operational update route:** `CompositionalTransport.update_to_yang_mills_c2`
  derives the ODE and the same limit for a supplied conserving single-hop update
  family. Exact composition under subdivision and a C² infinitesimal response are
  hypotheses; skewness and cubic consistency are conclusions. This is a sufficient
  operational criterion, not a proof that the native E8 update satisfies it.

**What this does not show.** The native E8 packet subsystem and its refinement law
are not identified. The connection, group, representation and `β` are not selected
by the postulates. Thus the classical result still does not show that PM produces
Yang–Mills. Transport existence and the literal C² interface are no longer missing.
The density is Euclidean, and the convergence result concerns smooth classical fields.

## The quantum problem, and what is missing

The Clay statement (Jaffe–Witten): for a compact simple gauge group `G`, construct a quantum
Yang–Mills theory on `ℝ⁴` satisfying the Wightman axioms (equivalently, Osterwalder–Schrader
axioms for its Euclidean Schwinger functions), and prove a mass gap `Δ > 0`.
The finite results below address only parts of this program. Items marked (M)
also lack the required Mathlib infrastructure.

1. **A lattice quantum measure.** A finite-volume, finite-spacing probability measure
   `Z⁻¹ exp(−S(U)) Π_edges dHaar(U)` on link configurations, with `S` PM's D₄ action. Now done for
   `U(1)` and `U(N)` (see below); `SU(N)` is not constructed. Also missing: why PM's real-time unitary update
   gives a Euclidean measure (a transfer-matrix or Wick-rotation identification). PM's survival
   weight `exp(−β·cost)` has the Gibbs form, but identifying it with this measure is not proved.
2. **Reflection positivity.** `ReciprocalReflection.reflection_positive` proves
   the normalized finite site-reflection form for reciprocal `U(N)` links on a
   reflection-symmetric integer-site region at unit spacing. It uses the same measure
   as the gauge-invariance theorem below. Link-reflection, a transfer matrix and
   nonnegative-Hamiltonian reconstruction remain open.
3. **Gauge invariance.** `GeometricGauge` constructs the local gauge action on
   geometric directed links and proves product Haar/Gibbs invariance.
   `ReciprocalReflection.gauge_preserving` proves invariance of the reciprocal-link
   measure. Arbitrary edge-identification quotients are not covered. A continuum
   observable algebra and its quantum moments remain open.

4. **Infinite volume.** Existence (and uniqueness or translation invariance) of the
   thermodynamic limit of correlation functions.
5. **Continuum limit with renormalization.** Send `h → 0` while running `β(h) → ∞` by asymptotic
   freedom (`b₀ > 0` is proved). Prove the Schwinger functions converge to a nontrivial limit.
   Here our classical theorem's hypothesis is exactly what fails: typical configurations of the
   quantum measure are rough, not `C^{1,1}`, so the classical limit says nothing about them.
   Balaban's renormalization-group program gives partial ultraviolet stability in finite volume.
   No full construction exists.
6. **Osterwalder–Schrader axioms for the limit.** Temperedness, Euclidean covariance (the D₄ point
   group is larger than the hypercubic one, and the root-moment identity `Σ k_μ k_ν = 12 δ_{μν}`
   gives second-order isotropy, but full `O(4)` restoration must be proved), reflection positivity,
   symmetry and clustering. Then OS reconstruction of a Wightman theory (M).
7. **The mass gap.** Exponential decay of connected correlations of gauge-invariant observables,
   uniformly in the continuum limit, equivalently `spec(H) ∩ (0, Δ) = ∅`. A gap is known for
   lattice gauge theory at strong coupling (cluster expansion), but the continuum limit is at weak
   coupling, where nothing is known. Unbounded self-adjoint spectral theory in Mathlib is limited (M).
8. **Nontriviality.** The limit is not a free (Gaussian) theory.

## What PM contributes (proved 2026-10-31)

- **Item 1, a lattice quantum measure: `LatticeGibbs`, `LatticeGibbsU1`.**
  - PM's D₄ action on a finite region is bounded on unitary links,
    `0 ≤ S ≤ 2N·|X|·|tri|` (`wilson_bounds`, `action_bounds`).
  - So PM's survival weight `exp(−β S)` normalizes any probability reference measure on link
    configurations to a probability measure, with `exp(−βM) ≤ Z ≤ 1` (`gibbs_isProbability`).
    Relative weights are survival ratios (`gibbs_ratio`).
  - For `U(1)`, angles in `ℝ/ℤ` with Mathlib's normalized Haar measure and the
    supplied edge assignment give a probability measure (`u1_gibbs`). Arbitrary
    assignments need not be closed under local gauge transformations.
  - The measure-theoretic statement is generic: any bounded action normalizes any probability
    measure. That the Wilson action is PM's survival cost is asserted, not derived.
  - Open: `SU(N)` (`U(N)` is `UnitaryHaar`), and the identification of PM's real-time update with
    this Euclidean measure.
- **Item 6, Euclidean covariance: `D4Isotropy`.**
  - The 24 D₄ roots have isotropic moments through degree four: first and third moments vanish,
    `Σ k_μ k_ν = 12 δ`, `Σ k_μ k_ν k_ρ k_σ = 4(δδ + δδ + δδ)` (kernel-checked).
  - Hence `Σ_k (k·w)⁴ = 12|w|⁴`, invariant under every orthogonal map
    (`quartic_rotation_invariant`). The hypercubic directions fail this (`hypercubic_not_isotropic`).
  - This is a directional root-moment theorem, not a theorem about corrections to the
    full gauge action. For midpoint links, rotated smooth U(1) fields can have different
    `O(h²)` errors (see the counterexample in `LEAN-AUDIT-YANG-MILLS.md`). Full
    `O(4)` restoration in the quantum continuum limit remains open.
- **Item 2, reflection positivity: `ReflectionKernel`, `D4Reflection`, `SiteReflection`,
  `FiniteReflection`, `FiniteD4Reflection`, `D4ActionReflection`.**
  - The positive-definite Wilson kernel and the abstract Fubini identity remain valid.
  - `D4Reflection.one_side` proves no triangle crosses the site plane. On a finite
    reflection-symmetric region, `FiniteD4Reflection` constructs the actual shared
    directed edges, reflected cells and half-action, sharing plane terms by halves.
  - `FiniteReflection.measure_preserving` proves the product Haar factorization,
    rather than assuming independence of triangle variables. `action_eq` identifies
    the geometric action with `LatticeGibbs.action`; `action_factor` proves its split.
  - `D4ActionReflection.gibbs_reflection_positive` proves the normalized Gibbs form
    real and nonnegative for all bounded measurable upper-half observables, β ≥ 0.
    The theorem uses unit lattice spacing and integer-site regions, including D₄
    regions. It needs no smooth background connection.
  - **Reciprocal extension:** `ReciprocalLinks` chooses a spatial orientation
    commuting with the site reflection and imposes the inverse on reverse edges.
    `ReciprocalReflection` uses the pushforward of a weighted product Haar input
    law. One member of each reverse pair is used; the other input is ignored. It
    proves probability normalization, gauge invariance and reflection positivity
    for this same physical measure. The original independent-directed API remains
    valid. A transfer matrix and `H ≥ 0` reconstruction remain open.
- **Item 1 for `U(N)`: `UnitaryHaar`.** The unitary group is compact (`isCompact_unitary`). Its
  normalized, left-invariant Haar measure (`haar`) gives a `U(N)` lattice measure with PM's D₄
  Wilson action on any finite region (`uN_gibbs`). The edge-to-variable assignment is arbitrary in
  that theorem and need not be closed under local gauge transformations; `SU(N)` is
  not constructed.
- **Item 3, gauge invariance: `GaugeInvariance`, `GeometricGauge`, `ReciprocalReflection`.**
  - Gauge transformations conjugate triangle holonomies and preserve the Wilson
    action. `GeometricGauge.edge_realization` connects the finite configuration
    action to the actual geometric link values.
  - Normalized compact Haar is proved right invariant by uniqueness; the geometric
    gauge maps preserve product Haar and the normalized Gibbs measure.
  - The reciprocal projection intertwines gauge transformations, so the physical
    reciprocal-link measure is gauge invariant as a pushforward statement.
  - Arbitrary edge identifications can still prevent closure; generic normalization
    theorems are not gauge-closure theorems.
- **Item 4, infinite volume: not advanced.** The finite substrate makes each finite-volume measure
  exist (item 1). It does not by itself give the thermodynamic limit.

Items 5, 7 and 8 (the renormalized continuum limit, the mass gap, nontriviality) and item 4 (infinite
volume) are untouched. They are the hard core of the problem.


## Current physical priority

The remaining PM-specific task is to identify a native carrier/record packet
transport and prove its refinement contracts. `CompositionalTransport` gives a
precise sufficient route: conservative single-source hops, identity at zero,
exact straight-edge subdivision and a C² infinitesimal response that is linear
in the edge direction (a connection one-form). A general
multi-neighbour vacuum update does not automatically have that hop factorization.
Exact all-real subdivision is a strong continuum-family contract; it has not been
proved for finite native events or for an interpolated refinement of them.

`refinement_is_extra` supplies a normalized conserving abstract-hop countermodel
that fails subdivision; its links are also reciprocal (`jump_reciprocal`). This
shows the implemented hop premises alone do not choose refinement. It is not a
countermodel to every PM postulate or to a specified native E8 implementation.
The action limit also does not identify the native required-work functional with
the Wilson sum or derive its physical equations of motion. The quantum
continuum/mass-gap program is outside this current priority.
