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

**What this does not show.** In every version the link field is constructed from a given smooth
connection. No theorem derives the links from PM's substrate update, so this establishes that
D₄ Wilson triangles are a correct discretization of Yang–Mills, not that PM produces Yang–Mills.
The gauge group, `N`, `β` and the existence of the transport solution are inputs. The density is
Euclidean. All of this is about fixed smooth classical fields.

## The quantum problem, and what is missing

The Clay statement (Jaffe–Witten): for a compact simple gauge group `G`, construct a quantum
Yang–Mills theory on `ℝ⁴` satisfying the Wightman axioms (equivalently, Osterwalder–Schrader
axioms for its Euclidean Schwinger functions), and prove a mass gap `Δ > 0`. None of the following
exists in this project, and items marked (M) also lack Mathlib infrastructure.

1. **A lattice quantum measure.** A finite-volume, finite-spacing probability measure
   `Z⁻¹ exp(−S(U)) Π_edges dHaar(U)` on link configurations, with `S` PM's D₄ action. Now done for
   `U(1)` and `U(N)` (see below); `SU(N)` is not constructed. Also missing: why PM's real-time unitary update
   gives a Euclidean measure (a transfer-matrix or Wick-rotation identification). PM's survival
   weight `exp(−β·cost)` has the Gibbs form, but identifying it with this measure is not proved.
2. **Reflection positivity.** The finite site-reflection bridge is now proved for
   the existing D₄ action on shared geometric directed links, with product `U(N)`
   Haar and a reflection-symmetric finite integer-site region; see below. Opposite
   directions are independent. The reciprocal-link version, link-reflection and
   transfer-matrix/nonnegative-Hamiltonian reconstruction remain open.
3. **Gauge-invariant observables.** The observable algebra: Wilson loops and local gauge-invariant
   fields, with gauge fixing or a gauge-invariant construction of the measure's moments.
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
  - For `U(1)`, this is fully concrete: angles in `ℝ/ℤ` with Mathlib's normalized Haar measure, and
    PM's D₄ action, give a probability measure on any finite region (`u1_gibbs`).
  - The measure-theoretic statement is generic: any bounded action normalizes any probability
    measure. That the Wilson action is PM's survival cost is asserted, not derived.
  - Open: `SU(N)` (`U(N)` is `UnitaryHaar`), and the identification of PM's real-time update with
    this Euclidean measure.
- **Item 6, Euclidean covariance: `D4Isotropy`.**
  - The 24 D₄ roots have isotropic moments through degree four: first and third moments vanish,
    `Σ k_μ k_ν = 12 δ`, `Σ k_μ k_ν k_ρ k_σ = 4(δδ + δδ + δδ)` (kernel-checked).
  - Hence `Σ_k (k·w)⁴ = 12|w|⁴`, invariant under every orthogonal map
    (`quartic_rotation_invariant`). The hypercubic directions fail this (`hypercubic_not_isotropic`).
  - So the `O(h²)` lattice artifacts of PM's D₄ action are `O(4)`-invariant; rotation symmetry is
    broken first at higher order. Open: `O(4)` restoration in the quantum continuum limit.
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
  - **Convention boundary:** opposite directed edges are independent. The reciprocal
    constraint `U(y,x) = U(x,y)†` is not imposed or selected from PM. Thus the bridge
    is closed for this explicit directed-link model, while the reciprocal-link model,
    transfer matrix and `H ≥ 0` reconstruction remain open.
- **Item 1 for `U(N)`: `UnitaryHaar`.** The unitary group is compact (`isCompact_unitary`). Its
  normalized, left-invariant Haar measure (`haar`) gives a `U(N)` lattice measure with PM's D₄
  Wilson action on any finite region (`uN_gibbs`). The edge-to-variable assignment is arbitrary in
  that theorem; `SU(N)` is not constructed.
- **Item 3, gauge invariance: `GaugeInvariance`.** Gauge transformations conjugate every triangle
  holonomy (`holonomy_gauge`). So Wilson loops, PM's action and the survival weight are gauge
  invariant (`wilson_gauge`, `action_gauge`, `weight_gauge`). Open: invariance of the full Gibbs
  measure as a pushforward statement, which needs two-sided Haar invariance on each link.
- **Item 4, infinite volume: not advanced.** The finite substrate makes each finite-volume measure
  exist (item 1). It does not by itself give the thermodynamic limit.

Items 5, 7 and 8 (the renormalized continuum limit, the mass gap, nontriviality) and item 4 (infinite
volume) are untouched. They are the hard core of the problem.
