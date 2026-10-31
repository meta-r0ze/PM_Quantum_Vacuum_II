# Yang–Mills: what PM proves, and the open quantum problem

## Proved: the classical continuum limit with canonical normalization

`PMAction.ClassicalYangMills` (standard axioms only):

- **`pm_lattice_yang_mills`.** Take a `u(N)`-valued `C^{1,1}` connection `A` on `ℝ⁴` with continuous
  derivative. Take PM's actual unitary link family `U`, cubically consistent with `A` (within `K h³`
  of the midpoint exponentials, one `K` on the region). PM's Wilson density on the D₄ minimal
  triangles, `(β/12) Σ_△ Re tr(1 − U_△)/h⁴`, accumulated with cell volumes on any refining tagged
  partitions of a box `I` as `h → 0⁺`, converges to `∫_I (β/2) Σ_{μν} ‖F_{μν}‖²_F`.
- **`canonical_density`.** With `β = 1/g²` and `‖F_{μν}‖²_F = (g²/2) Σ_a (F^a_{μν})²`, the limit is the
  canonical Lagrangian `(1/4) Σ_{μν a} (F^a_{μν})²`.
- **PM's coupling.** Event pricing fixes `β`: a summed-read sector is canonical exactly when
  `g² = 1/(κ·toll·m·W)` (`SummedReference.sum_canonical_iff`).
- **Supporting results:**
  - `link_yang_mills_uniform`: one error constant on any compact region.
  - `IntegratedScalarAction`: the same limit for the scalar action.
  - Perturbative inputs: the one-loop `b₀` from spin-½, spin-0 and spin-1 response
    (`RunningResponse`, `GaugeFluctuation`), the ghost determinant power (`FluctuationClosure`), the
    Landau degeneracy, and the pointwise lattice Hessian (`LatticeToContinuum`).

**Hypotheses kept:** `C^{1,1}` fields with one Lipschitz constant on the box; cubic link
consistency, which says the links discretize `A`. It is a theorem when each link is the parallel
transport of `A` along its edge (`ParallelTransport.transport_consistent`), and
`ParallelTransport.pm_lattice_yang_mills_transport` gives the limit for parallel-transport links with
no consistency hypothesis (global Lipschitz `DA` instead). `GaugeTransport` shows unitarity, locality
and conservation alone do not imply it;
a bounded box. All of this is about fixed smooth classical fields.

## The quantum problem, and what is missing

The Clay statement (Jaffe–Witten): for a compact simple gauge group `G`, construct a quantum
Yang–Mills theory on `ℝ⁴` satisfying the Wightman axioms (equivalently, Osterwalder–Schrader
axioms for its Euclidean Schwinger functions), and prove a mass gap `Δ > 0`. None of the following
exists in this project, and items marked (M) also lack Mathlib infrastructure.

1. **A lattice quantum measure.** A finite-volume, finite-spacing probability measure
   `Z⁻¹ exp(−S(U)) Π_edges dHaar(U)` on link configurations, with `S` PM's D₄ action. Missing: a
   concrete Haar measure on products of `SU(N)` (M). Also missing: why PM's real-time unitary update
   gives a Euclidean measure (a transfer-matrix or Wick-rotation identification). PM's survival
   weight `exp(−β·cost)` has the Gibbs form, but identifying it with this measure is not proved.
2. **Reflection positivity.** Osterwalder–Seiler prove it for the hypercubic Wilson action. It is
   not proved for the D₄ triangle action. It is what gives a Hilbert space, a transfer matrix and a
   Hamiltonian `H ≥ 0`.
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
  - Open: `SU(N)` needs compact Haar measure on the unitary group, which this Mathlib does not
    provide as instances. The identification of PM's real-time update with this Euclidean measure
    is also open.
- **Item 6, Euclidean covariance: `D4Isotropy`.**
  - The 24 D₄ roots have isotropic moments through degree four: odd moments vanish,
    `Σ k_μ k_ν = 12 δ`, `Σ k_μ k_ν k_ρ k_σ = 4(δδ + δδ + δδ)` (kernel-checked).
  - Hence `Σ_k (k·w)⁴ = 12|w|⁴`, invariant under every orthogonal map
    (`quartic_rotation_invariant`). The hypercubic directions fail this (`hypercubic_not_isotropic`).
  - So the `O(h²)` lattice artifacts of PM's D₄ action are `O(4)`-invariant; rotation symmetry is
    broken first at higher order. Open: `O(4)` restoration in the quantum continuum limit.
- **Item 2, reflection positivity, the kernel half: `ReflectionKernel`.**
  - The Osterwalder–Seiler kernel is positive definite: `Σ c_i c_j exp(β Re tr(U_i U_jᴴ)) ≥ 0` for
    `β ≥ 0` (`wilson_kernel_psd`). The proof is an induction on Gram-kernel powers
    (`gram_power_psd`) and the exponential series (`gram_exp_psd`).
  - Open: the geometric half for D₄. Every triangle crossing a reflection plane must factor as
    `tr(Φ Ψᴴ)` with `Φ`, `Ψ` on opposite sides. Then the transfer matrix and `H ≥ 0` follow.
- **Item 2, reflection positivity, now both halves: `D4Reflection`, `SiteReflection`.**
  - The site reflection `x₀ ↦ −x₀` maps D₄ roots and triangles to themselves (`reflect_tri`), and
    no D₄ triangle crosses its plane (`no_crossing_pair`, `one_side`). So PM's action splits as
    `S₊ + θS₊`.
  - For an action that splits this way, `∫ F · θF · e^{−S} = ∫_plane |G_F|² ≥ 0`
    (`reflection_identity`, `reflection_positive`). More generally, the OS form is the `L²` inner
    product of the plane functions `G_F` (`os_inner_product`), so the physical Hilbert space is
    the closure of the `G_F` in `L²(plane)`.
  - Open: the transfer matrix and the Hamiltonian `H ≥ 0` built from it.
- **Item 1 for `U(N)`: `UnitaryHaar`.** The unitary group is compact (`isCompact_unitary`). Its
  normalized, left-invariant Haar measure (`haar`) makes the `U(N)` lattice measure of PM's D₄
  action concrete on any finite region (`uN_gibbs`).
- **Item 3, gauge invariance: `GaugeInvariance`.** Gauge transformations conjugate every triangle
  holonomy (`holonomy_gauge`). So Wilson loops, PM's action and the survival weight are gauge
  invariant (`wilson_gauge`, `action_gauge`, `weight_gauge`). Open: invariance of the full Gibbs
  measure as a pushforward statement, which needs two-sided Haar invariance on each link.
- **Item 4, infinite volume: not advanced.** The finite substrate makes each finite-volume measure
  exist (item 1). It does not by itself give the thermodynamic limit.

Items 5, 7 and 8 (the renormalized continuum limit, the mass gap, nontriviality) and item 4 (infinite
volume) are untouched. They are the hard core of the problem.
