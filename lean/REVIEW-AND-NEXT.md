# Paper II: current proof status and remaining work

The 2026-11-01 independent-register construction narrows the state-space gap:
`IndependentRegisters` realizes independent finite labels in two explicitly
supplied Boolean banks, conserves their occupied-register count, and proves
exact coherent tensor readout. `RegisterPrograms` extends this to operator
expressions and evolution; `TensorObservation` supplies reusable composition.
Paper III applies the construction to its actual carrier labels. The physical
allocation/selection and preparation of those banks, admissible spatial gates,
complete vacuum/current schedule, comparison/reference integration and prices
remain obligations. This construction does not derive an extra free payload
factor or evade `GaugeRecordEmbedding.spinor_commutant_abelian`.

`RegisterHamiltonian` now supplies a full-generator route on those banks, using
explicit occupation-dependent register hops. Its Hermitian completion observes
any supplied Hermitian generator exactly, evolves unitarily, and conserves total
occupation and each payload bit on every sector. Paper III applies it to the
actual native vacuum. This closes that configuration-generator construction;
it retains bank/hopping admission, the chosen higher-occupation completion and
physical prices. The shared schedule and chiral-charge constructions are now
provided by `RegisterSplit` and `ChiralRegisterCurrent`; their physical admission
and identification remain distinct obligations.

The reusable finite register branch now also includes `RegisterVacuum`
(canonical full vacuum and chiral projector), `RegisterInteraction` (both-bank
Hermitian interactions), `TensorEvolution`, `TensorKernel`, `ClockDynamics`,
`RegisterReference` and `RegisterControl`. The spatial vacuum/current/reference
model uses one common encoding, explicitly counting `16·|X| + |payload|·|record|`
Boolean registers, plus its separate four-phase clock. Joint controls require
their branch to be represented in those labels; they are not certified as local
E8 primitives by a finite-permutation extension. Paper III keeps only its packet
specializations and compatibility entry points.

Reviewed during housekeeping on 2026-10-31; items 2, 3 and 6 updated the same night. Canonical proofs live under
`PMAction/` and are imported by `PMAction.lean`. The merged research wrappers,
completed task briefs and superseded progress notes have been removed.
[README.md](README.md) maps the results and their hypotheses;
[VERIFICATION.md](VERIFICATION.md) records the current check.

## Newly integrated work

| Modules | What is proved | What is not thereby selected |
| --- | --- | --- |
| `ProjectedEvolution`, `JointSpaceTime` | Stable projected unitary error bound, actual Wilson-generator tangent on the original vacuum sector, simultaneous fixed-momentum evolution and a concrete cubic refinement | The sufficient spacing/tick rule, physical clock calibration and occupation; full real-space/interacting/quantum limits remain outside the result |
| `LocalIsometricDynamics` | An all-label unitary completion with exactly the existing finite stencil, four lifted split factors, all-state readout histories, fixed-space equivalence, response identity and no new labels | Physical gate admission, completion selection and primitive pricing; this is an alternative to the directional-exponential completion, not its locality theorem |
| `RecordSupply`, `HomogeneousRouting` | Exact disturbance export and reference replacement; indefinite maintenance iff an open backward orbit for the specified universal task; finite orbits return; translation-equivariant lattice permutations are translations | Initial record/background contract, physical routing and its admissibility; homogeneity is a hypothesis of the translation classification, not a consequence of the open-orbit theorem |
| `PersistenceSelection` | With β>0 and survival exp(−β cost), maximizing survival iff minimizing cost; positive occurrence probability and unit toll give positive event price | Actual cost functional, admissible options and physical hazard |
| `ReadoutAdditivity` | Exact independent-state refresh requires enough records; additive singleton pricing is the summed flag; the mean is not additive | Which states must be refreshed, how exact refresh is physically supplied and which event-pricing law applies |
| `ChiralityConvention` | Orientation/axis exchange flips γ⁵; wall parity swaps projectors; the original reference is killed by the chosen charged projector, while its parity-exchanged zero mode is retained | Physical current/reference attachment and its action away from the kernel |
| `WeakVertex` | Kernel orthonormal-basis existence and the stated W-exchange/contact-amplitude normalization | Physical mediator/current and external-state identification |
| `WallDispersion` | Exact nonzero-link light/heavy branch formulas, idempotent eigenprojectors and trace multiplicities under the regular-branch conditions | Link selection, physical branch occupation, particle statistics or three generations |
| `RunningResponse`, `GaugeFluctuation`, `FluctuationPremises`, `FluctuationClosure` | Landau-pair expansion, spin-1 Hessian coefficient, Ward/gauge-mode identities and finite-dimensional ghost determinant power | Continuum quantum measure, regulator and physical running prescription |
| `ContinuumFields`, `LandauDegeneracy`, `LatticeToContinuum` | Concrete smooth-field Hessian/Ward instances, strip-centre density and pointwise lattice-density second variation | Site-integrated action limit, complete concrete L² spectral realization and quantum/Lorentzian limits |
| `UniformGaugeAction`, `IntegratedGaugeAction` | Explicit triangle remainder (`VaryingFields.triangleBound`); one Yang–Mills error constant on any compact region (`yang_mills_uniform`); volume-weighted tagged sums of the midpoint D₄ density on refining partitions of a box converge to `∫ (β/2) Σ ‖F‖²` (`midpoint_sampled_limit`) | Common C¹,¹ bound and continuous derivative retained; quantum measure, clock and link law not selected |
| `IntegratedScalarAction` (with explicit `ScalarTransport.linkBound`, `covBound`) | Explicit pointwise scalar bound, one constant on a compact region, and the integrated limit `∫ (3/4)·toll·m·Σ ‖(∂ + A)Φ‖²` on a box (`scalar_sampled_limit`) | Common C¹,¹ bounds and cubic-consistency constant retained; no potential or VEV |
| `ClassicalYangMills` | Any link family cubically consistent with `A`: the D₄ Wilson density, volume-weighted on refining partitions of a box, converges to `∫ (β/2) Σ‖F‖²` (`pm_lattice_yang_mills`); generator normalization derived (`generator_norm`, `canonical_from_generators`) | Local C¹,¹ bound (was global); links built from a given connection; `β`, group inputs; see [YANG-MILLS-STATUS.md](YANG-MILLS-STATUS.md) |
| `LatticeSiteAction` | Sum over the actual D₄ sites of a region with cell volume `2h⁴` (`d4_sites`, `d4Map_det`) converges to the Yang–Mills action for parallel-transport links of any connection with derivative Lipschitz on compacts (`d4_yang_mills_action`); transport unitarity derived | Old API accepts a transport witness; `TransportExistence` now constructs it; audit in [LEAN-AUDIT-YANG-MILLS.md](LEAN-AUDIT-YANG-MILLS.md) |
| `FiniteReflection`, `FiniteD4Reflection`, `D4ActionReflection` | Finite shared geometric directed-link configuration/measure split; exact equality to `LatticeGibbs.action`; half-action factorization and normalized Gibbs site-reflection positivity | Unit lattice spacing; finite reflection-symmetric integer-site region; opposite directed links independent in this API; `ReciprocalReflection` supplies the reciprocal version. Transfer matrix and PM selection remain open |
| `ConnectionRegularity`, `TransportExistence` | Literal C² hypotheses imply the compact-Lipschitz derivative conditions; global unitary transport exists for continuous skew coefficients; connection links are reciprocal; classical site-action limit with transport constructed | The connection, group, representation and β remain supplied |
| `GeometricGauge`, `ReciprocalLinks`, `ReciprocalReflection` | Concrete geometric gauge action, right Haar invariance and Gibbs pushforward invariance; one reciprocal-link measure with gauge invariance and site-reflection positivity | Finite reflection-symmetric region at unit lattice spacing; no transfer matrix or quantum limit |
| `CompositionalTransport` | Exact subdivision and infinitesimal response imply the transport ODE; conserving single-hop updates force skewness and give the classical C² site-action limit without a cubic-consistency premise | Native E8 packet implementation, exact subdivision/refinement and a C² infinitesimal response are not derived from causality alone |
| `PersistentBackground` | Under the survival law, the most persistent configuration of the native reference protocol is exactly a uniform background, every live and record cell holding the reference (`persistent_background`) | β > 0 and a positive toll; the reference value itself |
| `CompletionSelection` | Every completion `E U Eᴴ + P W P` has the same readout (`readout_same`); with a positive price per invisible displacement the most persistent one has `P W P = P` (`most_persistent_completion`), i.e. it is the identity completion (`selected_is_identity`) | The invisible-displacement price; identification with the directional-exponential completion |

These supersede the older notes that still asked for the spinor-to-trace bridge,
normalized-basis existence, spin-1 coefficient, ghost determinant power or
pointwise lattice-to-Hessian connection. Those are no longer open algebra tasks.

## Completed foundations to reuse

- Finite Hermitian transport, exact exponential and comparison response with an
  explicit quadratic remainder; finite/differentiable restoration bridges and
  coherent conservative reset.
- Actual-root carrier events, conditional logarithmic/quarter-phase reconstruction,
  native reference permutation, finite register configuration and distinct
  one-hot amplitude lift, stationary backgrounds and conditional setup ledger.
- Intrinsic coordinate-odd carrier representation of the chosen full vacuum
  Hamiltonian, exact exponential intertwining and parity-derived no-feedback
  for the certified native operator library.
- Concrete two-wall spectra and kernels, corrected local split, global safe-tick
  existence, uniform C T²/N time-refinement estimate, actual finite-torus Fourier
  identification and light/heavy spatial dispersion control.
- Link extraction and frame law for supplied linear single-hop updates, cubic-link
  robustness and pointwise gauge/scalar density limits under their stated
  consistency, regularity and pricing hypotheses.
- Charged/neutral current algebra, contact matching, massive trace cancellation,
  normalized spin sums and the actual bilinear-amplitude-to-trace factor 64.

## Remaining work, in dependency order

1. **Physical states and observations.** Justify the complex-amplitude/coordinate
   readout contract, carrier class and wall allocation; identify the other/even
   modes and any many-particle state space/statistics. The native representation
   is constructed, but physical selection is not proved by equal dimensions or
   reversible persistence alone.
2. **Primitive admission and physical completion selection.** The mathematical
   finite-support existence gap is closed by `LocalIsometricDynamics`: extending
   the local split through the on-site carrier isometry and fixing its complement
   gives a unitary on all 16 labels, with the same finite stencil and four-factor
   schedule. Every ambient readout follows the original update at every tick;
   invisible modes are retained, and full squared-displacement response agrees
   with the coordinate response. Still derive admission/implementation of those
   local amplitude factors in the microscopic E8 gate library and their prices.
   The earlier directional-exponential completion still has its proved tails;
   the two completions are not identified. *Conditional selection:* identity evolution on the invisible complement
   minimizes the explicit positive displacement price (`CompletionSelection`).
   The family-restricted theorem also requires that option to be physically admitted.
3. **Reference, records and vacuum coexistence.** Specify a capacity-aware
   allocation or schedule where reference and spinor readouts share carriers.
   The chosen projector retains the exchanged reference zero mode, but this does
   not identify its physical weak-maintenance task or supply independent storage.
   *Conditional construction:* `PersistentBackground` minimizes an explicitly
   supplied excess-change price. Its family-restricted theorem requires a
   stationary witness in the admissible/conserved family. `ReversibleStationarity`
   proves that iterating the same closed native routing does not prepare its
   own stationary background from a moving seed. Other gate preparations and
   open sources are not excluded. A clean
   initial supply for `RecordSupply` therefore remains an identified source contract. Exact maintenance forever forces
   an open orbit and an infinite substrate (`HomogeneousRouting.forever_iff_open`,
   `forever_needs_infinite`). Still open: the per-tick ledger of that supply, and the
   physical selection and preparation of the allocation. `RegisterReference`
   now supplies a capacity-aware witness on the same spatial configuration as
   `RegisterSplit`: the payload × record bank is fully counted, current evolution
   and record permutations have order-independent all-state readout, and the
   current acts on the supplied exchanged reference. No fresh-record source or
   routing price follows from this finite construction.
4. **Physical clock and event ledger.** `RegisterSplit` now constructs the full
   four-phase schedule with exact phase/tick readout; `ClockDynamics` proves
   unitary evolution even on coherent clock amplitudes. Relate this supplied
   schedule to the substrate clock and price setup, controls,
   transport/source/export and required maintenance. Four factor applications
   are not automatically four primitive E8 events. Survival minimization orders
   a supplied cost; it does not determine that cost or identify net comparison
   response with total required work.
5. **Microscopic gauge transport and smooth refinement.** Identify the finite E8
   payload/record realization of the abstract hop and physical readout/price law.
   Derive cubic edge consistency, sufficient regularity and shared group/trace
   normalization across spacings. Unitarity, finite per-spacing smoothness and
   bounded density do not by themselves supply the needed refinement law.
   The mathematical subdivision route is now proved in `CompositionalTransport`:
   exact hop-update composition plus a C² infinitesimal response gives the transport
   equation and classical action limit; conservation supplies skewness.
   `NativePacketUpdate` now establishes those contracts for the native E8 packet
   subsystem, with its carrier/readout realization (`readout_hop`, `embed_hop`) and
   a unique realization. Remaining: the smooth controls and the admission of the
   coherent root-generator evolution as the substrate's dynamics. A general multi-neighbour vacuum
   update is not automatically the single-source conservative hop used here.
   Configuration-space gauge closure, Haar/Gibbs invariance and reciprocal-link
   site-reflection positivity are now proved for the geometric model.
   Arbitrary edge-identification quotients still need their own closure proof.
6. **Full field and integrated limits.** The previously proposed fixed-momentum
   joint evolution route is completed in `JointSpaceTime`, including the stable
   intertwining estimate, canonical vacuum sector, projected generator convergence,
   all-kernel-state limit and concrete a=1/(r+1), N=(r+1)³ refinement. The general
   sufficient rule is a→0 and 1/(a²N)→0; it is not a physical clock-selection law.
   Extending this momentum-block result to a full real-space field/PDE requires
   the corresponding mode/domain control, and interactions need further estimates.
   *Closed (2026-10-31) for the classical gauge and scalar actions on a box:*
   uniform compact-region estimates and the site-sum-to-integral limit
   (`UniformGaugeAction`, `IntegratedGaugeAction`, `IntegratedScalarAction`), under a
   common C¹,¹ bound and cubic consistency. `LatticeToContinuum` remains the pointwise
   Hessian-density limit; the integrated Hessian, the full real-space fermion field
   and interactions are still open.
7. **Physical applications.** Identify the weak current/mediator, statistics,
   normalization, measure and regulator before reading the trace/running
   results as physical predictions. Gravity and measurement need their own
   state/update/observable constructions. Quantum continuum and Lorentzian
   continuation remain distinct obligations.

No research assignment is active. A surviving mathematical or physical question
belongs in this list, rather than an old task brief. When multiple updates persist,
prove their common consequences and surviving freedom instead of selecting one by
agreement with a measured number.

## Downstream boundary

Paper II supplies generic dynamics without importing later papers. Paper III owns
packet representations, sector/resource ownership and constants; Paper IV owns
flavour/mass applications; Paper V owns decay/phase-space/lifetime applications;
Paper VI owns cosmology. Moving a generic proof upstream does not move an
application's physical identification assumptions with it. See
[FOUNDATION-PLACEMENT.md](FOUNDATION-PLACEMENT.md).

## Dependency review and improved routes (2026-11-01)

The missing spinor/amplitude, kernel-basis, finite spectrum and classical site-sum
results are already available. They should not be assigned again as Paper III blockers.
The new shared work is:

- `FiniteEncoding`, `RayPersistence` and the generic maintenance-control theorem
  own proofs previously duplicated or placed in Paper III. Compatibility names remain.
- `SectorObservation` and `CarrierClassBundle` combine the actual class-sector
  vacuum models, including the common Hamiltonian/evolution and class-independent
  observed wall parity. This is simpler than imposing the cyclic pair encoding on
  the vacuum. It leaves a degenerate class multiplicity; physical admission,
  interaction/current identification and a breaking law still need derivation.
- `InvolutionComparison` removes the independent global branch-marker requirement
  for native involution-phase words. A five-call circuit, or nine forward calls
  after expanding inverse quarters, is exact. This does not give a universal
  free mixer or price a spectral phase as one primitive event.
- `SpatialComparison` is a concrete two-cell implementation of that branch
  register. It is isometric, fully unitary, observed exactly on every ambient
  state, and fixes outside cells. The cells and the supplied payload/control
  permutations must still be admitted, prepared and priced. A spatial pair is
  not identified with the already occupied chirality wall.
- Family-restricted background and completion selection retain accessibility and
  baseline costs. Closed reversible evolution cannot finitely prepare a globally
  stationary background from a moving state.

The finite shared construction now provides a capacity-aware state/current
route for spinor, internal payload and records, with joint controls on allocated
labels and the full spatial split/clock. Its physical allocation, preparation,
charge/current attachment and coherent gate admission remain a contract to
identify. Reuse `GaugeRecordEmbedding.spinor_commutant_abelian` rather
than treating spinor modes as an independent non-Abelian payload. Then price the
admitted spatial/root-phase schedule, including cell preparation, controls and
occupied-record renewal/export, before applying it to Paper III's gauge/η
contracts. State-space realization alone does not establish those prices or
select the observed couplings.
