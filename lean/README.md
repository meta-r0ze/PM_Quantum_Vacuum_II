# PM-2-Action: Lean formalization

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum II: Operational Action and the
Emergent Lagrangian*. This package contains the shared dynamics, event accounting and
action-response mathematics used by the later papers.

## Main result

`PMAction.Main.hermitian_action_response` (`PMAction/MainTheorem.lean`) packages the constructed
dynamics/readout result; `LinkEvolution` identifies its transport with the exponential. For a
supplied finite Hermitian generator H and normalized complex amplitude φ,

- its spectral transport is unitary and equals exp(i t H);
- its two-branch comparison is unitary and has an exact coherent inverse;
- its comparison response is (1 − Re⟨φ,Uφ⟩)/2 = ‖φ − Uφ‖²/4;
- within an explicit positive step radius, the squared displacement differs from
  t²‖Hφ‖² by at most an explicit nonnegative coefficient times t⁴.

`PMAction.Main.hypotheses_satisfiable` gives a finite witness for these mathematical hypotheses.
The theorem constructs a consistent response model; it does not select H, a physical vacuum,
its gauge representations or a primitive implementation from persistence alone.

The concrete fermion branch proves an eight-component Hermitian Wilson/domain-wall
Hamiltonian, its signed spectrum, and a finite-range unitary split update.
`GlobalTickInterval.global_fixed_iff` now proves that **one positive tick interval works
throughout the whole momentum cell**: the corrected split's stationary kernel equals the
Wilson Hamiltonian kernel. Only zero momentum supports nonzero stationary vectors, with
exactly the four known free components. The safe interval's existence is proved; its
numerical or maximal endpoint and physical tick selection are not. See
[GLOBAL-TICK-INTERVAL.md](GLOBAL-TICK-INTERVAL.md).

The earlier explicit inverse-gap bounds, local pi/10 tangent analysis and nonlinear
near-origin results remain useful refinements; see [SPECTRAL-SAFETY.md](SPECTRAL-SAFETY.md).

`VacuumIteration.fixed_time_convergence` now proves that repeating the corrected split
at tick T/N converges to the exact Wilson exponential at each fixed momentum and elapsed
time. It includes a finite-step operator-norm error bound and convergence on internal states.
`VacuumErrorRate` strengthens this to an explicit C T²/N bound with the same constant
at every momentum. A joint space–time evolution limit and an explicit numerical
global tick endpoint remain open; see
[MANY-TICK-CONVERGENCE.md](MANY-TICK-CONVERGENCE.md).

The reviewed controlled-limit results are now default modules:

- `RealSpaceFourier` proves inversion, exact block evolution and spectral identification
  for the **actual finite-torus update**. One tick bound, uniform in torus size,
  leaves precisely spatially constant fields in the wall kernel stationary.
- `SpatialContinuum` proves the massless light-branch dispersion limit at k = a p
  with an explicit error bound, and E²/a² ≥ 1/a² on the heavy branch. This is
  branchwise Hamiltonian spectral control; full spatial evolution, joint tick/spacing
  scaling and physical species identification remain separate.
- `VaryingFields` proves the pointwise non-Abelian D4 triangle density limit with
  O(h) error for specified midpoint-exponential links and skew-Hermitian connections.
  Its formal hypotheses require differentiability everywhere and a global bound
  ‖DA(y) − DA(x)‖ ≤ L ‖y − x‖ about the base point. A local-only regularity
  version, identification with record links, site integration, quantum continuum
  and Lorentzian dynamics are not proved. Group, representation and normalization
  remain inputs. See [the reviewed contribution note](research/controlled-limits/NOTE.md).

`LinkConsistency` extends the conditional gauge limit to any one shared unitary
edge family with cubic per-edge consistency. The actual-link and midpoint densities
differ by O(h), with the same limit. A constant −1 unitary-link countermodel has
density 32β/h⁴, so unitarity alone cannot select a smooth connection family. The
consistency law, physical representation and normalization still need derivation.

`GaugeTransport` starts with a supplied complex-linear, single-source-hop packet
update rather than a link field. It extracts unique links, derives unitarity from
local quadratic-norm conservation, and proves frame-covariant transport and an
exactly frame-invariant triangle action. Cubic consistency then gives the existing
pointwise limit for the update's own links. This is a continuum-indexed hop model,
not a derived finite E8 payload encoding or a consequence of general causality alone.

For a supplied uniform basis sampler and repair/toll convention, the module proves
β = toll·m·W/(2N) and the corresponding event-priced density limit. A physical
probability/cost interpretation needs N > 0 and appropriate sign conditions; the
sampler and primitive prices are not selected. A bound on normalized density
bounds triangle holonomy, while the switched-refinement theorem shows that
smoothness at each spacing need not produce one continuum limit (conditional on
a regular connection with nonzero limiting density). The smooth refinement law,
physical group/normalization and finite record realization remain open.

`SplitCovariance` proves wall-parity covariance of the chosen sine-momentum
Hamiltonian, ordered split, powers and exponential. `ReferenceWalkParity` checks
stream-exchange/reversed-neighbour covariance and stationary-reference consequences.
These retain the specified update; they do not select physical parity, a general
flavour-link symmetry or a mass phase.

Root-transfer reconstruction now supplies a further conditional route:
[ROOT-TRANSFER-RECONSTRUCTION.md](ROOT-TRANSFER-RECONSTRUCTION.md). For the specified
lazy actual-root transfer, Lean verifies the logarithmic generator against the
two-tick operator and derives a coherent quarter-pulse, retaining its scalar phase.
A two-history Gibbs model supplies a conditional rate, and integer tick matching
imposes an explicit calibration. Physical phase implementation and its primitive
price remain open; the statistical transfer itself is proved nonunitary.

The local repair now also has an actual-carrier realization: `ActualRootRepair` uses
exactly the four moving vector-class labels for two live and two record modes. The
existing root performs the exchange, preserves population and retains all input;
the arriving record must be prepared. `RootBranchEncoding` links its branch action
to reconstructed phase evolution. `RootPulseEvents` derives distinct endpoint-label
and comparison-event probabilities, rather than assigning both one tariff. See
[ROOT-TRANSFER-RECONSTRUCTION.md](ROOT-TRANSFER-RECONSTRUCTION.md) for the exact scope.

`RootWalkEncoding` now gives the explicit on-site carrier/spinor isometry and
intertwines the actual root with the reference walk's gamma repair. `RootCarrierWalk`
extends the four-component reference protocol unitarily to actual carrier amplitudes,
without adding off-site dependencies. `RootCarrierCycle` proves its finite prepared-record
horizon. This is a constructed reference protocol, not a selection of the full vacuum split
or a derivation of control/source prices.

`RootReferencePreparation` now supplies the specified reference by one existing root
from a known, distinct carrier seed. For a finite array it proves exact preparation and
one sitewise change per supplied seed as the minimum for that conversion task.
The old spinor seed is already coherent in this carrier frame. Neither source is
selected for free, and this does not implement the general comparison mixer.

`ReferenceSourceBoundary` tests two uniform-source proposals separately: closed
unitaries preserve the incoherent mixture I/8, and reconstructed root/involution
phase words fix a coherent constant-amplitude state. Neither supplies the basis
reference under those respective contracts. These are conditional source bounds,
not an identification of either source with the physical vacuum.

The zoom-out now gives a more direct state/update construction. `NativeCarrierProtocol`
proves the entire constructed reference walk equals a native permutation: opposite
streams, the existing root at the coupling site, and fixed unused labels. No coherent
frame-change gate needs to be executed for that particular protocol. `NativeCarrierState`
specifies finite register configurations and their distinct one-hot amplitude sector.

`NativeReferenceBackground` classifies stationary matching-reference fields, connects the
coherent background to the first-wall zero kernel and preserves discrepancy norm.
Positive value-change minimization is conditional on its price rule and an admissible
stationary candidate within the conserved family. It does not fix the reference value.
`FullCarrierIdentification` rules out the onto single-root/doubled-gamma identification
and full carrier-permutation Clifford pairs.

The internal representation now has an intrinsic candidate: `CarrierParity` proves
that coordinate-linear readouts are exactly the antipodal-odd sector of each actual
minimal carrier class, with projector (I − N)/2. It works for all three classes;
no class or unitary frame is selected by matching a measured value. Two actual D4
sectors of one fixed class give eight odd coordinates among sixteen label amplitudes.
The other class in the 32-channel inventory is not discarded by a selection theorem;
invariance under the entire E8 Weyl group is not claimed.
`SubstrateWeylRoots` checks the integral E8 roots, norm/glue preservation and both
embedding diagrams. `CarrierWeyl` gives explicit root words for beta, chirality,
two directional generators and the real signed permutation −i alpha₁.
`OrthogonalRootPhase` supplies the remaining common factor i from four individual
orthogonal-root reconstructed phases at a specified positive time, without assuming
a lazy transfer for the composite antipodal instruction. The common transfer rate
and physical admission/time price of those phases remain inputs.

`CarrierClifford` checks the native generators' Clifford relations on that entire
odd sector. `CarrierVacuumSector.full_intertwining` matches the **full** chosen
two-wall Hamiltonian, for all momenta and detunings, including both wall couplings.
Its intrinsic odd restriction is Hermitian; isometric conjugation is a proved
consequence of the root/phase construction. `CarrierVacuumEvolution` proves the
sector dimension, exact exponential intertwining, real-time unitarity and identical
squared-displacement response. Zero generator on the even complement is an explicit
mathematical extension convention, not a physical filtering operation.

`CarrierReadoutQuotient` gives a second interpretation that does not require
all initial states to be odd: coordinate readouts are insensitive exactly to even
backgrounds. Two states have the same readout precisely when their difference is
even. The observed full evolution is unchanged by any background generator with
no feedback into these coordinates. This leaves background states/dynamics present;
the coordinate-readout contract still needs physical justification. The general
no-feedback hypothesis here is derived for the certified `StateIdentification`
constructions described below, not for arbitrary updates.
Invisible background dynamics may still consume required work; this quotient does
not remove them from the physical event ledger.

`StateIdentification` now derives no-feedback for the certified native operator
library from parity, with closure under products, adjoints, exponentials and spatial
tensoring. A Hermitian full-label completion is observed exactly as the vacuum
Hamiltonian, with the native split's odd branches and torus spectrum. It does not
need the older zero-even-action convention; its Hermitian assembly remains a choice.
The reference contrasts occupy the same readout as first-wall spinor components,
so their allocation/schedule and source need physical justification. A four-phase
factor clock gives 4m events per m ticks from a prepared phase-zero register; its
capacity, substrate-clock relation and primitive prices remain open.

`NativeLocalityBoundary` records an implementation limit: on a five-site cycle,
the full-label directional exponential has distance-two entries at arbitrarily
small ticks. The observed odd factor retains the nearest-neighbour stencil.
Full-label unitarity and observed locality therefore do not supply a full-label
finite-stencil theorem for this completion. A causal microscopic completion/circuit
and its price remain part of the physical bridge.

This closes an internal **realization**, not unique physical selection. Complex
amplitudes, accessible odd coordinate readouts, the assignment of wall components
to the D4 halves, the cross-sector coupling, sine-momentum rule and coefficients
still need physical justification. Neither a primitive circuit/event tariff nor the
corrected spatial split is selected by these identities. See
[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md).

## Premises and consequences

| Supplied premise or model choice | Lean location | Checked consequence |
| --- | --- | --- |
| Finite positive history weights and limiting selection score | `PMFramework.Gibbs`, `LawSelection`; `Survival`, `SelectedSampling` | Normalization, ordering and conditional concentration/selected carrier law |
| Stationary detailed balance and injective statistical transfer | `Reconstruction` | Symmetric transfer, positive two-tick operator, real logarithmic energies and norm-preserving phases |
| A finite Hermitian generator and complex amplitudes | `HermitianTransport`, `LinkEvolution`, `FixedSpace` | Unitary group, basis independence, controlled response, exact fixed-space/phase-alias criterion |
| Prepared reference branch and coherent comparison | `CoherentComparisonRepair`, `ControllerHamiltonian` | Exact uncomputation; exp(z K(H)) = C(exp(z H)); trace and prepared-state response identities |
| Paper I carriers, a specified E8 root event, and supplied sampling | `CarrierEvents`, `SubstrateReflection`, `CarrierCost`, `EventAccounting` | Actual carrier support, root restriction, counted/expected event cost |
| One flag-price rule with a supplied toll and repair length | `InterferenceReadout`, `CarrierResponse`, `CommonResponse`, `LinkExpansion` | Gauge cosine, fermion Wilson form and scalar covariant difference from the same defined readout |
| Required jobs, additive prices, clean records | `RefreshSchedule`, `ReferenceMaintenance` | Minimum executable repair cost, reversible record retention, and limits on record reset/reuse |
| Chosen Clifford/Wilson matrices and split ordering | `ConcreteFermion` through `GlobalTickInterval` | Signed spectrum, exact vacuum kernel, unitary 27-site propagation, first-order generator consistency, tick-refinement convergence and a global sufficiently-small-tick fixed-space theorem |
| Actual carrier coordinate-odd sector, specified root phases and supplied two-wall/spatial coupling ansatz | `CarrierParity` through `CarrierReadoutQuotient` | Native internal Clifford realization, full Hamiltonian and exponential intertwining; physical sector/admissibility/price selection remains open |
| Actual finite periodic split update and Fourier characters | `RealSpaceFourier` | Exact mode evolution/inversion and spectral equivalence; uniform-small-tick classification of all stationary fields |
| Wilson Hamiltonian at k = a p and the stated branch | `SpatialContinuum` | Light dispersion tends to unit-speed massless form; scaled heavy-branch lower bound |
| Smooth skew-Hermitian connection, midpoint links, global derivative bound, supplied β/group/trace | `VaryingFields` | Pointwise D4 non-Abelian classical density with O(h) error; microscopic link consistency remains open |
| Constant Abelian triangle flux and cell-volume convention | `D4Gauge`, `GaugeContinuum` | Exact area tensor, remainder bound and Maxwell limit conditional on beta = 1/(2g²) |
| Quadratic occupancy/quartic potential ansatz | `Governor`, `Potential`, `Operators` | Conditional signs, minima and leading operator bookkeeping |
| Supplied doublet generators, chiral involution and charge convention Q = T₃ + Y/2 | `ChargedCurrent`, `NeutralCurrent` | Charged vertex coefficient g/(2√2), orthogonal neutral-field rotation and Z current T₃ − s² Q |
| Stated flavour-link Hamiltonian and parity-combined exchange | `WallExchange` | Exact exchange covariance; covariance with the same link iff it is Hermitian |
| Hamiltonian-derived Dirac matrices and specified trace/coupling/spin-average expression | `VATrace` | Exact V−A trace contraction and factor 64; physical spinor/amplitude bridge remains separate |
| Supplied spin/index rule and massive-current exchange coefficient | `RunningCoefficients`, `ContactMatching` | One-loop coefficient arithmetic and contact limit; G_F = 1/(√2 v²) under the mediator mass relation |

**Not derived inside Lean:** the physical update/representation selection, its identification
with the concrete spatial walk, the controller's branch preparation/local implementation and
primitive prices, a common physical normalization, the scalar kinetic/scale inputs, and the
spin/orbital loop responses. Squared-amplitude readout is an input, not a derived Born rule.
Gravity and apparatus measurement require additional constructions.

The spin formula in `RunningCoefficients` is a stated continuum input: its arithmetic is proved,
not a substrate derivation of 11/3. `ContactMatching` starts from a supplied vertex/propagator
coefficient. `ChargedCurrent` now derives its scalar vertex normalization for the stated
doublet/projector conventions; physical chirality, the current interaction and propagator
remain inputs. The contact-limit cancellation does not establish those identifications.

## Layout

| Path | Contents |
| --- | --- |
| `PMAction/MainTheorem.lean` | Constructed dynamics/comparison/response theorem and satisfiable hypotheses |
| `Reconstruction`, `HermitianTransport`, `LinkEvolution`, `FixedSpace` | Statistical reconstruction, spectral transport, exponential and fixed-space analysis |
| `Protocol`, `Gauge`, `D4Gauge`, `GaugeContinuum`, `VaryingFields` | Link covariance, geometry, constant-Abelian and conditional varying non-Abelian density limits |
| `RealSpaceFourier`, `SpatialContinuum` | Actual finite-torus Fourier/spectral bridge and branchwise spatial dispersion estimates |
| `ReferenceWalkParity`, `SplitCovariance` | Reference-stream parity and exact specified-Hamiltonian/ordered-split covariance |
| `StateIdentification` | Parity-derived observation, native Hermitian completion, real-space split/branches, record contrasts and prepared four-phase clock |
| `LinkConsistency` | Conditional cubic-edge robustness of the D4 density and a unitary countermodel |
| `GaugeTransport` | Unique link extraction from supplied conserving single-hop updates, frame covariance/invariance, conditional event-priced action and refinement freedom |
| `ExponentialLocality`, `NativeLocalityBoundary` | General second-derivative propagation test and a full-label directional-factor locality boundary |
| `CarrierEvents`, `SubstrateReflection`, `CarrierCost`, `EventAccounting`, `SelectedSampling` | Substrate carriers, actual root operation, sampling and event prices |
| `InterferenceReadout`, `CarrierResponse`, `CommonResponse`, `LinkExpansion`, `CoherentComparisonRepair`, `ControllerHamiltonian` | Shared readout, quadratic bounds, coherent repair and generator lift |
| `RefreshSchedule`, `ReferenceMaintenance` | Generic minimal-work schedules and reversible reference tasks |
| `CoherentRecordRestoration` | Exact finite-mode amplitude repair, unitary record routing and record-capacity bounds |
| `RestorationResponse` | Universal conservative-reset response; normalized balanced preparation; gain-trace versus mean/sum accounting and round-trip prices |
| `GaugeRecordEmbedding`, `GaugeRecordLinks` | Independent payload gauge index, isometric record embedding, covariant preparation/exchange and local link transport |
| `OpenReferenceFlow`, `PrimitiveRecordBoundary` | Reversible open renewal with explicit source consumption; obstruction to fixed-basis permutation/phase preparation |
| `InvolutionSpectral`, `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting` | Actual-root statistical transfer, verified logarithmic generator, coherent quarter preparation, conditional Gibbs/clock calibration and event-cost boundary |
| `RootWalkEncoding`, `IsometricDynamics`, `RootCarrierWalk`, `RootCarrierCycle` | Explicit carrier/spinor frame, conservative dynamics extension, inherited spatial dependencies, exact reference-flow evolution and finite prepared-record horizon |
| `SpinorCompleteness`, `MassiveVATrace` | On-shell projector/range and normalized-basis particle/antiparticle completeness; exact massive-muon V−A trace cancellation |
| `RootReferencePreparation` | Known actual-carrier seed to reference by one root; exact array preparation, source necessity and conditional minimum sitewise setup cost |
| `ReferenceSourceBoundary` | Invariant uniform mixture under closed unitaries; invariant coherent uniform vector under reconstructed involution-phase words; neither is a free prepared basis source |
| `NativeCarrierProtocol`, `NativeCarrierState` | Exact native permutation equal to the reference walk; finite register state space, causal/reversible/conservative evolution and distinct one-hot linear lift |
| `NativeReferenceBackground`, `FullCarrierIdentification` | Stationary reference classification, constrained-family minimum criterion and discrepancy conservation; spectral/fixed-mode guards on full-vacuum identification |
| `AmplitudeTrace` | Spin-summed squared Dirac-bilinear amplitude reduced to traces and the factor 64, under supplied on-shell external-state/vertex/basis hypotheses |
| `RootBranchEncoding`, `ActualRootRepair`, `RootPulseEvents` | Faithful actual-carrier branch and record encodings, root-implemented conservative repair, phase intertwining and distinct label/comparison event prices |
| `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle` | Concrete gamma coupling, constrained reference preparation, local unitary interface, complete named-operation schedule and exact finite-ring restoration horizon |
| `WalkRecordTransport` | Exact norm-preserving two-mode record channel in existing neighbour-pulse/coin factors; finite cyclic FIFO intertwining |
| `WallChiralCurrent`, `WallExchange`, `VATrace` | Dirac-product chirality, zero-kernel current projector, parity-combined wall/link covariance and V−A trace algebra |
| `RecordTransport` | Unitary finite record flow, repeated repair up to capacity, exact history retention and circuit-independent linear memory bound |
| `CoherentRefresh` | Executable addressed repair; once-only minimum coverage and two-schedule partition under explicit task/price hypotheses |
| `CarrierReferenceCycle` | Closed carrier/43-phase reference cycle, repeated operation and conditional minimum root-component work |
| `CarrierProbe`, `ClockControlledRoot` | Necessary interaction for an operational bit readout, reversible writable-phase probe, and clock-conditioned E8 norm/glue/root-step checks |
| `MatchedLatticeProbe` | Reversible readout of Paper I's exact modulo-two pairing, retained substrate probe, and the root's two-coordinate readout formula |
| `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit` | Independent-clock read/undo schedule, explicit product-gate limitation, and Paper I vertex-based parity circuit with exact transition accounting |
| `InBandRootReadout` | Actual E8 parity accumulator; minimal-shell/clean-record unit coupling; nearest-neighbour read/undo event cost for a supplied law |
| `Dirac`, `DomainWall*`, `DetuningMass`, `Concrete*`, `SignedSpectrum`, `EnergyCounts` | Chosen fermion Hamiltonian and complete signed energy counts |
| `LocalUnitary`, `Split*`, `PropagationBounds`, `WilsonSplit`, `Vacuum*` | Local finite-lattice dynamics, first derivative, vacuum preservation and origin fixed space |
| `IterationError`, `MatrixEvolutionSlope`, `VacuumIteration`, `PathError`, `VacuumErrorRate` | Contraction stability, many-tick convergence and an explicit momentum-independent C T²/N error bound for the corrected split |
| `SplitGap`, `CompactSplitGap` | Inverse-generator tick test and stationary-mode exclusion, pointwise and uniformly on compact momentum regions avoiding zero |
| `RotationAlgebra`, `VacuumTangent`, `VacuumPrincipal` | Actual finite-tick vacuum momentum derivative, its coercive square, normalized limit and exact π/10 first-direction degeneracy |
| `VacuumSchur`, `VacuumRay`, `EllipticLocal`, `VacuumDifferential`, `VacuumLocalGap` | Exact complementary-sector elimination and nonlinear near-origin exclusion uniform in momentum direction at each fixed admissible tick |
| `NormalizedIncrement`, `NormalizedSchur`, `JointVacuumGap`, `GlobalTickInterval` | Joint analytic extension through zero tick, a shared near-origin neighborhood and fixed-space equivalence over the whole momentum cell for one positive tick interval |
| `Survival`, `Governor`, `Potential`, `Operators`, `DiscreteEvolution`, `Doubling`, `TwinTests`, `WalkSpeed`, `AppendixChecks` | Conditional models, walk tests, limitations and counterexamples |
| `ChargedCurrent`, `NeutralCurrent` | Charged and neutral current algebra for explicit generator/charge conventions |
| `ComparisonFactorization`, `BranchGateBoundary`, `BranchMixerSynthesis`, `BranchPulseContract` | Controlled-operation factorization, exact fractional-exchange pulse circuit, admissibility/cost contract and the limitation of permutation/diagonal gate words |
| `FiniteRestorationBridge`, `RecordFeedbackBoundary` | Finite restoration to linear gain under a spanning update encoding; E8 memory-feedback and nonlinear encoding boundaries |
| `RunningCoefficients`, `ContactMatching` | Conditional running coefficients and low-momentum mediator matching |
| `REVIEW-AND-NEXT.md`, `FOUNDATION-PLACEMENT.md` | Current open obligations, dependency order and cross-paper ownership |

Module names in this table are under `PMAction/`. Paper III retains its W/Z, reference-sector,
resource-assignment and constant specializations. Its former general theorem names remain
available through thin compatibility modules; proofs now live here without a reverse dependency.

## Build and audit

Lean 4.34.1. Mathlib is pinned through sibling `PM-1-Arch/lean`; the framework is sibling
`PM/lean`. Keep the paper directories as siblings and run:

```sh
source ~/.elan/env
./check.sh
```

`PM_ACTION_LAKE_BIN` may name a specific installed lake executable. No new installation is needed.
`check.sh` builds the default imports, audits every PMAction declaration and its transitive axioms,
and checks that Paper II imports no Paper III–VI modules. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Unimported research files are outside that default coverage.

Latest full run (2026-10-30): 3764 build jobs, 4002 strict-audited declarations; dependency audit passed.

See [VERIFICATION.md](VERIFICATION.md) for the latest completed run and exact scope. See
[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) for genuine unfinished work. Build/audit success establishes
proof correctness under the stated hypotheses, not a completed derivation of all physical inputs.

[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) gives the high-level dependency map and the physical
questions behind it. The first repeatable carrier/reference construction and its limits are in
[CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md).

## Charged-current vertex normalization

`ChargedCurrent`: `g(W₁T₁ + W₂T₂) = (g/√2)(W⁺T₊ + W⁻T₋)` with unit-entry `T±` (`charged_decomposition`,
`raising_entries`); for any involution `Γ`, `(1 − Γ)/2` is a projector (`projector_idempotent`) and
`(g/√2)·(1 − Γ)/2 = (g/(2√2))(1 − Γ)` (`vertex_coefficient`), the coupling `ContactMatching` squares.
Inputs: the doublet generator/field normalization, the current interaction, and the
identification of `Γ` with the carriers' physical chirality.

## The comparison controller factors through a branch mixer

`ComparisonFactorization`: `compare U = branchInverse · ctrl U · branchChange` and, with the unitary
mixer `had = branchChange/√2`, `compare U = had · ctrl U · had` (`compare_factor`,
`compare_hadamard`), where `ctrl U = diag(1, U)` (the Hadamard test). Both factors are unitary
(`had_unitary`, `ctrl_unitary`), and for a permutation `U`, such as a root reflection, `ctrl U` is a
permutation (`ctrl_permutation`). The only non-permutation resource is one two-level branch mixer,
used twice.

The factorization does not supply the mixer's physical origin, locality, preparation or price.
`BranchGateBoundary.word_ne_mixer` proves that finite products of permutations and diagonal
phases in this basis cannot implement it. A supplied coherent weak rotation is outside that
restricted gate family and needs an admissibility and cost construction.

## Neutral-current normalization

`NeutralCurrent.decomposition` proves the photon/Z decomposition in any real module,
including complex carrier matrices. With `r = √(g²+g'²) > 0`, `c = g/r`, `s = g'/r`,
`W₃ = c Z + s A`, `B = −s Z + c A` and **`Q = T₃ + Yh`**, the current is
`e A Q + r Z (T₃ − s² Q)`, where `Yh` is **half** hypercharge and `e = gg'/r`.
`rotation_norm` proves the rotation preserves squared field norm; `mass_combination`
proves `g W₃ − g' B = r Z`. The representation and its reference-derived mass form stay
in Paper III; this algebra neither chooses them nor selects the mixing angle numerically.

[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) distinguishes proved constructions from the
remaining shared physical obligations and downstream applications.

## Shared operational constructions

The finite-to-linear and differentiable restorer implications, explicit coherent reset,
once-only execution coverage and comparison pulse circuit are already proved. Their exact
hypotheses and countermodels are in [OPERATIONAL-BRIDGES.md](OPERATIONAL-BRIDGES.md).
A reference gain trace is not automatically a physical per-phase work budget.

| Topic | Detailed result and boundary |
| --- | --- |
| Actual carriers, event law and common response | [CARRIER-EVENT-RESPONSE.md](CARRIER-EVENT-RESPONSE.md) |
| Repeatable root/clock cycle | [CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md) |
| Matched probe, clock control and in-band parity | [OPERATIONAL-READOUT.md](OPERATIONAL-READOUT.md), [COMPLETION-BARRIER.md](COMPLETION-BARRIER.md) |
| Finite coherent FIFO, exact history retention and capacity | [RECORD-TRANSPORT.md](RECORD-TRANSPORT.md) |
| Conservative reset response, preparation norms and event-ledger distinction | [RESTORATION-RESPONSE.md](RESTORATION-RESPONSE.md) |
| Walk-factor channel and zero-kernel chirality | [WALK-RECORD-TRANSPORT.md](WALK-RECORD-TRANSPORT.md) |
| Prepared coupling, finite ring and named-operation schedule | [WALK-REFERENCE-PROTOCOL.md](WALK-REFERENCE-PROTOCOL.md) |
| Gauge payload extension, local links and accounted open source | [GAUGE-RENEWAL-BOUNDARY.md](GAUGE-RENEWAL-BOUNDARY.md) |
| Actual-root logarithmic generator and coherent quarter preparation | [ROOT-TRANSFER-RECONSTRUCTION.md](ROOT-TRANSFER-RECONSTRUCTION.md) |
| Consolidated Hamiltonian spectrum and corrected local split | [SPECTRUM-AND-LOCALITY.md](SPECTRUM-AND-LOCALITY.md) |

## Wall parity and decay trace

`WallExchange.exchange_conjugates` proves `P H_Y(k) P = H_{Yᴴ}(-k)` for its stated
flavour-link Hamiltonian. `exchange_symmetry_iff` makes covariance with the same Y
equivalent to Y being Hermitian. A plain wall swap still fails. Identical D₄ sectors
do not alone establish vacuum-update covariance, low-energy mass identification or
positive mass spectrum. Paper III supplies its application hypotheses. `SplitCovariance` now supplies the sine-momentum specialization and exact
ordered finite-tick covariance for the flavour-free model. `ReferenceWalkParity`
supplies the separate reference-stream covariance. General flavour-link physical
identification remains open.

`VATrace.g_eq` identifies the written gammas with `WallChiralCurrent.diracGamma`;
`L_eq` identifies the chiral factor. `tr4_closed`, `contraction`, `projector_twice`
and `double_contraction` prove the exact V−A trace algebra. `muon_amplitude` gives
128 times the scalar product expression before the specified two-spin average and
64 afterward. This derives the numerical factor of the stated trace expression.
`SpinorCompleteness` now proves the on-shell projector/range identities and complete
particle/antiparticle spin sums for any normalized orthonormal basis of the solution
kernel. Existence of such a basis is not constructed in that module. The canonical
proof is in II; its original research path is a compatibility import.

`MassiveVATrace` proves `L gamma^nu L=0`, so the massive muon spin-sum term cancels
exactly in the chiral trace and the audited factor 64 is unchanged. No massless-muon
approximation is used. `AmplitudeTrace`, reviewed from Claude's isolated proof, now derives the spin-summed
squared Dirac-bilinear amplitude, including its conjugation/order, coupling square and
two-spin average, and obtains `64 G²(p·kbar)(pe·k)`. Its hypotheses include the stated
V−A vertex, real coupling and masses, positive-energy on-shell momenta, massless electron
and outgoing neutrino, and normalized complete kernel bases. The physical substrate
identification of that interaction, current/propagator, external states, statistics and
phase-space measure remain additional obligations. The canonical source is now in II;
the original research path remains a compatibility import.
Paper V can consume these upstream theorems without an import in the reverse direction.

See [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) for the dependency-ordered work remaining.


## Eigenstate energy bridge

`DiracEnergy` now derives the real eigenvalue shell and its nonnegative square-root
branch from the existing Clifford Hamiltonian, and proves existence of positive-
branch states in the concrete four-component model. See [DIRAC-ENERGY.md](DIRAC-ENERGY.md).
This supports Paper IV's controlled propagation phases without selecting physical
neutrino masses or identifying the full finite-tick wall dispersion with that model.
