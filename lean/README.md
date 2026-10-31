# PM-2-Action: Lean formalization

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum II: Operational
Action and the Emergent Lagrangian*. This package supplies shared dynamics,
event accounting and action-response mathematics to the later papers.

## Main result and scope

`PMAction.Main.hermitian_action_response` in [MainTheorem.lean](PMAction/MainTheorem.lean)
packages a constructed response model. For a supplied finite Hermitian generator
H and normalized complex amplitude φ, its transport is unitary, its two-branch
comparison has a coherent inverse, and its response is

    (1 − Re⟨φ,Uφ⟩)/2 = ‖φ − Uφ‖²/4.

Within an explicit positive step radius, the squared displacement differs from
t²‖Hφ‖² by an explicitly bounded fourth-order remainder. `LinkEvolution` identifies
the spectral transport with exp(i t H); `Main.hypotheses_satisfiable` gives a finite
witness. These results do not select a physical generator, gauge representation,
state/readout contract or primitive implementation from persistence alone.

## Proof map

All module names below refer to canonical sources under `PMAction/`, imported by
[PMAction.lean](PMAction.lean). There are no separate research proof copies.

| Area | Canonical modules | Checked result and retained inputs |
| --- | --- | --- |
| History and transfer | `Survival`, `SelectedSampling`, `Reconstruction`, `PersistenceSelection` | Conditional history selection and transfer reconstruction; exp(−β cost), β>0 makes greatest survival equivalent to minimum cost. The cost functional and admissible choices remain inputs. |
| Action response | `Operators`, `CommonResponse`, `HermitianTransport`, `LinkExpansion`, `LinkEvolution`, `MainTheorem` | Hermitian evolution, comparison response and controlled quadratic expansion for the supplied generator/readout. |
| Comparison implementation | `ComparisonFactorization`, `BranchGateBoundary`, `BranchMixerSynthesis`, `BranchPulseContract`, `ControllerHamiltonian` | Exact Hadamard-test factorization and conditional pulse construction; permutations and diagonal phases alone cannot synthesize its branch mixer. Admission, locality and prices are separate. |
| Restoration and pricing | `FiniteRestorationBridge`, `DifferentialRestoration`, `FiniteLinearizationBoundary`, `CoherentComparisonRepair`, `RestorationResponse`, `EventAccounting`, `CarrierEvents`, `CarrierCost`, `RefreshSchedule` | Finite/differentiable bridges, conservative reset and minimum execution for specified jobs. Net response is not automatically accumulated primitive expenditure. |
| Carrier readout | `SubstrateReflection`, `CarrierReferenceCycle`, `CarrierProbe`, `ClockControlledRoot`, `MatchedLatticeProbe`, `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit`, `InBandRootReadout` | Actual-root events and conditional probes/readouts; an autonomous clock trace alone does not measure a nonconstant carrier bit. |
| Root reconstruction | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair` | Lazy statistical root transfer, logarithmic generator, quarter-phase preparation and carrier repair; label-change and comparison events have distinct probabilities. Transfer rate, real-time admission and tariffs remain inputs. |
| Finite reference protocol | `RecordTransport`, `WalkRecordTransport`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RootWalkEncoding`, `RootCarrierWalk`, `RootCarrierCycle` | Exact FIFO retention, sharp finite-memory horizon, coupling and full reference walk. No irreversible erasure or free fresh records is inferred. |
| Native states and sources | `RootReferencePreparation`, `ReferenceSourceBoundary`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `FullCarrierIdentification` | Known-seed conversion; native reversible configurations and distinct one-hot amplitude lift; stationary reference classification and conditional minimization; obstructions to full-space root/Clifford identifications. |
| Continuing record supply | `RecordSupply`, `HomogeneousRouting`, `OpenReferenceFlow`, `PrimitiveRecordBoundary` | Disturbances are exported into records. For the specified routing/clean-record contract, exact maintenance forever iff the backward orbit is open; finite substrates return. Homogeneous lattice routings are translations **under the explicit homogeneity hypothesis**. Initial clean records and this maintenance task are not general consequences of persistence. |
| Intrinsic vacuum representation | `CarrierParity`, `CarrierWeyl`, `SubstrateWeylRoots`, `OrthogonalRootPhase`, `OddCarrierPhase`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `RectangularEvolution`, `CarrierReadoutQuotient` | Coordinate-odd carrier representation, native generators, full Hamiltonian and exponential intertwining. Physical observations, admitted phases, class/wall allocation and cross-sector coupling remain choices. |
| Full-label observation and locality | `StateIdentification`, `LocalIsometricDynamics`, `ExponentialLocality`, `NativeLocalityBoundary` | Exact observation and two explicit full-label completions. The directional-exponential choice has tails; the on-site isometric/identity-complement choice is unitary with the original finite stencil, all-state readout and no added labels. Primitive admission/prices remain open. |
| Fermion spectrum and split | `Dirac`, `DomainWall`, `DetuningMass`, `DomainWallSpectrum`, `ConcreteFermion`, `ConcreteSpectrum`, `SignedSpectrum`, `EnergyCounts`, `WallDispersion`, `DiracEnergy`, `WallSeesaw`, `WallExchange` | Supplied two-wall Hamiltonian, signed branches, positive-state existence, link-dependent seesaw and parity-combined covariance. Representation, link, occupied branches and particle statistics are not selected. |
| Controlled propagation | `LocalUnitary`, `SplitUpdate`, `PropagationBounds`, `WilsonSplit`, `VacuumSplit`, `VacuumGenerator`, `VacuumUniform`, `GlobalTickInterval`, `VacuumIteration`, `VacuumErrorRate`, `RealSpaceFourier`, `SpatialContinuum`, `ProjectedEvolution`, `JointSpaceTime`, `SplitCovariance`, `ReferenceWalkParity` | Corrected local unitary split, global safe-tick existence, uniform time-refinement bound, actual torus Fourier/spectrum identification, branch dispersion and joint fixed-momentum vacuum-sector evolution. Physical refinement/clock selection, full field and interacting limits remain open. |
| Gauge and scalar transport | `D4Gauge`, `GaugeContinuum`, `VaryingFields`, `LinkConsistency`, `GaugeTransport`, `ReferenceSampling`, `SummedReference`, `ReadoutAdditivity`, `ScalarTransport` | Pointwise D₄ density limits, cubic-consistent link robustness, link extraction from a supplied linear hop, reference readout and scalar kinetic normalization. Smooth refinement, representations, sampling, exact-refresh and pricing contracts remain visible. |
| Gauge fluctuations and running | `RunningCoefficients`, `RunningResponse`, `GaugeFluctuation`, `FluctuationPremises`, `FluctuationClosure`, `ContinuumFields`, `LandauDegeneracy`, `LatticeToContinuum` | Spin/orbital kernel coefficients, gauge-fixed Hessian and Ward algebra, finite-dimensional ghost determinant power, concrete field identities, strip-centre density and pointwise lattice-to-continuum second variation. These do not establish a quantum continuum measure or an integrated lattice action limit. |
| Currents and decay foundations | `ChargedCurrent`, `NeutralCurrent`, `ContactMatching`, `WallChiralCurrent`, `ChiralityConvention`, `VATrace`, `MassiveVATrace`, `SpinorCompleteness`, `AmplitudeTrace`, `WeakVertex` | Charged/neutral normalization, wall-projector algebra, spin sums, bilinear-to-trace amplitude and factor 64, contact matching and kernel-basis existence. Physical interaction, mediator, external-state interpretation and phase-space measure remain application inputs. |

## Joint space/time evolution

`ProjectedEvolution.error` gives a stable unitary intertwining estimate, independent
of the ambient Hamiltonian norm. `JointSpaceTime` applies it to the actual corrected
split on the canonical zero-wall-kernel projector P. Write H_a for the Wilson
Hamiltonian at k=a p divided by a, and D(p) for its massless kinetic tangent. Then

    ‖U(a p, T/(a N))^N P − P exp(−i T D(p))‖
      ≤ C T² ‖P‖/(a² N) + |T| ‖H_a P − P D(p)‖,
    C = 2*VacuumErrorRate.speedBound².

The projected generator defect tends to zero as a→0. For fixed continuum momentum
and elapsed time, the actual split therefore converges whenever a→0 and
1/(a²N)→0. `explicit_limit` supplies a=1/(r+1), N=(r+1)³; `kernel_state_limit`
applies the limit to every fixed initial wall-kernel state. The four-coordinate
compression of D(p) is exactly the existing massless Clifford Hamiltonian.
No changing eigenbasis or fitted energy law is used. The refinement rule is a
sufficient supplied choice; this result does not select a physical clock or prove
a full real-space, interacting-field, integrated-action or quantum limit.

## Important interpretation boundaries

The corrected eight-component split is unitary with a 27-site spatial support
bound. One positive tick interval gives its stationary-space equivalence to the
Wilson Hamiltonian across the whole momentum cell; the endpoint is qualitative.
The repeated split has a momentum-independent C T²/N exponential error bound.
There are now two full-label carrier completions. The directional-exponential
completion has observable odd dynamics equal to the split, but has directional
tails. `LocalIsometricDynamics` constructs an alternative

    U_full = E U E† + (I − E E†),

with the on-site carrier isometry E. It is unitary on all labels, preserves the
same 27-site dependence bound, has exactly the spinor readout history for every
initial amplitude, and fixes invisible modes. Its response equals the coordinate
response; its fixed states are exactly fixed readouts plus invisible backgrounds.
It factors into the four separately lifted local split factors and needs no extra
labels or sites. These are matrix-level implementation/existence results, not a
primitive E8 gate decomposition, tariff or unique physical selection. See [SPECTRUM-AND-LOCALITY.md](SPECTRUM-AND-LOCALITY.md).

`StateIdentification` connects reference and spinor contrasts in one readout.
It does not supply an extra independent record copy, a substrate encoding of its
four-phase clock or their primitive price. `ChiralityConvention` proves that the
displayed first-wall reference is annihilated by the chosen charged projector;
the parity-exchanged reference is a nonzero zero mode retained by that projector.
Using it as the physical reference still requires attaching the physical current
and maintenance task. The convention identities do not establish that attachment.

`ReadoutAdditivity` proves that additive singleton flag pricing yields the summed
readout, and exact conservative refresh of r independent states requires at least
r record slots. `RecordSupply` supplies exact repair within its specified initial
record/routing model. Together these are conditional operational results, not a
selection of the physical refresh contract or event law by measured agreement.

The gauge limit uses skew-Hermitian connections, the stated differentiability and
global derivative bounds, and cubic per-edge consistency. Unitarity alone does
not imply that consistency or even a finite density limit; smoothness at each
spacing need not give one continuum limit. Group, trace and physical normalization
remain inputs. `LatticeToContinuum` proves a pointwise second-variation limit, not
the site-summed integral, and gauge fixing remains a separate construction.

The fluctuation results now include the spin-1 Hessian coefficient and finite
mode-truncated ghost determinant identity. `LandauDegeneracy` derives the strip
orbit-centre density b/(2π); Fourier completeness, the concrete L² ladder
realization and the counting convention are not constructed by that result.
A regulated quantum measure and its physical identification remain separate.

`SpinorCompleteness` proves particle/antiparticle spin sums for any complete
normalized kernel basis; `WeakVertex` also supplies orthonormal-basis existence
and the stated contact normalization. `AmplitudeTrace` derives
64 G²(p·kbar)(pe·k) from the specified V−A bilinears and spin average, with real
coupling/masses, positive-energy on-shell states and massless outgoing electron
and neutrino. The physical vertex, statistics and decay measure are not selected.

## Documentation and ownership

- [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md): remaining mathematical and physical obligations.
- [SPECTRUM-AND-LOCALITY.md](SPECTRUM-AND-LOCALITY.md): spectral, fixed-tick and propagation theorem map.
- [FOUNDATION-PLACEMENT.md](FOUNDATION-PLACEMENT.md): upstream/downstream ownership and compatibility exports.
- [VERIFICATION.md](VERIFICATION.md): current full build/audit and housekeeping record.

The old topic/progress notes and merged research entry points have been removed.
Canonical theorem names and downstream compatibility modules are unchanged.

## Build and audit

Lean 4.34.1; Mathlib is pinned through sibling `PM-1-Arch/lean`, and the framework
is sibling `PM/lean`. Keep these directories as siblings, then run:

```sh
source ~/.elan/env
./check.sh
```

`PM_ACTION_LAKE_BIN` can name a specific installed Lake executable. The checker
builds the default library, strictly audits project declarations and their
transitive axioms, and rejects Paper III–VI imports. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. A successful audit establishes
correctness under the stated hypotheses, not selection of all physical inputs.
The current run and its counts are recorded in [VERIFICATION.md](VERIFICATION.md).
