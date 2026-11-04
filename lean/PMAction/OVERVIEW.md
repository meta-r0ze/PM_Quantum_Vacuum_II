# PMAction — overview of checked results

The single map of what Paper II proves and what later papers can reuse. Open work
is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Canonical sources are under `PMAction/`, imported by
`PMAction.lean`; there are no separate research copies. Theorem names are entry
points, not exhaustive lists. Lean source is the ground truth.

## Scope

Paper II builds on the Paper I substrate (E8, clock Δ = 43) and supplies generic
finite dynamics, register/current/schedule constructions, gauge and scalar
transport limits, current algebra, and their audit boundaries. It imports nothing
from Papers III–VI; each later paper owns its own physical application.

Main result: `PMAction.Main.hermitian_action_response` — for a supplied finite
Hermitian `H`, unitary transport of a normalized `φ`, with two-branch response
`(1 − Re⟨φ,Uφ⟩)/2 = ‖φ − Uφ‖²/4` and a bounded fourth-order remainder from
`t²‖Hφ‖²`. `LinkEvolution` identifies the spectral transport with `exp(i t H)`.

## Module map (what you can use)

| Area | Canonical modules | Checked result and retained inputs |
| --- | --- | --- |
| Discrete causal structure | `DiscreteCausal` | The causal preorder on `ℕ × X` induced by the update stencil `Reach` (≤27 sites/tick): `causal_refl`, `causal_trans`, `causal_one_tick`; `CausallyTrapped`; `zero_clock_not_horizon` (a capacity point is not trapped) | Continuum metric / Lorentzian comparison |
| Spatial metric | `SpatialResponse` | Diagonal optical metric `g_ij = n_i² δ_ij = δ_ij/c_i²` from the same capacity ledger; `spatialMetric_from_index`, `spatialMetric_isotropic` (isotropy from an axis-independent load) | The optical-metric reading; off-diagonal shear |
| Coulomb kernel | `CoulombKernel` | Green's-function interface `Kernel` with `lap_green` and `symm`; `pairEnergy`; concrete 2/3/4-site path kernels `green2/green3/green4` with `pathLap*_green*` (`lap G = δ`) | General path/cycle Green's function; Paper 3 charge source |
| Discrete response law | `ResponseLaw` | Laplacian on the actual axis-neighbour adjacency: `lap_const` (uniform load → no field), `lap_sum_zero` (antisymmetric double sum), `response_source_neutral` (a static source must sum to zero) | The source distribution; continuum limit |
| Gravitational weak field | `WeakField` | Capacity ledger `C=ν−K`, index `ν/C`, clock `C/ν`; the identification `g_00=−(1+2Φ)` for the paper's linearized pair and the exact clock-squared pair; `Φ=−K/ν+K²/(2ν²)`, strictly attractive | The response law selecting the readout; spatial metric, field equation, global causal structure |
| Conservation → continuity | `Continuity` | A conserved comoving charge gives density `N/a³` and `matter_continuity` (`aρ'+3ρ=0`); `matter_w`/`radiation_w`/`vacuum_w` (`w=0,1/3,−1`). | Which per-particle scaling holds; the expansion `a` |
| History and transfer | `Survival`, `SelectedSampling`, `Reconstruction`, `PersistenceSelection` | Conditional history selection and transfer reconstruction; `exp(−β cost)`, `β>0` makes greatest survival equivalent to minimum cost. Cost functional and admissible choices remain inputs. |
| Action response | `Operators`, `CommonResponse`, `HermitianTransport`, `LinkExpansion`, `LinkEvolution`, `MainTheorem` | Hermitian evolution, comparison response and controlled quadratic expansion for the supplied generator/readout. |
| Comparison implementation | `ComparisonFactorization`, `BranchGateBoundary`, `BranchMixerSynthesis`, `BranchPulseContract`, `ControllerHamiltonian` | Exact Hadamard-test factorization and conditional pulse construction; permutations and diagonal phases alone cannot synthesize the branch mixer. Admission, locality and prices are separate. |
| Restoration and pricing | `FiniteRestorationBridge`, `DifferentialRestoration`, `FiniteLinearizationBoundary`, `CoherentComparisonRepair`, `RestorationResponse`, `EventAccounting`, `CarrierEvents`, `CarrierCost`, `RefreshSchedule` | Finite/differentiable bridges, conservative reset and minimum execution for specified jobs. Net response is not automatically accumulated primitive expenditure. |
| Carrier readout | `SubstrateReflection`, `CarrierReferenceCycle`, `CarrierProbe`, `ClockControlledRoot`, `MatchedLatticeProbe`, `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit`, `InBandRootReadout` | Actual-root events and conditional probes/readouts; an autonomous clock trace alone does not measure a nonconstant carrier bit. |
| Root reconstruction | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair` | Lazy statistical root transfer, logarithmic generator, quarter-phase preparation and carrier repair; label-change and comparison events have distinct probabilities. |
| Finite reference protocol | `RecordTransport`, `WalkRecordTransport`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RootWalkEncoding`, `RootCarrierWalk`, `RootCarrierCycle` | Exact FIFO retention, sharp finite-memory horizon, coupling and full reference walk. No irreversible erasure or free fresh records inferred. |
| Native states and sources | `RootReferencePreparation`, `ReferenceSourceBoundary`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `FullCarrierIdentification` | Known-seed conversion; reversible native configurations and one-hot amplitude lift; stationary reference classification and conditional minimization; obstructions to full-space root/Clifford identifications. |
| Continuing record supply | `RecordSupply`, `HomogeneousRouting`, `OpenReferenceFlow`, `PrimitiveRecordBoundary` | Disturbances exported into records; for the specified routing/clean-record contract, exact maintenance forever iff the backward orbit is open; finite substrates return. Homogeneous routings are translations **under an explicit homogeneity hypothesis**. |
| Intrinsic vacuum representation | `CarrierParity`, `CarrierWeyl`, `SubstrateWeylRoots`, `OrthogonalRootPhase`, `OddCarrierPhase`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `RectangularEvolution`, `CarrierReadoutQuotient` | Coordinate-odd carrier representation, native generators, full Hamiltonian and exponential intertwining. Physical observations, admitted phases, class/wall allocation and cross-sector coupling remain choices. |
| Full-label observation and locality | `StateIdentification`, `LocalIsometricDynamics`, `ExponentialLocality`, `NativeLocalityBoundary` | Exact observation and two full-label completions. The directional-exponential choice has tails; the on-site isometric/identity-complement choice is unitary with the original finite stencil, all-state readout and no added labels. Primitive admission/prices remain open. |
| Fermion spectrum and split | `Dirac`, `DomainWall`, `DetuningMass`, `DomainWallSpectrum`, `ConcreteFermion`, `ConcreteSpectrum`, `SignedSpectrum`, `EnergyCounts`, `WallDispersion`, `DiracEnergy`, `WallSeesaw`, `WallExchange` | Supplied two-wall Hamiltonian, signed branches, positive-state existence, link-dependent seesaw and parity-combined covariance. Representation, link, occupied branches and statistics are not selected. |
| Controlled propagation | `LocalUnitary`, `SplitUpdate`, `PropagationBounds`, `WilsonSplit`, `VacuumSplit`, `VacuumGenerator`, `VacuumUniform`, `GlobalTickInterval`, `VacuumIteration`, `VacuumErrorRate`, `RealSpaceFourier`, `SpatialContinuum`, `ProjectedEvolution`, `JointSpaceTime`, `SplitCovariance`, `ReferenceWalkParity` | Corrected local unitary split, global safe-tick existence, uniform time-refinement bound, torus Fourier/spectrum identification, branch dispersion and joint fixed-momentum vacuum-sector evolution. Physical refinement/clock and full field/interacting limits remain open. |
| Gauge and scalar transport | `D4Gauge`, `GaugeContinuum`, `VaryingFields`, `LinkConsistency`, `GaugeTransport`, `ReferenceSampling`, `SummedReference`, `ReadoutAdditivity`, `ScalarTransport` | Pointwise D₄ density limits, cubic-consistent link robustness, link extraction from a supplied linear hop, reference readout and scalar kinetic normalization. |
| Gauge fluctuations and running | `RunningCoefficients`, `RunningResponse`, `GaugeFluctuation`, `FluctuationPremises`, `FluctuationClosure`, `ContinuumFields`, `LandauDegeneracy`, `LatticeToContinuum` | Spin/orbital kernel coefficients, gauge-fixed Hessian and Ward algebra, finite-dimensional ghost determinant power, concrete field identities, strip-centre density and pointwise lattice-to-continuum second variation. No quantum continuum measure or integrated lattice action limit. |
| Currents and decay foundations | `ChargedCurrent`, `NeutralCurrent`, `ContactMatching`, `WallChiralCurrent`, `ChiralityConvention`, `VATrace`, `MassiveVATrace`, `SpinorCompleteness`, `AmplitudeTrace`, `WeakVertex` | Charged/neutral normalization, su(2) doublet algebra (`T3`, `commutator_*`, `anticommutator_Tp_Tm`), V−A projector `P_L` (idempotent/Hermitian/rank two), wall-projector algebra, spin sums, bilinear-to-trace amplitude and factor 64, contact matching and kernel-basis existence. Physical interaction, mediator, external states and phase-space remain application inputs. |

## Shared state/controller and register layer

`FiniteEncoding` owns sparse label encodings, coherent isometry, pairing, recovery
and permutation/readout intertwining (Paper III reuses it). `SectorObservation`
combines dependent native sectors without identifying labels; `CarrierClassBundle`
applies it to all three glue classes (48 labels, 24 observed modes). `InvolutionComparison`
and `SpatialComparison` give exact comparison circuits for spectral phases of
involutions, with no independent branch marker.

`IndependentRegisters`, `TensorObservation`, `RegisterPrograms` construct two
disjoint Boolean register banks with exact tensor/composed readout;
`RegisterHamiltonian` lifts any supplied Hermitian generator to occupation-dependent
register hops with unitary evolution and conservation of occupation/payload bits.
`RegisterVacuum`, `RegisterInteraction`, `ChiralRegisterCurrent`, `ClockDynamics`,
`RegisterSplit`, `RegisterReference`, `RegisterControl` give the full native
generator/readout, both-bank interactions, chiral charge on the zero kernel and the
exchanged reference, the four-phase clock, and joint configuration controls.
`RegisterReference` counts `16·|X| + |payload|·|record|` Boolean registers; the clock
is separate. These are compatible finite constructions with **supplied** banks,
amplitudes, charge and admission; they do not select or prepare them.

`PersistenceSelection`, `PersistentBackground`, `CompletionSelection` give
family-restricted selection with the real admissible family; `ReversibleStationarity`
shows closed injective updates cannot finitely prepare a stationary state.

## Spectrum, split and locality (from the former SPECTRUM map)

- `ConcreteFermion` checks the Hermitian β/γ/α Clifford algebra and the concrete
  eight-component two-wall Hamiltonian; the zero-momentum kernel is `((u0,u1,0,0),(0,0,u2,u3))`.
- `DomainWallSpectrum` cancels cross terms: `(H²−(s+δ²)I)(H²−(s+δ²+1)I) = δ²I`.
  `ConcreteSpectrum`/`SignedSpectrum`/`EnergyCounts` give the characteristic
  polynomials and multiplicities; four kernel dimensions are **not** four species.
- `LocalUnitary`, `SplitUpdate`, `PropagationBounds`: unitary involutive
  nearest-neighbour factors, ≤27-site dependence per tick.
- `VacuumSplit`: corrected split `U(t)=onsite(Q(t))R₀R₁R₂` with exact zero-momentum
  `exp(−itW)`; `VacuumIteration`/`VacuumErrorRate` give a momentum-independent
  `C T²/N` bound; `SplitGap`/`GlobalTickInterval` give a safe tick interval (endpoint
  qualitative, physical tick not selected).
- `RealSpaceFourier`, `SpatialContinuum`, `JointSpaceTime`: exact torus update and
  momentum blocks, branch dispersion, and fixed-momentum joint limit
  (`a→0`, `1/(a²N)→0`; explicit family `a=1/(r+1)`, `N=(r+1)³` via `ProjectedEvolution`).
- `WallDispersion`, `DiracEnergy`, `WallSeesaw`, `WallExchange`, `SplitCovariance`:
  exact nonzero-link masses `m₊²+m₋²=y²+2δ²`, `m₊²m₋²=δ⁴`, positive eigenstates,
  multi-flavour seesaw, parity-combined covariance.
- `LocalIsometricDynamics`: the finite-stencil full-label completion
  `E U E† + I − E E†` (unitary on all labels, same readout, no extra labels).

## Gauge, Yang–Mills and limits

`GeometricGauge`, `ReciprocalLinks`, `ReciprocalReflection` give the geometric
configuration-space gauge action and Gibbs invariance, with one reciprocal-link
measure that is gauge invariant and site-reflection positive. `LatticeGibbs`,
`LatticeGibbsU1`, `UnitaryHaar` and `SpecialUnitaryHaar` give the finite-volume
Euclidean probability measures for `U(1)`, `U(N)` and `SU(N)` links.
`TransportExistence` constructs global unitary transport from a continuous skew
connection; `CompositionalTransport` derives the ODE and classical limit from
conserving single-hop updates; `NativePacketUpdate` proves those contracts for the
native E8 packet subsystem. `UniformGaugeAction`, `IntegratedGaugeAction`,
`IntegratedScalarAction`, `LatticeSiteAction`, `ClassicalYangMills` give the
site-sum-to-integral limits on a box under explicit regularity.
`QuotientClosure.gibbs_quotient_invariant` proves gauge invariance descends to any
measurable edge-identification quotient compatible with the action.

**Yang–Mills scope.** This branch is a test of persistence mechanics, not a
construction of Yang–Mills theory. Its deliverable is the classical continuum
limit plus the finite-volume Euclidean setup (Gibbs measure, gauge invariance,
site-reflection positivity). The Clay-level items — infinite volume, the
renormalized continuum, full O(4) restoration, Osterwalder–Schrader
reconstruction, the mass gap and nontriviality — are the general
quantum-Yang–Mills problem, not PM-specific consequences, and are out of scope
here. The remaining PM-specific inputs are the two `NativePacketUpdate`
controls/admission premises and the selection of group, representation and β.

## Interpretation boundaries (what is *not* selected)

Build success certifies the conditional statements, not physical identification.
Not selected by these theorems: the physical generator/representation, state/readout
contract, carrier/spinor/gauge identification, link/occupied branches and statistics,
bank/occupancy preparation, gate admission, clock calibration, primitive event
tariffs, the current/mediator and decay measure, and the quantum continuum measure /
Lorentzian limit. The V−A projector `P_L` and the su(2) doublet algebra are proved
algebra; attaching them to the physical weak interaction is a model input.

## Ownership / downstream boundary

Paper II supplies **generic** dynamics and imports no later paper. Paper III owns
packet representations, sector/resource ownership and constants; Paper IV owns
flavour/mass applications; Paper V owns decay/phase-space/lifetime; Paper VI owns
cosmology. Moving a generic proof upstream does not move an application's physical
identification assumptions. Paper IV's `WeakCurrentBridge` reuses
`WeakVertex.PL` and `VATrace.L_eq` to identify the native flavour-current chiral
projector with `P_L`; the flavour generator and mediator remain Paper IV inputs.

## Verification

Run `./check.sh`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
