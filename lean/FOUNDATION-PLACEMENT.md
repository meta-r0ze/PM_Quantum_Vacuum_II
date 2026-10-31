# Ownership of shared Lean foundations

The dependency direction is `PMFramework / PMArch -> PMAction -> later papers`.
Paper II imports no later-paper module; `AuditDependencies.lean` checks the
default import closure. General theorems belong here when they do not depend on
a later paper's packet, constants, physical resource assignment or decay measure.

## Preserved downstream compatibility

These general constructions were extracted from Paper III. Its compatibility
exports remain intact; the housekeeping removed only Paper II's obsolete
research wrappers, not these downstream modules or theorem names.

| Canonical Paper II module | Paper III compatibility module | What remains in III |
| --- | --- | --- |
| `HermitianTransport` | `LinkSpectralResponse.HermitianTransport` | W/Z generator, mass form and link specialization |
| `LinkEvolution` | `LinkEvolution` | Mass-form specialization and W/Z imports |
| `CoherentComparisonRepair` | `CoherentComparisonRepair` | No duplicate generic proof |
| `ControllerHamiltonian` | `ControllerHamiltonian` | Physical packet/controller identification |
| `RefreshSchedule` | `MinimalRefresh` | Gauge resource sets and prices |
| `ReferenceMaintenance` | `ReferenceMaintenance` | Sector assignment and maintenance-ledger consequences |
| `ReferenceWalkParity` | `ReferenceWalkParity` | Physical sector/link interpretation |

Canonical names start with `PMAction`; former `PMNested` compatibility names
remain downstream. Declaration counts can change ownership without losing proof
coverage. Review both packages' checks when changing those interfaces.

## Foundations owned by Paper II

| Shared construction | Canonical modules | Application boundary |
| --- | --- | --- |
| Hermitian transport, exponential and response | `HermitianTransport`, `LinkEvolution`, `MainTheorem`, `ControllerHamiltonian` | Physical generator, comparison, admissibility and tariffs |
| Conservative restoration and finite memory | `FiniteRestorationBridge`, `DifferentialRestoration`, `CoherentComparisonRepair`, `RecordTransport`, `RestorationResponse` | Physical task and gain-to-required-work identification |
| Native carrier/reference protocol | `RootWalkEncoding`, `RootCarrierWalk`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `RootReferencePreparation` | Carrier allocation, prepared seed/background and physical clock/ledger |
| Actual carrier vacuum representation | `CarrierParity`, `CarrierWeyl`, `SubstrateWeylRoots`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `CarrierReadoutQuotient`, `StateIdentification` | Coordinate observation, phase admission, Hermitian completion and coupling choices |
| Locality tests | `RectangularEvolution`, `LocalIsometricDynamics`, `ExponentialLocality`, `NativeLocalityBoundary` | A finite-support full-label amplitude completion is constructed; physical admission, selection and primitive price remain |
| Continued record supply and readout | `RecordSupply`, `HomogeneousRouting`, `ReadoutAdditivity`, `ReferenceSampling`, `SummedReference` | Initial records/routing, exact-refresh task, additive event pricing and physical sampler |
| Conditional economy | `PersistenceSelection` | The survival/cost law orders choices; their physical cost and admissible set remain supplied |
| Fourier, dispersion and time limits | `RealSpaceFourier`, `SpatialContinuum`, `VacuumIteration`, `VacuumErrorRate`, `GlobalTickInterval`, `ProjectedEvolution`, `JointSpaceTime`, `DiracEnergy`, `WallDispersion` | Joint vacuum-sector evolution is proved under sufficient refinement; state occupation, physical clock/scales, masses and species remain inputs |
| Gauge/scalar transport and robustness | `VaryingFields`, `LinkConsistency`, `GaugeTransport`, `ScalarTransport` | Actual finite payload, smooth refinement, group/trace/price and integration limits |
| Fluctuations and running foundations | `RunningResponse`, `GaugeFluctuation`, `FluctuationPremises`, `FluctuationClosure`, `ContinuumFields`, `LandauDegeneracy`, `LatticeToContinuum` | Physical action/measure/regulator, concrete spectral completeness and downstream coupling specialization |
| Currents, chirality and spin sums | `ChargedCurrent`, `NeutralCurrent`, `WallChiralCurrent`, `ChiralityConvention`, `SpinorCompleteness`, `VATrace`, `MassiveVATrace`, `AmplitudeTrace`, `WeakVertex` | Physical current/mediator, state identification, statistics and decay phase space |

The research contributions above are canonical default imports. Their previous
Paper II research paths contained only import wrappers and have been removed.
No theorem implementation was deleted or moved during housekeeping.

## What stays downstream

Paper III's packet representations, selected references, resource ownership,
group factors and constants are applications. Paper IV's flavour matrices,
generation/mass selection and dressing interpretation remain there. Paper V's
phase-space integral and lifetime model remain there; Paper VI's cosmological
readout and calibration remain there. A generic kernel-basis or amplitude theorem
can support these applications without importing their interpretation upstream.

Unfinished downstream research is neither a default Paper II theorem nor a
reason to move a failing draft here. The current Paper II obligations are in
[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md), with precise model boundaries summarized
in [README.md](README.md).
