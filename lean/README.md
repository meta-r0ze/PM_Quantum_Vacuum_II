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

The concrete fermion branch also proves an eight-component Hermitian Wilson/domain-wall
Hamiltonian, its signed spectrum, and a finite-range unitary split update. New completion:
`VacuumFixedSpace.origin_fixed_coordinates` proves that, for 0 < |τ| ≤ 1/2, the corrected split
update at zero momentum has exactly the four expected free vacuum components. The exact
Hamiltonian exponential has no extra fixed vectors away from zero momentum in the stated
momentum cell (`exact_fixed_only_at_origin`). This last conclusion is not yet proved for the
nonzero-momentum split product.

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
| Chosen Clifford/Wilson matrices and split ordering | `ConcreteFermion` through `VacuumFixedSpace` | Signed spectrum, exact vacuum kernel, unitary 27-site propagation and first-order generator consistency |
| Constant Abelian triangle flux and cell-volume convention | `D4Gauge`, `GaugeContinuum` | Exact area tensor, remainder bound and Maxwell limit conditional on beta = 1/(2g²) |
| Quadratic occupancy/quartic potential ansatz | `Governor`, `Potential`, `Operators` | Conditional signs, minima and leading operator bookkeeping |
| Supplied spin/index rule and massive-current exchange coefficient | `RunningCoefficients`, `ContactMatching` | One-loop coefficient arithmetic and contact limit; G_F = 1/(√2 v²) under the mediator mass relation |

**Not derived inside Lean:** the physical update/representation selection, its identification
with the concrete spatial walk, the controller's branch preparation/local implementation and
primitive prices, a common physical normalization, the scalar kinetic/scale inputs, and the
spin/orbital loop responses. Squared-amplitude readout is an input, not a derived Born rule.
Gravity and apparatus measurement require additional constructions.

The spin formula in `RunningCoefficients` is a stated continuum input: its arithmetic is proved,
not a substrate derivation of 11/3. `ContactMatching` starts from a supplied vertex/propagator
coefficient. Its coupling cancellation does not derive that vertex.

## Layout

| Path | Contents |
| --- | --- |
| `PMAction/MainTheorem.lean` | Constructed dynamics/comparison/response theorem and satisfiable hypotheses |
| `Reconstruction`, `HermitianTransport`, `LinkEvolution`, `FixedSpace` | Statistical reconstruction, spectral transport, exponential and fixed-space analysis |
| `Protocol`, `Gauge`, `D4Gauge`, `GaugeContinuum` | Covariance, loop action, lattice geometry and controlled Abelian continuum limit |
| `CarrierEvents`, `SubstrateReflection`, `CarrierCost`, `EventAccounting`, `SelectedSampling` | Substrate carriers, actual root operation, sampling and event prices |
| `InterferenceReadout`, `CarrierResponse`, `CommonResponse`, `LinkExpansion`, `CoherentComparisonRepair`, `ControllerHamiltonian` | Shared readout, quadratic bounds, coherent repair and generator lift |
| `RefreshSchedule`, `ReferenceMaintenance` | Generic minimal-work schedules and reversible reference tasks |
| `CarrierReferenceCycle` | Closed carrier/43-phase reference cycle, repeated operation and conditional minimum root-component work |
| `CarrierProbe`, `ClockControlledRoot` | Necessary interaction for an operational bit readout, reversible writable-phase probe, and clock-conditioned E8 norm/glue/root-step checks |
| `MatchedLatticeProbe` | Reversible readout of Paper I's exact modulo-two pairing, retained substrate probe, and the root's two-coordinate readout formula |
| `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit` | Independent-clock read/undo schedule, explicit product-gate limitation, and Paper I vertex-based parity circuit with exact transition accounting |
| `InBandRootReadout` | Actual E8 parity accumulator; minimal-shell/clean-record unit coupling; nearest-neighbour read/undo event cost for a supplied law |
| `Dirac`, `DomainWall*`, `DetuningMass`, `Concrete*`, `SignedSpectrum`, `EnergyCounts` | Chosen fermion Hamiltonian and complete signed energy counts |
| `LocalUnitary`, `Split*`, `PropagationBounds`, `WilsonSplit`, `Vacuum*` | Local finite-lattice dynamics, first derivative, vacuum preservation and origin fixed space |
| `Survival`, `Governor`, `Potential`, `Operators`, `DiscreteEvolution`, `Doubling`, `TwinTests`, `WalkSpeed`, `AppendixChecks` | Conditional models, walk tests, limitations and counterexamples |
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

Latest full run (2026-10-29): 3441 build jobs, 1184 strict-audited declarations; dependency audit passed.

See [VERIFICATION.md](VERIFICATION.md) for the latest completed run and exact scope. See
[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) for genuine unfinished work. Build/audit success establishes
proof correctness under the stated hypotheses, not a completed derivation of all physical inputs.

[PROGRAM-OVERVIEW.md](PROGRAM-OVERVIEW.md) gives the high-level dependency map and the physical
questions behind it. The first repeatable carrier/reference construction and its limits are in
[CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md).
