# PMAction — open work (todo)

Checked mathematics and the module map are in [`OVERVIEW.md`](OVERVIEW.md). This
file is only what remains. Paper II builds clean; run `./check.sh` for current counts. Each item states the frontier: what is proved, and
the physical or mathematical input still missing. Nothing here is a missing Lean
*statement* hidden behind an extra hypothesis; each needs a model law or a new
construction.

## 1. Physical states and observations
Proved: native representation, dependent-sector observation (`SectorObservation`),
class bundle (`CarrierClassBundle`). Open: justify the complex-amplitude/coordinate
readout contract, carrier class and wall allocation; identify the other/even modes
and any many-particle state space or statistics. Equal dimensions and reversible
persistence do not select the physical state space.

## 2. Primitive admission and physical completion selection
Proved: `LocalIsometricDynamics` closes the finite-support existence gap (unitary
on all 16 labels, same finite stencil, four-factor schedule, all-state readout);
`CompletionSelection` gives a family-restricted identity-complement selection.
Open: derive admission/implementation of the local amplitude factors in the
microscopic E8 gate library and their prices; the directional-exponential completion
is not identified with the on-site one.

## 3. Reference, records and vacuum coexistence
Proved: `RegisterReference` gives a capacity-aware spatial model
(`16·|X| + |payload|·|record|` registers); `PersistentBackground` and
`ReversibleStationarity` bound stationary-preparation selection;
`HomogeneousRouting.forever_iff_open` classifies exact maintenance.
Open: a clean initial record supply (a source contract), the per-tick ledger of that
supply, and physical allocation/preparation of the reference/record banks.

## 4. Physical clock and event ledger
Proved: `RegisterSplit` constructs the four-phase schedule with exact phase/tick
readout; `ClockDynamics` is unitary on coherent clock amplitudes.
Open: relate this supplied schedule to the substrate clock and price setup,
controls, transport/source/export and maintenance. Four factor applications are not
four primitive E8 events; survival minimization orders a supplied cost but does not
determine it.

## 5. Microscopic gauge transport and smooth refinement
Proved: `CompositionalTransport` derives the transport ODE and classical limit from
conserving single-hop updates under subdivision + C² response; `NativePacketUpdate`
proves the contracts for the native E8 packet subsystem; `GeometricGauge`,
`ReciprocalReflection` give gauge/Gibbs/site-reflection positivity, and
`QuotientClosure.gibbs_quotient_invariant` closes the edge-identification case
(invariance descends to any measurable quotient compatible with the action).
Open: the microscopic E8 realization of the abstract hop, its physical readout and
price law, shared group/trace normalization across spacings, and the admission of
the coherent root-generator evolution as the substrate dynamics. For the packet
subsystem this reduces to two explicit inputs: the C² control one-forms and that
admission. Further quantum-Yang–Mills constructions (gauge-measure transfer matrix,
infinite volume, full O(4) restoration, renormalized continuum, mass gap) are out of
scope for this test; see the Yang–Mills scope note in [`OVERVIEW.md`](OVERVIEW.md). The redirected
PM-specific work is the native control/admission question here and the PM-4
structural items (global all-nonzero mixing, per-step maintenance).

## 6. Full field and integrated limits
Proved: `JointSpaceTime` gives the fixed-momentum joint limit (`a→0`, `1/(a²N)→0`),
`UniformGaugeAction`/`IntegratedGaugeAction`/`IntegratedScalarAction`/
`ClassicalYangMills`/`LatticeSiteAction` give site-sum-to-integral limits on a box
under explicit regularity; `LatticeToContinuum` is a pointwise Hessian-density limit.
Open: full real-space field/PDE mode–domain control, the integrated Hessian, the full
real-space fermion field, and interacting-field estimates.

## 7. Physical applications
Open: identify the weak current/mediator, statistics, normalization, measure and
regulator before reading the trace/running results as physical predictions. Gravity
and measurement need their own state/update/observable constructions; quantum
continuum and Lorentzian continuation are distinct obligations.

## Downstream boundary
Generic proofs do not move a downstream paper's physical identification with them.
Paper III owns packet representations and constants; Paper IV flavour/mass; Paper V
decay/phase-space; Paper VI cosmology. See [`OVERVIEW.md`](OVERVIEW.md).

## Verification

Run `./check.sh`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
