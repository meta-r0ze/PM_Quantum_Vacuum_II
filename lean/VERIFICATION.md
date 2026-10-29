# Paper II verification checkpoint — 2026-10-29

## Latest: scheduled and in-band E8 readout

Complete `check.sh` passed: 3441 build jobs and 1184 strict-audited PMAction declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The no-downstream-import
check passed. Log: `/tmp/pm2-inband-completion-check.log`.

New default modules: `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit`,
`InBandRootReadout`. The selected new component uses the actual E8 reflection to write
matched-pairing parity into coordinate 2. Its accumulator is itself an intrinsic substrate
pairing. Positivity/evenness prove unit coupling on a clean minimal-norm shell, giving
nearest-neighbour read/undo event accounting for a supplied law. Other prepared readout
models and a six-instruction parity circuit are also checked, with their explicit scopes.

The current physical stopping point and all five stage statuses are in
[COMPLETION-BARRIER.md](COMPLETION-BARRIER.md): required execution, full preparation/control
prices and the coherent-comparison/statistical-transfer bridge remain open. No downstream
source, manuscript or numerical constant changed in this pass. The minimum lattice norm
is not identified with a physical energy gap.


## Earlier: operational readout and matched lattice probe

Complete `check.sh` passed: 3415 build jobs and 991 strict-audited PMAction declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The no-downstream-import
dependency audit passed. Log: `/tmp/pm2-matched-operational-check.log`.

New default imports: `CarrierProbe`, `ClockControlledRoot`, `MatchedLatticeProbe`.
They prove necessary coupling for an operational readout; the old cycle's clock-only
readout obstruction; reversible probes preserving their inputs; exact correspondence
with Paper I's modulo-two E8 pairing; and E8 norm/glue/root-step checks for the clock-controlled
root family. The matched root probe reads the parity of two neighbouring Gram coordinates.
Operational execution rate, combined register encoding, causal physical implementation,
coherent mixing and prices remain application obligations. No numerical constant or
downstream source changed. See [OPERATIONAL-READOUT.md](OPERATIONAL-READOUT.md).

## Earlier: repeatable carrier/reference cycle

The complete `check.sh` passed with 3411 build jobs and 917 strict-audited PMAction
declarations. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The no-downstream-import dependency audit passed. Log: `/tmp/pm2-carrier-cycle-check.log`.

`CarrierReferenceCycle` is a default import. It proves exact repeatable 43-phase closure
and reference preservation on the actual carrier product, a single-conditional-root gate
form, phase-by-phase event matching, and minimum non-idle root-component cost. Clock prices,
phase control and uniform sampling are supplied. The pointwise count is two changes or zero;
the ensemble mean is not an individual-history time average. See
[CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md) for the precise physical boundary.
No downstream source, manuscript or numerical constant changed in this pass.

## Earlier foundation-extraction checkpoint

Complete `check.sh` passed after the foundation extraction and new fixed-space work:

- 3410 build jobs.
- 866 PMAction declarations passed the strict transitive axiom audit.
- Dependency audit passed: no Paper III–VI imports in the default Paper II closure.
- Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

Log: `/tmp/pm2-foundations-reorganization-check.log`.

New default-import foundations: `HermitianTransport`, `LinkEvolution`,
`CoherentComparisonRepair`, `ControllerHamiltonian`, `RefreshSchedule`, `ReferenceMaintenance`.
New proof modules: `FixedSpace`, `VacuumFixedSpace`, `MainTheorem`.

`FixedSpace` proves a full-vector exponential/kernel equivalence under a spectral phase bound.
`VacuumFixedSpace` supplies that bound for the concrete Wilson Hamiltonian and proves its exact
exponential has no nonzero fixed vector away from the origin. At the origin, the actual corrected
split update has precisely the old four-dimensional kernel for 0 < |tau| <= 1/2. No all-momentum
fixed-space theorem for the split product, physical update selection or primitive pricing theorem
is asserted.

The main theorem constructs a unitary evolution, comparison/repair and controlled response from
explicit finite Hermitian/amplitude hypotheses. Its satisfiability witness is mathematical, not a
physical-vacuum identification. See `README.md` and `REVIEW-AND-NEXT.md` for the input boundaries.

The complete Paper III compatibility check also passed after all six extractions: 4179 build
jobs, 159 independently audited general-rule declarations and 2904 strict-audited PMNested
declarations. Log: `/tmp/pm3-after-paper2-foundations-check.log`. Its lower project count reflects
proofs moving into PMAction, whose declarations are separately audited; their transitive axiom
dependencies remain checked in Paper III. Counts are not measurements of physical completeness.

No manuscript source or numerical formula was changed in this pass. Existing historical compiler
results do not constitute a new manuscript compile. No dependencies were installed.
