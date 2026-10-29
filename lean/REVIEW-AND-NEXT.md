# Paper II: current review and completion order

Current stopping point: [COMPLETION-BARRIER.md](COMPLETION-BARRIER.md). The strongest new
implementation is now `InBandRootReadout`: the actual E8 reflection writes the matched
pairing into coordinate 2's parity. E8 positivity/evenness force 0-or-unit coupling on a clean,
minimal-norm shell, giving elementary read/undo event accounting. Required execution and the
coherent comparison/transfer/preparation bridge remain open. The five-stage status and the
other circuit routes are recorded in that note; no coupling formula has been changed.

Reviewed 2026-10-29 against the theorem statements and the Paper III dependency chain.
This replaces the accumulated progress list.
The README is the current result/premise/layout guide, rather than a chronology.

## What is already done

The older lists still called several completed tasks open. Do not redo them:

- Full concrete Hermitian representation, squared and signed spectra, branch multiplicities,
  four-dimensional zero kernel, all-momentum Hamiltonian zero exclusion and energy bandwidth.
- A unitary finite-range split update, 27-site input bound, correct first derivative, and a
  corrected ordering preserving the known vacuum modes exactly.
- Actual carrier/E8 root-operation connection, event accounting and controlled common
  gauge/scalar/fermion comparison response.
- Constant-Abelian triangle continuum limit with a quantitative error bound.
- Contact-limit cancellation and running-coefficient arithmetic under supplied physical inputs.

Previously completed in Paper III and now owned by II:

- Automatic Hermitian spectral transport, positive radius and quartic response bound;
  equality with the ordinary exponential and fixed-generator group/reversal laws.
- Coherent comparison, exact valid-input repair, reset/permutation restrictions, explicit
  lifted controller Hamiltonian and its response/trace identities.
- Generic minimum-refresh schedules and reversible retained-record maintenance tasks.

New proof work in this pass:

- `FixedSpace.exponential_fixed_iff` promotes the scalar alias argument to the full vector space.
- `VacuumFixedSpace` applies the actual bandwidth to the concrete Wilson exponential and proves
  the corrected split update's **complete** origin fixed space for 0 < |tau| <= 1/2.
- `Main.hermitian_action_response` presents the shared constructed dynamics/readout result with
  explicit hypotheses. This is not an implication from the unaugmented PM postulates.

## What genuinely remains, in useful dependency order

1. **One physical state/update contract.** Identify the actual carrier/register/reference and
   retained-record states, allowed local operations and conserved observables. Relate these to
   the specified spatial walk. Generic reversible bit repairs do not identify their bits with
   carrier amplitudes. A finite clean-record reservoir cannot be silently renewed for free.
2. **Primitive implementation and required work.** Supply the comparison branch, admissible
   coherent mixer, controlled evolution and preparation, with locality and actual event counts.
   The controller identities prove correctness, not these resources or a repair price. Derive
   which distinctions/fields each sector must maintain. This unlocks Paper III's gauge workload
   and stiffness map and Paper V's protocol costs.
3. **Action/current normalization.** Connect that event model to the common link/loop response
   and scalar/fermion kinetic terms. A shared toll or repair length in a cost definition is not
   a proof that the sectors use the same physical process. Construct the charged-current vertex
   before interpreting `ContactMatching` as a derived Fermi interaction. Paper III keeps the
   representation-specific mass form and electroweak resource assignments.
4. **Controlled dynamics and continuum.** For the *nonzero-momentum split product*, exclude extra
   unit eigenphases in a proved admissible tick interval or revise the candidate. The exact
   exponential result cannot settle that product. Complete many-tick error estimates, varying
   Abelian-field flux errors and non-Abelian/path-order estimates. The old diagnostic near
   tau=0.5 is numerical evidence to investigate, not a Lean counterexample or global theorem.
5. **Running from the action.** Derive the spin response `(2s)^2` and orbital `1/3`, including
   statistics, measure and regulator, before the standard one-loop arithmetic is claimed as
   substrate-derived. Averaging over three spatial directions alone does not derive a loop
   coefficient. Thresholds and scale matching must be physically specified; Paper III applies
   them to its content and constants.
6. **Separate larger branches.** Physical generation/chirality selection, flavour dynamics,
   scalar scale/corrections, gravity and apparatus measurement remain constructions. They do
   not follow from signed matrix roots or from a finite lattice merely existing.

## What stays in later papers

Paper III: the actual packet gauge representation, reference stabilizer and mass entries,
weak/colour/hypercharge task scopes, eta interpretation, workload tables, matching scales,
scalar/VEV inputs and numerical constants. Its `MatterRunning` applies Paper II's conditional
rule to supplied physical content. Papers IV–VI keep their flavour, decay and cosmology models.
General dynamics should be lowered only when independent of those interpretations; this pass
keeps the old Paper III theorem names as compatibility exports. See
[FOUNDATION-PLACEMENT.md](FOUNDATION-PLACEMENT.md).

## Recommended next construction

The next operational test is now checked in `CarrierProbe` and `ClockControlledRoot`.
`MatchedLatticeProbe` also implements the exact modulo-two E8 pairing used in Paper I,
with both input and substrate probe retained. For the selected root, its output depends
only on two neighbouring Gram coordinates modulo two. Physical coupling and timing remain
inputs; this is coordinate/readout locality rather than spatial propagation.
Readability as a capability does not specify an execution rate. A nonconstant probe readout
requires coupling; the old cycle's phase-only history is blind to its carrier. A reversible
readout can leave the carrier stationary, so a root excursion is not forced by that finite
readout task alone. The clock-controlled root has a reversible E8 norm/glue-preserving lift
and root-length moving carrier steps. Required operational probing, an actual combined
register encoding, allowed causal gates and full prices remain to be derived. See
[OPERATIONAL-READOUT.md](OPERATIONAL-READOUT.md). The phase used as the new writable probe
cannot simultaneously be assumed to advance independently as an ideal clock.

`CarrierReferenceCycle` now supplies the first repeatability test: a reversible root-excursion
cycle on actual carriers and a supplied 43-phase clock, with conserved encoded reference, no
fresh records, exact repetition and a minimum non-idle root-component cost. Uniform sampling
and the clock/control contract are inputs; an idle cycle also persists. The physical reason
for a non-idle task, its spatial implementation, coherent mixer and full event prices remain
open. See [PROGRAM-OVERVIEW.md](PROGRAM-OVERVIEW.md) for the high-level dependency map and
[CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md) for the exact new boundary.

Work on the microscopic reference/controller event contract in Paper II, using the extracted
operator and record theorems as constraints. Paper III's `SectorCapabilities` already shows why
an action's moved-carrier count cannot by itself select the maintenance task: weak reaches every
axis on the whole packet but only the reference row in a reference-scoped task; relative
hypercharge phases involve fourteen carriers, including the sterile one, rather than all sixteen.
Derive the maintained objects and their prices before further constant arithmetic.

The fixed-space work is a separate bounded viability branch: the origin is now complete; the
nonzero-momentum product still needs analysis. See [VERIFICATION.md](VERIFICATION.md) for the
current build/audit checkpoint. The older [CROSS-PAPER-BRIDGE-REVIEW.md](CROSS-PAPER-BRIDGE-REVIEW.md)
is historical context; its declaration counts and completion list are superseded here.
