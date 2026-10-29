# Paper II: the work in dependency order

Latest pass: [COMPLETION-BARRIER.md](COMPLETION-BARRIER.md). An actual E8 reflection now
implements the classical readout using an in-band coordinate parity, with elementary read/undo
cost on the prepared minimal shell. The remaining physical barrier is required execution,
coherent comparison/mixing and the transfer-to-event map. The independent-clock and three-leg
circuit routes remain useful checked alternatives, not selected vacuum dynamics.

Latest operational step: [OPERATIONAL-READOUT.md](OPERATIONAL-READOUT.md). The current cycle's
clock alone cannot read its carrier. A nonconstant readout requires coupling, but can leave
the carrier fixed. Clock-controlled roots now preserve the actual E8 form/glue and have
root-length carrier steps; full physical gate/readout selection and prices remain open.

The central target is one state/update/event-cost model whose consequences can be used by every
later paper. Existing spectral, carrier and response results are foundations for that model.
They do not yet identify one selected microscopic dynamics.

| Stage | What has to be established | What it unlocks |
| --- | --- | --- |
| 1. State and repeatable update | Where reference/payload information lives; a reversible local update; retained distinctions and finite memory across cycles | A physical persistence protocol rather than fresh-record repairs |
| 2. Operations and required work | Admissible clock, controlled carrier operations, coherent mixer and preparation; which jobs are required; primitive prices | Controller implementation; Paper III workloads and Paper V protocol costs |
| 3. Action and currents | One event-to-response map, kinetic normalization, charged-current vertex and scalar link | A common effective Lagrangian and physical mediator matching |
| 4. Error and continuum control | Nonzero-momentum split spectrum, many-tick errors, varying fields and non-Abelian remainders | A controlled effective theory, with its approximation regime stated |
| 5. Running and applications | Spin/orbital loop response, statistics, measure and thresholds | Derived running inputs for later constants and decay calculations |

Gravity, apparatus measurement and physical flavour selection are additional constructions;
finishing the finite matrix algebra does not settle them.

## The first concrete construction

`CarrierReferenceCycle` uses an actual eight-state D4 glue class and a supplied 43-phase clock.
It stores the conserved reference label as a correlation between carrier and phase. A phase
program makes a root-reflection excursion and returns it before the clock closes. The cycle
is a permutation on all 344 states and can repeat indefinitely without fresh clean records.

The first new constraint is also useful: a non-idle excursion must have at least two boundaries.
At positive root toll, minimum root-component cost selects two boundaries, but not their placement
or separation. The carrier root cost is one toll per cycle on a uniform ensemble; the 43 clock
advances have a separate supplied price. This is not a price for the complete apparatus.

For a single fixed reference, the count is two carrier changes or zero; one toll is the supplied
uniform-ensemble mean. This model preserves the reference instead of mixing through carrier
labels, so a physical law selecting that mean remains a separate obligation.

This closes a finite-memory *existence test*, not Stage 1's whole physical contract. The clock
register, its phase-dependent control and its coupling to carriers are supplied, and the update
does not yet act on the spatial lattice. The coherent mixer is still absent.

## The questions that matter physically

- **What must remain distinguishable?** A carrier label, a relative phase, an address, and a field
  configuration are different maintained objects. Their upkeep need not be the same task.
- **What disturbance is required?** Reversibility allows an idle carrier cycle too. A physical
  workload must follow from the actual update and conserved data, rather than be inserted so
  minimizing its cost gives a desired coefficient.
- **Where is the reference?** It may be an independent register or a recoverable correlation.
  The new construction realizes the latter. An operational readout must identify which is used.
- **Which events are allowed and paid for?** A carrier reflection is tied to an E8 root; its
  phase-controlled implementation and clock advance still need an admissibility/locality law.
  A whole circuit application is not automatically one E8 event.
- **Where does coherent mixing come from?** A permutation preserves amplitude norms after
  linearization but cannot by itself create the half-amplitude comparison from a basis state.
  The reconstructed statistical evolution and deterministic update need an actual common model.

The guiding use of persistence is to require retained distinctions and bounded repeatable
resources. Economy then minimizes a derived task within a justified feasible family. When
several different tasks persist, an additional substrate constraint is still needed to choose
between them.

See [CARRIER-REFERENCE-CYCLE.md](CARRIER-REFERENCE-CYCLE.md) for the exact construction and limits;
[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) tracks the full remaining program.
