# Paper II: cross-paper bridge review and revised priority

Historical review (2026-10-28). The current result map and open tasks are in
[README.md](README.md) and [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md); module placement is in
[FOUNDATION-PLACEMENT.md](FOUNDATION-PLACEMENT.md). Counts and completion statements below
are the historical checkpoint, not the current verification status.

Review date: 2026-10-28. This is a source/dependency review, not a new physical
closure theorem. No Paper III or other companion-paper source was edited.
The latest completed Paper II Lean audit remains 506 declarations.

## What Paper II needs to accomplish

The central target is a dynamics and effective action from the supplied PM and
Paper I premises. Existence of a consistent chosen lattice walk is useful, but
is not selection of that walk or its physical carriers by those premises.

The recent fermion work has established an explicit Hermitian Hamiltonian,
its signed spectrum, a finite-range unitary implementation, and exact vacuum
preservation. It has not identified its eight complex components and cubic
spatial shifts with Paper I's actual D4 glue-class carrier states and geometry.
The D4 gauge-loop and cubic-walk calculations are not already a common
microscopic model. The scalar and statistical reconstruction have their own
stated premises. A single operational cost/current/normalization bridge is the
main unresolved connection.

## Existing results that can help

### Paper I and Paper III: actual local events and common primitive cost

PM-3-Nested/lean/PMNested/LocalMaintenance.lean embeds two binary sites at
actual E8 nearest neighbors, classifies reversible population-preserving
updates as identity or swap, and derives swap activation and cost. It imports
Paper I's Distinctions and NetCost, including expected_count_linear.
TransitionLedger.lean prices explicitly counted primitive events and shows why
one macro operation need not cost one event. The common primitive toll cancels
from ratios; relative event multiplicities and the event law do not.

This is the strongest existing starting point for connecting substrate,
operation and action. It is still a two-site binary model, not an identification
of the sixteen actual channel carriers or a selected global schedule.
Its invariant-ensemble counterexamples show that equal one-site occupancies and
local symmetries do not determine the joint activation probability.

### Paper III: gauge stiffness and representation normalization

GaugeStiffness.lean supplies the conditional chain

    refresh cost c0 * W * loop cost -> beta=c0 W -> g²=1/(2 beta).

It then derives mixing ratios and a common electric combination. The refresh
assignment and common normalization are explicit premises, not selected dynamics.
StiffnessIndices.lean adds representation indices; under the specified channel
inventory and charge premises, T2=T3=2 and TY=10/3. It proves the mixing formula
uses index-weighted workloads. Its parity result excludes reading a clock
contribution of 43 as 2 times an integer refresh count. Thus the counting unit
must be derived, not renamed to recover an allocation.
ColourChannels.lean proposes a coloured-channel workload, but explicitly leaves
the assignment of weak links to clock maintenance and colour links to payload
maintenance to be derived from the actual update.

These are concrete constraints for Paper II's gauge-action normalization. The
representation inventory and workload rules must remain exposed until derived.

### Paper III: one scalar link, gauge covariance and mass response

SectorLinks.lean relates endpoint charge differences to the Yukawa charge
conditions. LinkMass.lean computes |theta phi|² for a specified doublet generator
and vacuum direction, giving the charged term and (g W3-g' B)² neutral term.
GaugeSpectrum supplies its flat and massive directions. These are useful
structural pieces of a common scalar/gauge response, conditional on the chosen
representations and link penalty. They do not supply the scalar kinetic cost or
its absolute normalization from the primitive substrate events.

HermitianMass and SectorExchange add conditional constraints on inter-sector
mass links. Sector exchange, positivity and a physical identification of those
matrices still require their own premises. A positive scalar mass branch in
Paper II does not automatically prove positivity of every flavour Yukawa matrix.

RepairSpace and the scale/response modules provide downstream consistency tests.
They cannot be used to fit an extra coefficient and then call it a derivation.

### Paper IV: consistency tests for a common flavour space

CKMClosure.lean proves that a change between complete orthonormal mass bases is
unitary. A uniform amplitude dressing is incompatible with that closed basis
change, and a common rate factor cancels from normalized readouts. This can test
Paper II's eventual flavour/current construction. It does not derive that
construction, select the mixing angles or identify lattice triality as generations.

### Paper V: the operator and measure obligations are sharply identified

SubstrateBridge.lean derives the fifth-power exponent conditionally from kinetic,
four-field interaction and rate-scaling equations, and proves that positive E8
norm symmetry plus a root calibration does not select that exponent. This tells
Paper II which current, mediator, normalization and measure rules it must supply.
The proposed routing inventory and spin/charge interpretation in the prose are
not independent proofs of Paper II's missing carrier identification.

### Paper VI: downstream bookkeeping and information constraints

SubstrateLoad and InformationCapacity offer useful consistency and storage
constraints. The cosmological response law and physical geometry remain inputs.
They do not close the microscopic update/action bridge and should not be used
as independent derivations of the earlier chirality or carrier assumptions.

## Revised work order

1. Trace Paper I's actual glue-class carriers into an explicit local state and
   event model. Use the existing E8-neighbor/cost construction as a starting
   point, while exposing its binary-state and schedule assumptions.
2. Derive a common primitive-event ledger, conserved currents and loop/link
   costs in that model. Distinguish event multiplicity from representation index
   and from phase/clock workload.
3. Connect the gauge stiffness and scalar-link quadratic response to that same
   action, fixing relative normalization and testing the Paper III identities
   jointly. Either prove a selected microscopic realization or prove that the
   leading response is invariant across the admissible family.
4. Use the existing fermion walk as a bounded viability test. Finish useful
   spectral gates where they bear on admissibility, but do not let stencil
   refinements replace the carrier/action derivation.
5. Then extend controlled continuum estimates, current/mediator matching and
   multi-tick error control. Treat gravity and measurement as separate remaining
   constructions, not consequences of the completed matrix identities.

## Dependency discipline

Paper III's companion update now requires both Paper I and Paper II and imports
the event/readout/link-expansion modules. Preserve the dependency direction
PM1 -> PM2 -> PM3. Avoid a conceptual
loop in which II assumes III's physical identifications while III assumes II's
dynamics. General structural lemmas can be extracted to the proper earlier or
shared layer, with explicit hypotheses; numerical allocation conclusions should
remain downstream tests. Coordinate any such extraction before modifying the
Paper III files currently being worked on separately.

## Current finite-tick warning

An exploratory numerical search found an apparent extra unit eigenphase for
the corrected momentum update at tau=0.5, near k=(0.67456,-0.57138,0.65264).
This is not a Lean counterexample or a complete parameter-range result. It does
show that the old Hamiltonian tick bound cannot be promoted to a split-update
exclusion theorem. A smaller admissible range needs a proof, or the candidate
needs revision. No global no-extra-modes theorem was added in this review.
