# Actual carriers, primitive events and a conditional common response

## New checked connection

CarrierEvents uses Paper I's actual doubled minimal vectors of the three
nontrivial D4 glue classes, with eight states each. Its finite encoding is
injective and includes every integer minimal vector. Coordinate permutations
act reversibly within each class. Reflection in e0-e1 is involutive and moves
four states, fixing four; uniform preparation gives activation probability 1/2.

SubstrateReflection realizes the same first-sector root operation as an actual
integral E8 root reflection. It preserves the E8 norm and four glue labels, and
its action intertwines through Paper I's D4⊕D4 embedding and even-sum coordinate
model. This establishes compatibility of the local root operation, not a full
carrier-to-spinor or global vacuum-dynamics identification.

CarrierCost prices the changed-state event with Paper I's NetCost theorem:

    expected changed-state cost = toll * (1 - Re Tr P / n)

for a permutation P of n uniformly prepared carrier labels. It also proves the
sixteen-state count for a pair of classes and injectivity of the combined actual
vectors when the classes differ. Eight distinct vectors in four coordinates
are not eight independent geometric vectors; geometric_vectors_not_independent
formalizes that distinction. A Hilbert space over labels is an additional lift.

EventAccounting generalizes the same finite-event accounting to weighted laws;
uniform weights recover Paper I's expectedCost exactly. Linearity never needs
independence and never chooses the event distribution.

## Readout and primitive repair accounting

InterferenceReadout compares transported and reference amplitudes. Under the
explicit squared-amplitude readout, the minus-port probability on basis a is
(1-Re U_aa)/2. Both binary outcomes are nonnegative and normalized. Uniform
preparation gives mean flag (1-Re Tr U/n)/2. For a scalar phase this is
(1-cos theta)/2. Ordinary occupation probabilities alone do not determine this
phase-sensitive event.

CarrierResponse prices m primitive repair events triggered by that flag:

    repair cost = toll*m/2 * (1-Re Tr U/n),
    W scalar-phase refreshes cost toll*m*W/2 * (1-cos theta).

All m events may share the same flag; no independence is assumed. A required
phase-independent comparison cost stays in the baseline. The excess over the
zero-phase reference, not the whole operating cost, has the cosine form.
The same counting coefficient feeds GaugeContinuum's controlled D4 limit:

    density -> toll*m*W*g²/4 * sum F².

This is a real operational derivation within a stated readout/repair contract.
It does not derive that contract from persistence. In particular a carrier
reflection changes a uniformly sampled label with probability 1/2, while its
coherent comparison flags with probability 1/4: the events cannot be exchanged
silently. Uniform preparation, a coherent reference, squared-amplitude readout,
repair length, physical refresh workload and representation normalization are
still inputs needing substrate justification.

## Companion additions reviewed and included

CommonResponse and LinkExpansion were supplied during the companion work and
are included in the complete Paper II build/audit. They extend the comparison
penalty to normalized amplitudes and neighboring scalar fields, and prove a
controlled fourth-order remainder for a unitary-eigenbasis link expansion.
The scalar quadratic cost then has a precise leading generator norm and error.

The common prefactor remains conditional on a common physical repair process;
a theorem using one m for all sectors does not prove that all sectors realize
that m. Unnormalized scalar field norms require a workload-density map rather
than a one-event probability interpretation. The positive transport-mismatch
form involving 2-U-U† is not alone a derivation of the first-order Dirac action
or fermionic statistics.

## Best next mainline proof

Derive how actual carrier operations represent the conserved currents and
which resources their gauge links must refresh. Connect the scalar field's
workload/normalization and fermionic carrier action to the same operational
readout, with explicit primitive counts. Paper III's RequirementTable and
EventStiffness are now downstream tests of these choices, not replacements for
their microscopic derivation. Preserve the package direction PM1 -> PM2 -> PM3.

## Verification

Complete check.sh passed: 3393 build jobs and 677 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound
are allowed. No sorry, native_decide or custom proof axioms were introduced.
The expanded manuscript compiled successfully with the actual bibliography.
This pass uses existing dependencies; no installation was needed.


Manuscript source checks found no missing labels or citation keys, and the
acknowledgments match the pre-cleanup backup byte-for-byte. Paper III now imports
this foundation directly; its reviewed full package also passes (1527 project
and 153 independent general declarations). The neutrino review is recorded in
PM-3-Nested/lean/NEUTRINO-TOWER-REVIEW.md; it does not alter the Paper II event law.
