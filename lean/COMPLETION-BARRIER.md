# Paper II: classical readout closure and the remaining physical barrier

This pass continued beyond the first abstract register models and found a direct E8 readout
implementation. It did not complete all five stages. The remaining barrier is the mandatory
readout schedule and the physical coherent-comparison/event map. No constant was fitted or changed.

## Selected implementation: use a lattice coordinate as the record

`InBandRootReadout` uses the existing E8 root reflection. It has the exact update

`z₂ -> z₀ + z₃ - z₂ = z₂ + pairing(z, root)`.

The other seven coordinates are unchanged. Consequently coordinate 2's parity is an in-band
accumulator: it is XORed with the exact modulo-two pairing in Paper I's self-readability
postulate. If that parity is initially zero, the new parity is the readout. The full map is
reversible, preserves E8 norm and glue, and its second application restores every coordinate.
`record_is_intrinsic` also proves that the accumulator's own bit is an actual substrate
pairing: the integral inverse Gram matrix supplies its probe. This certifies observability
at the matched resolution, not a free detector or a price for preparing that probe.
The existing clock-controlled root cycle schedules read/undo while its independent clock
advances and closes at 43. The record is reused, not replaced with a fresh one each cycle.

This is a physical lattice-coordinate implementation of this classical observable, rather
than an unimplemented abstract bit gate. The task treats coordinate 2 as record/workspace;
it does not preserve the full lattice vector during the read. It preserves the seven data
coordinates and restores the complete vector after undo. The clock/register assembly and
its preparation/control costs still require the full operational model.

## When a reflection really is one elementary displacement

For arbitrary input, the displacement has quadratic norm `2 * pairing(z,root)^2`.
An even nonzero pairing can move the state while producing a false parity output: the
explicit input `2e₀` has false output but displacement norm 8. A reflection call cannot
therefore always be charged as a single nearest-neighbour event or only on a true bit.

The useful stronger result comes from E8 itself. `minimum_nonzero_norm` proves the least
nonzero quadratic level is 2, using Paper I's positivity/evenness and a root witness.
`minimal_clean_unit_coupled` proves that norm 2 plus clean record parity forces the pairing
to be 0 or ±1. Positivity of `z ± root` excludes larger pairings; the clean record excludes
the extremal states ±root. Thus, in this prepared family:

- the root moves exactly when the observed bit is true;
- every move has norm-two displacement, the elementary E8 neighbour distance;
- the read and its undo have the same activation event;
- `expected_read_undo_cost` gives twice the supplied primitive toll times that event's mass,
  for any supplied input law, without independence of the two events.

This is conditional classical event accounting for an actual root operation. It is not a
claim that the vacuum occupies this prepared family, that its law is selected, or that the
quadratic level is a physical energy/mass gap. Clock, control and initial preparation are
not silently included. This bit is also not `CommonResponse.stateFlag`; no scalar repair
multiplicity or field-normalization factor is inferred by equating different tasks.

## Other routes checked along the way

`ScheduledReadout` supplies the alternative explicit architecture with independent input,
substrate probe, Boolean record and 43-phase clock. It reads at phase 1, uncomputes at phase
2, preserves both lattice registers, and returns every state at phase 43. Its idle schedule
has the same clock and the actual Gram matrix's static bit-readability, but performs no
operational readout (`readable_idle_witness`). This demonstrates the limited point that
static readability, norm preservation and clock closure do not themselves set an execution
rate. It is not an independence theorem for every PM postulate or possible dynamics.

`ReadoutGateBoundary` proves independent lattice-register and clock permutations cannot write
an independently stored Boolean record. The in-band construction bypasses that limitation:
the record is now a function of a lattice coordinate, and a root actually changes it. This
is why the theorem was scoped to its product encoding rather than stated as a global no-go.

`ParityReadoutCircuit` verifies a six-instruction implementation using Paper I's three-leg
interaction witness, addressed bit flips and a wire exchange. It retains the two input bits,
writes their parity into the third, and can be undone. It makes four changed-gate transitions
on every input, even when net state change is zero. Under a supplied common bit-gate toll its
cost is four tolls for every normalized law. This was a useful algebraic alternative and a
warning against pricing a macro operation by net change. It is not a minimal E8 price: its
wire encoding, gate admissibility and toll assignment were not derived. The direct root
readout is the stronger substrate implementation for the stated prepared family.

## The first remaining physical barrier

Two inputs are still missing, even after this classical implementation:

1. **Required execution.** Why must the vacuum perform which readout, at what frequency or
   latency, and with what prepared state law? Paper I's capability statement does not specify
   those dynamical obligations. Neither a non-idle mask nor uniform sampling may be selected
   merely because a downstream coefficient needs it.
2. **Coherent comparison.** These readout implementations are configuration permutations.
   The field-response controller has half-amplitude entries. The existing
   `CoherentComparisonRepair.root_comparison_not_permutation` excludes implementing it by
   a permutation on that basis alone. It does not exclude coherent encodings or prepared
   coherent ancillas; those resources and their physical origin/cost must be supplied.

Paper II's reconstruction theorem can construct phase evolution from a supplied symmetric,
injective statistical transfer. It does not select that transfer, identify it with these
root/clock events, or establish the physical preparation/mixer and its event ledger. That
bridge is where the current derivation stops. These inputs need derivation from the full
substrate/update theory or explicit physical postulates; assigning an unexplained multiplier
or charging a whole controller as one event would conceal them.

## Status of the five stages

| Stage | Current status |
| --- | --- |
| 1. State/update | Repeatable read/undo and an in-band E8 accumulator are constructed. The required vacuum schedule, preparation law and complete clock assembly remain open. |
| 2. Operations/costs | Actual classical root readout and elementary event counting on the prepared minimal shell are proved. **Remaining barrier:** coherent preparation/mixer, statistical-transfer link and full microscopic costs. |
| 3. Action/currents | Common response and contact identities remain conditional on that bridge and on the current/normalization map. |
| 4. Controlled limits | Exact-exponential and origin split fixed-space results hold. Nonzero-momentum split phases, many-tick errors and extended gauge limits are independent mathematical branches still available. |
| 5. Running | Coefficient arithmetic is checked; action/measure/statistics and spin/orbital response needed for their substrate derivation remain open. |

This is a stop at missing physical implications under the requested stopping rule, not a claim
that no further conditional mathematics can be done or that PM has no possible completion.

## Verification

The full `check.sh` passed: 3441 build jobs, 1184 strict-audited PMAction declarations and
the no-downstream-import dependency audit. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. Log: `/tmp/pm2-inband-completion-check.log`. No sorry, custom physical axioms
or native_decide were used in the new modules. No numerical formula or manuscript source changed.
