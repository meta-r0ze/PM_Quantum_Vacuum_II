# Operational readout and clock-controlled roots

Stronger follow-up: `InBandRootReadout` uses coordinate 2's parity as the observer and the
actual E8 reflection as its write/undo operation. On the prepared minimal shell, unit coupling
and elementary event cost follow from E8 positivity/evenness. This bypasses the need for a
separately stored Boolean record in this particular task. See
[COMPLETION-BARRIER.md](COMPLETION-BARRIER.md) for the current result and remaining coherent bridge;
the writable-phase and separate-record models below remain distinct conditional constructions.

The next step is sharper than requiring a non-idle carrier excursion. Paper I's
`SelfReadable.BitReadable` states that suitable pairing probes exist at matched one-bit
resolution. It does not specify their dynamical schedule, apparatus or execution rate.
We cannot infer a per-cycle root workload from that capability alone.

## A readout requires interaction

`CarrierProbe.bit` tests whether doubled carrier coordinate 0 is smaller than coordinate 1.
It is nonconstant in each class and distinguishes each actively reflected carrier from its
reflected partner. This finite observable is not a proved identification with Paper I's
matched-resolution lattice pairing, nor a complete readout of all eight carrier labels.

`ReadsBit` requires a probe prepared at phase zero to output phase 0 or 1 according to the bit.
`readout_requires_coupling` proves that this output cannot be independent of the carrier.
`readout_requires_probe_motion` proves that some input must move the probe. A stipulated
operational readout therefore requires activity, but this does not require the vacuum to
execute it in each cycle or identify that activity with a root reflection.

The earlier reference cycle advances its clock independently of its carrier.
`cycle_phase_iterate` and `cycle_does_not_read` prove that no time in that clock-only history
reads the bit, even with non-idle excursions. Algebraic recovery of the reference from the
complete state is different from putting the reference into a probe record. A separate
observation of the carrier is not excluded by this theorem.

## Reversible readout with a stationary carrier

The constructed `probe` shifts its phase once when the bit is true, otherwise leaves it
unchanged, and always preserves the carrier. It is a permutation, reads the prepared bit,
and can be undone exactly on every state. Compute/undo can repeat without fresh records.
Its permutation matrix is unitary under the amplitude construction.

This is a supplied two-gate protocol, not an autonomous 43-tick update. During readout the
phase is a writable probe rather than an independently advancing clock. Retaining an ideal
clock requires another observing register or a different readout channel. Scheduling,
preparation, control and gate prices remain inputs. Undo leaves no retained probe record;
using or retaining the output needs the corresponding task/register and its cost. No
measurement rule, Born law or coherent comparison mixer is derived.

Within finite reversible register operations, the readout task thus admits a solution without
carrier motion. This is not a countermodel to all PM postulates: its physical admissibility
and its connection to the actual lattice probe still need proof.

## The clock-controlled E8 root

`MatchedLatticeProbe` now supplies the precise one-bit interface to Paper I: its outcome is
whether `2` divides the actual E8 pairing of an input lattice state and a retained substrate
probe state. Its reversible update preserves both lattice registers and writes that result
into a prepared writable phase. The probe state is included in the state, rather than treated
as an external source; its preparation, storage and implementation price are still unpriced.

The existing norm-two root is informative: it separates zero from a norm-two basis root.
Its pairing is `x₀ + x₃ − 2x₂`, so its one-bit output depends only on `x₀ + x₃` modulo two.
These are the root's two neighbours in the E8 Gram diagram. This proves coordinate/readout
locality, not physical spatial adjacency or a gate count. The writable phase still cannot
simultaneously be assumed to act as an independent ideal clock. No full embedding of all
three registers into the physical substrate or mandatory execution schedule is supplied.

`ClockControlledRoot` implements the phase-conditioned identity/root choice on the integral
E8 lattice. It proves reversibility, preservation of norm and glue code, the mask-conjugacy
and exact 43-tick closure. The same phase control commutes with the existing D4-to-E8
embedding calculation and agrees with the carrier cycle's gate condition.

`moving_step_is_root` additionally proves that each moving minimal-carrier displacement,
after undoing the doubled-coordinate convention, is an integral norm-two D4 root. Integer
division loses no part of that displacement. This is internal carrier geometry, not spatial
finite propagation for arbitrary E8 positions.

These are phase-dependent lattice isometries. A physical encoding of the combined clock and
carrier registers into one substrate state, causal gate implementation and hardware prices
are still required; no single phase-independent E8 symmetry of that encoding is asserted.

## Next obligation

Connect a required operational readout to the substrate's actual probe and allowed local
operations. Identify the register receiving its result while the clock does its own job,
derive the coupling and its setup/control/readout/record costs, then connect that process
to the coherent comparison response. The new necessity theorem concerns interaction for a
stated readout, not a selected vacuum schedule, root frequency or coupling constant. No
numerical formula changed.

Validation: complete `check.sh` passed with 3415 build jobs and 991 strict-audited PMAction
declarations, permitting only `propext`, `Classical.choice` and `Quot.sound`. The no-downstream-import
dependency audit passed. Log: `/tmp/pm2-matched-operational-check.log`.
