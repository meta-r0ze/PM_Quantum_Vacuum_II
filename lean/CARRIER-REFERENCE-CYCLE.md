# A repeatable carrier/reference cycle

Follow-up: `CarrierProbe.cycle_does_not_read` proves that the autonomous phase history alone
does not read a nonconstant carrier bit, even for this non-idle cycle. `ClockControlledRoot`
now verifies the conditional lattice action and internal root-step geometry. See
[OPERATIONAL-READOUT.md](OPERATIONAL-READOUT.md) for the necessary interaction and the remaining
physical implementation contract.

`PMAction.CarrierReferenceCycle` is the first finite operational test of the Paper II microscopic
contract. It uses the existing actual D4 carriers and their E8-induced root reflection, together
with a supplied 43-phase clock. It changes no constant or downstream workload.

## State, encoding and update

For any of the three nontrivial glue classes, the state is `(carrier, phase)` with 8 × 43 = 344
possibilities. Let `R` be the existing involutive root reflection and `b(t)` a Boolean phase mask.
Encode a reference carrier `r` at phase `t` as `(R(r),t)` if `b(t)` is true and `(r,t)` otherwise.
This encoding is itself a permutation, so the reference can always be recovered.

The update is conjugate to clock advance through that encoding. This is a closed register-cycle
construction, not yet an interacting spatial dynamics. Its proved gate form is:

1. Advance the phase once.
2. Reflect the carrier once if the old and new mask values differ; otherwise leave it alone.

The conjugacy is an algebraic description. Its two rebases are not charged as two physical gates
on every tick: `tick_gate_form` supplies the equivalent single-conditional-root implementation.
This implementation's access to the clock and conditional control is still an explicit input.

`reference_preserved`, `cycle_closes`, `cycles_repeat` and `trajectory_visits` prove preservation
at every tick, exact 43-tick return on every state, arbitrary repetition, and traversal of the
actual phase-indexed trajectory. No clean record reservoir is consumed. `tick_unitary` proves
unitarity of the resulting permutation matrix, given the amplitude construction.

## Work, including the return and clock

`event_matches_update` proves the carrier event sets describe the actual changed carriers.
The same reference label controls the outgoing and returning events; no independence is assumed.
For an explicitly uniform reference ensemble, the root-component cycle cost is

`root toll × number of mask boundaries / 2`.

This is an ensemble mean, not a time-average result for every individual history.
`pointwise_excursion_count` proves that a fixed active reference experiences two carrier changes
per cycle, while a fixed inactive reference experiences none. The conserved reference never
mixes between those sets in this model. A physical sampling or amplitude/readout contract is
therefore still needed to interpret the uniform average as a measured vacuum cost.

The half comes from the already proved four moving carriers out of eight, not a fitted factor.
`boundary_minimum` proves a nonempty binary change set on a closed clock has at least two edges.
`minimum_nonidle_carrier_cost` proves the minimum over this stated non-idle mask family is one
root toll; at positive toll equality holds exactly for two boundaries. The one-phase excursion
is an attainment witness. The reflection and its return are both counted. The separate
`minimum_closed_root_word` checks that two is also the shortest positive closed word on all
carriers using this single reflection generator.

`clock_cycle_cost` charges all 43 phase advances at a separate supplied clock toll. The two
specified ledger components therefore sum to `root toll + 43 × clock toll` for the minimum
excursion. This excludes preparation, phase control, storage and other implementation costs
unless an event contract explicitly includes them in those prices. It is not a minimum cost
for the complete apparatus, an absolute energy prediction or a proof of a gauge ledger.

## What persistence does and does not select here

Every mask yields a closed reversible cycle. The idle mask has zero carrier cost and also
persists. Requiring a non-idle root task is therefore an operational premise. Among those tasks,
Economy selects the boundary count, but not the timing or duration of the excursion. Nothing here
derives eta, the sector workloads, the physical sampling law or a coherent branch mixer.

The construction preserves its encoded reference. It does not take arbitrary noise and erase it
to restore an independently specified target. Different references remain different; a universal
finite reversible reset remains impossible. Thus it does not contradict `ReferenceMaintenance`'s
no-reset theorems. Nor does it justify dropping required payload fields or deferring their work.

## Next implementation obligation

Connect this register/clock action to the substrate's actual allowed local operations and spatial
state. Derive a disturbance/task that requires a root excursion, rather than selecting the mask
to fit a desired coefficient. Then account for phase control and coherent mixing, and prove how
their event ledger maps to the common comparison response. That is the next part of the Paper II
contract; the current cycle is an explicit finite candidate and a set of constraints on it.

Validation: complete `check.sh` passed, 3411 build jobs and 917 strict-audited declarations,
with the no-downstream-import dependency audit. Only the three permitted standard axioms
are allowed. Log: `/tmp/pm2-carrier-cycle-check.log`.
