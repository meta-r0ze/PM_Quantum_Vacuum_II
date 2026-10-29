# Ownership of shared Lean foundations

The dependency direction is `PMFramework / PMArch -> PMAction -> later papers`.
The following general proofs were implemented in Paper III but contain no constants or
Paper III physical representation choices, and now live in Paper II.

| Canonical Paper II module | Paper III compatibility module | What remains in III |
| --- | --- | --- |
| `HermitianTransport` | `LinkSpectralResponse.HermitianTransport` | W/Z generator, mass form and link specialization |
| `LinkEvolution` | `LinkEvolution` | `mass_form_exponential` and the W/Z-specific imports |
| `CoherentComparisonRepair` | `CoherentComparisonRepair` | No duplicate implementation |
| `ControllerHamiltonian` | `ControllerHamiltonian` | Physical packet/controller identification remains an application obligation |
| `RefreshSchedule` | `MinimalRefresh` | Gauge resource sets and prices in `GaugeLedgers` |
| `ReferenceMaintenance` | `ReferenceMaintenance` | Sector assignment and ledger consequences in `ReferenceMaintenanceLedger` |

Canonical names start with `PMAction`. Former `PMNested` names are compatibility exports,
so existing imports and theorem references continue to resolve. Their definitions and proofs
are not copied in both packages. Paper II imports no Paper III module; `AuditDependencies.lean`
checks that boundary on the default import closure.

Later proofs that actually use packet/gauge/reference/constant data stay downstream. Examples:
`PacketGaugeActions`, `ReferenceMasses`, `SectorCapabilities`, `TableConsequences`,
`MatterRunning`, `CurrentConstants`. A gauge representation and an operational workload are
not general dynamics merely because their consequences are algebraic.

The older unimported `PMNested.ControllerTransferWitness` was already unfinished before this
move. It is not a completed theorem or part of either default audit. Its generic research
subject may eventually belong in II; moving a failing draft is not completion. The standalone
controller-admissibility audit also remains research outside the default imports.

After extraction, project declaration counts change ownership. A smaller PMNested count is not
lost proof coverage: its theorems still depend transitively on the audited PMAction results.
Both complete checks must pass after such a move.

## Review of the other later-paper candidates

Paper IV's `CKMClosure` applies complete-basis unitarity to its flavour/dressing model. Its basis
product identity is general matrix algebra, but it supplies neither Paper II's physical currents
nor generation selection. Its physical exclusion result stays in IV.

Paper V's `MassScaling` proves dimensional/exponent identities under a stipulated four-fermion
amplitude. Its mediator cancellation is already represented upstream by II's `ContactMatching`;
it does not construct the vertex or spinor/phase-space response missing from II. The decay law
and its mass scaling stay in V.

Paper VI's information/capacity lemmas do not construct the action or update. General finite
information lemmas could live in the PM framework; the cosmological load/response specializations
stay in VI. None of these later applications discharges the microscopic task or loop-response
premises merely by reproducing their downstream arithmetic.
