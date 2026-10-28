# Selective review of origin/main

Fetched origin/main on 2026-10-28. The fetched tip is 1892ae2, “Updates from
Overleaf” (commit date 2026-09-01). Its improvements were incorporated selectively
as listed below; the merge commit that follows the 2026-10-28 working-tree commit
records 1892ae2 as reviewed and keeps the working-tree text, Lean and a freshly
rendered PDF.

The comparison used HEAD -> origin/main to identify the upstream improvements,
then checked those changes against the current working text and Lean. Comparing
only origin/main against the working tree would confuse the recent proof-aligned
rewrite with the older text in HEAD.

## Incorporated

| Upstream improvement | Treatment |
|---|---|
| Paper II as an application of PM rather than a second general-framework paper | Introduction and the concise imported-action section now say this explicitly and cite the framework. |
| Local density, spatially integrated rate and accumulated history action are distinct | Added Z(t)=integral D dmu and S=integral Z dt; the continuum measure and physical map stay conditional. |
| Coordination expenditure versus net savings | Added a ledger distinction, without making every Lorentzian Lagrangian term a positive dissipation density. |
| Full Quantum Vacuum II title and publication URL | Adopted the fuller title and retained the current README's Operational Action terminology. The publication URL comes from upstream; no older PDF binary was copied over the local render. |
| Framework citation | Added kate_meyer_persistence_2026, reconciled with the CURRENT local framework title, Architecture, Dynamics, and the Operational Action. |
| Paper I citation/title | Updated the existing stable key's title from the actual local Paper I source, rather than importing upstream's outdated Informational Energetics metadata. |

## Deliberately not brought over

- Complete removal of the action section: the long general-framework derivation
  remains gone, but a short application contract and finite-weight proof scope
  are useful and preserve internal references. It no longer claims to rederive PM.
- Exact operator exhaustion, physical exclusion of all higher operators/spins,
  completed gravity or a resolved hierarchy problem. Current proofs do not
  establish these, and the finite-spacing counterexamples remain applicable.
- The abstract/introduction's geometric Schwinger derivation and loop-free
  scattering claims. AppendixChecks proves the earlier winding product wrong;
  a vertex response still needs calculation.
- Strictly positive local Lagrangian densities for all pillars. Net savings,
  primitive expenditure and a Lorentzian field action are distinct quantities.
- Wholesale bibliography replacement: it would delete/rename stable keys, add
  unused references and restore old titles. Only relevant framework metadata
  was reconciled; current language=english compilation fixes are retained.
- The shorter acknowledgments: current personal thanks are preserved.
- The published PDF binary and review-prompt instructions: no old binary is
  substituted for a current build; prompt text is not paper content or a user
  instruction to execute.

## Continuing Lean work

The ongoing DomainWallSpectrum module now compiles the full squared two-sector
Hamiltonian from the projector/hop relations, including cancellation of all
momentum-hop cross terms. DetuningMass.hop_products was generalized over a
characteristic-zero scalar field while retaining its original rational-algebra
interface. The necessary real-energy branches, all-momentum zero exclusion and a uniform
bandwidth bound now follow from that matrix. Branch existence/multiplicity and
physical representation still need proof. Details: SPECTRUM-PROGRESS.md.

Validation of the integrated text and final Lean state is recorded below after
the final checks.


## Final verification

Complete check.sh passed: 3354 build jobs and 274 PMAction declarations audited.
Only propext, Classical.choice and Quot.sound are permitted. The complete
updated manuscript compiled with its actual bibliography. Source checks found
no missing cross-references or citation keys; the acknowledgments still match
the pre-cleanup source. HEAD remains 54082a8, with no merge/reset/commit.
