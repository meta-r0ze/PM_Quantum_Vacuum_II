# PMAction — Paper II action library

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum II: Operational
Action and the Emergent Lagrangian*. This package supplies **shared dynamics,
event accounting and action-response mathematics** to the later papers. It builds
on the Paper I substrate (`../../PM-1-Arch/lean`) and the framework (`../../PM/lean`) and
**rejects imports from Papers III–VI**.

## Main result

`PMAction.Main.hermitian_action_response` (`PMAction/MainTheorem.lean`) packages a
constructed response model. For a supplied finite Hermitian generator `H` and
normalized complex amplitude `φ`, its transport is unitary and its two-branch
response is

    (1 − Re⟨φ,Uφ⟩)/2 = ‖φ − Uφ‖²/4,

with the squared displacement equal to `t²‖Hφ‖²` up to an explicitly bounded
fourth-order remainder. These results do **not** select a physical generator, gauge
representation, state/readout contract or primitive implementation.

Shared results also include the **conservation → continuity** derivation
(`Continuity`) and the **gravitational weak-field reconstruction** from the
capacity ledger (`WeakField`, with `channelCapacity = ν = 16`): `g_00 = −(1+2Φ)` for
both the paper's linearized pair and the exact clock-squared pair, with
`Φ = −K/ν + K²/(2ν²)`. The **discrete causal structure** (`DiscreteCausal`) and the
**discrete response law** (`ResponseLaw`: Laplacian source-neutrality) and the
**Coulomb kernel** interface (`CoulombKernel`: `lap G = δ`, concrete 2/3/4-site
path Green functions) are derived from
the actual update stencil and adjacency, not postulated.

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)** — what is proved and reusable: the module map,
  the spectrum/split/locality results, the interpretation boundaries, and what each
  later paper may rely on. **Start here to find a theorem you can use.**
- **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)** — the remaining obligations, one
  list, with nothing already done.

## Build and audit

Lean 4.34.1; Mathlib is pinned through sibling `PM-1-Arch/lean`, and the framework
is sibling `PM/lean`. Keep these directories as siblings, then run:

```sh
source ~/.elan/env
./check.sh
```

`PM_ACTION_LAKE_BIN` can name a specific Lake executable. `check.sh` builds the
default library, strictly audits project declarations and their transitive axioms,
and rejects Paper III–VI imports. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. A successful audit certifies the statements under their
stated hypotheses; it does **not** select the physical inputs.

## Verification

Run `./check.sh`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
