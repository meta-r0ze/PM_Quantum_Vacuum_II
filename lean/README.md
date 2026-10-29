# PM-2-Action: Lean scope and completion plan

Current program review: [CROSS-PAPER-BRIDGE-REVIEW.md](CROSS-PAPER-BRIDGE-REVIEW.md).
The main priority is the shared substrate/event/action/response connection;
finite-tick spectrum completion remains a bounded viability test.

Lean 4.34.1. Mathlib is pinned through the sibling PM-1-Arch/lean package.
Keep paper directories as siblings and run:

```sh
source ~/.elan/env
./check.sh
```

`PM_ACTION_LAKE_BIN` can name the installed lake executable. Existing dependency
caches are reused; no new installation was needed for the review.

## Checked results and boundaries

| Modules | Mathematical result | Boundary |
|---|---|---|
| Survival (with `PMFramework.Gibbs`) | Positive normalized finite history weights, ratios and ordering; concentration uniformly on degenerate minima as inverse tolerance grows (framework `Gibbs`, moved from here). | Finite weights do not delete alternatives; the survival law and limiting regime are inputs. |
| Reconstruction | Detailed balance symmetrizes the transfer operator; symmetry plus injectivity gives a positive two-tick operator and real logarithmic energies. Spectral phases and configuration bijections preserve amplitude norms. | Detailed balance, statistical-operator injectivity and supplied amplitudes are premises; no Born rule or full field/locality reconstruction. |
| Protocol, Gauge | Transforming links preserve transport; loop products transform by conjugation and class scores are invariant. Exact U(1) cost bounds and field-normalization freedom. | No group, unique Wilson score or numerical coupling is selected. |
| D4Gauge | 24 roots, 192 ordered triangle pairs, exact isotropic area tensor and flux sum; quadratic normalization at beta=1/(2g²). | Constant-field geometric phase and volume/counting convention; beta itself remains free. |
| GaugeContinuum | Explicit small-phase error, exact sinc representation, actual cosine-action limit and the conditional Maxwell limit. | Abelian constant field; no non-Abelian path-order or varying-field error estimate yet. |
| Dirac | First-order squared relativistic dispersion iff Clifford relations. | The dispersion and first-order form are specified; no unique physical representation follows. |
| DiscreteEvolution, Doubling, TwinTests, WalkSpeed | Exact finite-ring norm preservation, twin relation and equal gauge response; split-step twin-gap/speed trade-off. | Results apply to named walk families, not all possible lattice updates. |
| DomainWall | Zero-momentum chiral kernel conditions, Clifford momentum square and chirality commutation; scalar phase-alias exclusion under a bandwidth hypothesis. | See DomainWallSpectrum and ConcreteFermion/ConcreteSpectrum for the squared spectrum, zero-mode count and bandwidth; discrete-time locality remains open. |
| DomainWallSpectrum | Full squared operator, its polynomial, necessary real-energy branches, no extra zero modes anywhere in the momentum cell, and a uniform real-energy bandwidth/phase-alias bound. | ConcreteFermion/ConcreteSpectrum now establish a Hermitian example and squared-branch counts; physical clock step and finite-tick eigenphase analysis remain open. |
| ConcreteFermion, ConcreteSpectrum | Exact Pauli/Clifford representation; Hermitian eight-component Hamiltonian; rank-two chirality projectors; a four-dimensional zero kernel; exact H² characteristic polynomial with two distinct roots of algebraic multiplicity four each. | Representation and Wilson parameters are specified. SignedSpectrum now supplies signed-energy multiplicities; physical species/channel identification and substrate selection remain open. |
| SignedSpectrum, EnergyCounts | Exact signed characteristic polynomial; multiplicity two at each nonzero positive/negative branch; four zero roots at the origin. | Counts concern the specified Hamiltonian. Physical species and the finite-tick spectrum remain open. |
| LocalUnitary, SplitUpdate, PropagationBounds, WilsonSplit, SplitSymbol, SplitGenerator | A concrete eight-component unitary update on every finite periodic cubic lattice; total squared-amplitude preservation; at most 27 spatial input sites; matching Wilson generator and first derivative of the momentum symbol. | First-order consistency does not prove finite-tick zero-mode preservation, absence of extra unit eigenphases, many-tick convergence, or physical selection of the update. |
| VacuumSplit, VacuumGenerator, VacuumUniform | Corrected coin preserves every known vacuum mode exactly for all ticks, including actual uniform finite-lattice states; retains unitarity, amplitude conservation, 27-site propagation and the same first derivative. | Does not exhaust the finite-tick fixed space or exclude extra unit eigenphases; admissible tick and unique physical selection remain open. |
| DetuningMass | Hop/projector products; candidate reduced-block light root, mass polynomial, positivity and corner bound. | The concrete squared-Hamiltonian spectrum now realizes these roots; on-site detuning is not automatically a changed link or Yukawa field. |
| Governor, Potential, Operators | Mexican-hat signs within the quadratic occupancy ansatz; minimum and VEV convention; leading dimension-four list; suppressed higher terms and finite-amplitude counterexample to exact quartic truncation. | Ansatz, kinetic normalization and dimension cutoff are hypotheses; no exact operator exhaustion or naturalness theorem. |
| AppendixChecks | The rejected winding product is 2alpha, not alpha/(2pi). | Scattering, vertex response and running are not derived. |

`AuditStrict.lean` checks public and private declarations and all transitive
axioms. Only propext, Classical.choice and Quot.sound are allowed. No sorry,
native_decide or custom physical proof axioms are used by the new work.

## Review and next order

See [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md). The first gap closed in this pass is
the actual Abelian triangle cosine limit. The squared Hamiltonian, necessary branches, all-momentum zero check and a
sufficient bandwidth bound are now proved. A concrete Hermitian representation, its zero kernel and squared-branch multiplicities are now checked. Signed-energy counts and a concrete local unitary split update now follow; see SIGNED-AND-LOCAL.md. VacuumSplit now fixes exact preservation of the known zero modes; see VACUUM-PRESERVATION.md. Next prioritize exclusion of additional finite-tick unit eigenphases and error control. Extended gauge limits
can proceed alongside that branch. A common scalar/fermion/gauge response must
precede Paper III's numerical physical matching. Gravity and measurement require
new constructions, not small missing arithmetic lemmas.

## Text alignment

The manuscript now separates exact results, conditional assumptions, limits,
numerical checks and proposals. It no longer simultaneously claims Wilson-free
fermions and a Wilson/domain-wall mechanism, exact finite-spacing Wilson
truncation, or a gauge coupling fixed by hop speed. It does not claim completed
gravity, a derived Born rule, exact operator exhaustion or particle exclusions.
The Hamiltonian/Clifford conventions and scalar VEV convention are explicit.

The full revised paper/main.tex compiled with the actual bibliography using the
desktop compiler. The unused constants extraction was removed and bibliography
language codes normalized. All references/citation keys resolve at the source
level, and the acknowledgments are unchanged. The previous text is backed up
at the workspace path recorded in REVIEW-AND-NEXT.md.

The baseline before GaugeContinuum passed: 3350 build jobs and 202 strict-audit
declarations. The final updated verification follows.


## Gauge-continuum verification, 2026-10-28

Complete check.sh passed: 3353 build jobs and 222 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound are
permitted. The full current paper/main.tex compiled successfully with the actual
bibliography and without stubbed numeric macros. Source checks found no missing
cross-reference labels or citation keys; acknowledgments match the saved pre-pass
text byte-for-byte. No new dependencies were installed. The built-in compiler
was used; no terminal TeX installation is required.


## Operator-spectrum progress

See SPECTRUM-PROGRESS.md for the full squared-operator polynomial, necessary
real-energy branches, all-momentum zero exclusion and a uniform bandwidth bound.
These are derived under the named Clifford/Wilson-point hypotheses. They are
now complemented by the concrete zero-mode and squared-branch count in
CONCRETE-SPECTRUM.md. Physical species assignment and a strictly local
discrete-time construction remain open. The selective origin/main comparison is
UPSTREAM-TEXT-REVIEW.md; no branch reset or whole-file upstream replacement was
performed.


Latest verification (upstream integration and operator spectrum): complete
check.sh passed with 3354 build jobs and 274 audited PMAction declarations.
The full revised manuscript compiled with its bibliography; source reference
and citation checks passed, and the acknowledgments remain unchanged.


## Concrete-spectrum verification, 2026-10-28

Complete check.sh passed: 3356 build jobs and 324 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound
are permitted; no sorry, native_decide or custom proof axioms were introduced.
The revised full manuscript compiled successfully with the desktop compiler.
Source checks found no missing reference labels or citation keys. Acknowledgments
match the pre-cleanup backup byte-for-byte. No dependencies were installed.


## Verification, 2026-10-28

The complete check.sh passed: 3375 build jobs and 445 project declarations
passed the strict transitive axiom audit. Only propext, Classical.choice and
Quot.sound are allowed. No sorry, native_decide or custom proof axioms were
introduced. All eight new proof modules are imported by PMAction.lean.
The complete revised manuscript compiled with its actual bibliography. Source
cross-reference and citation checks passed; acknowledgments remain byte-for-byte
unchanged. No dependencies were installed, and no Paper III file was changed.


## Vacuum-preserving verification, 2026-10-28

Complete check.sh passed: 3380 build jobs and 506 PMAction declarations in
the strict transitive axiom audit. Only propext, Classical.choice and Quot.sound
are allowed. No sorry, native_decide or custom proof axioms were added. The
three new modules are included in PMAction.lean. The complete updated paper
compiled successfully with its actual bibliography; reference/citation checks
and git diff --check passed, and acknowledgments remain unchanged.

The optional double-precision diagnostic now compares both orderings. For
tau=0.1, 0.25 and 0.5, the corrected zero-basis displacement is at roundoff
(2.2e-16 to 4.4e-16), consistent with the exact Lean preservation theorem.
This numerical comparison does not supply the no-extra-modes theorem.
No dependency installation or Paper III changes were needed.


## Carrier → event → cost → common response, 2026-10-28

The chain from Paper I's carriers to a common quadratic response is now closed in Lean:

- `CarrierEvents`: the eight minimal vectors of each nontrivial D4 glue class are the carriers
  (`carrier_card`, `vector_surjective`); the event is a coordinate reflection, half the carriers
  move (`active_card`), and one event costs `toll/2` under uniform input.
- `SelectedSampling`: that uniform input is the law the framework's Selection Principle keeps
  (`PMFramework.LawSelection`); with it, event accounting is Paper I's `NetCost`
  (`selected_recovers_netCost`) and a reflection event costs `toll/2` (`selected_primitive_cost`).
- `SubstrateReflection`: that reflection is the restriction of an actual integral E8 root
  reflection, preserving the E8 form and the D4⊕D4 glue labels (`euclidean_intertwines`).
- `CarrierCost`, `EventAccounting`: counted events priced at the common primitive toll; weighted
  linearity needs no independence and recovers Paper I's `NetCost`.
- `InterferenceReadout`, `CarrierResponse`: a coherent transported/reference comparison raises a
  flag with probability `(1 − Re U_aa)/2`; refreshed phase tests give the cosine action and its
  controlled continuum limit (`common_response_limit`).
- `CommonResponse`: the same readout for any normalized amplitude, `stateFlag U φ = ‖φ − Uφ‖²/4
  = (1 − Re⟨φ,Uφ⟩)/2` (`state_flag_formula`). It gives the gauge cosine (`gauge_case`), the
  fermion Wilson form `Re⟨ψ,(2 − U − U†)ψ⟩/4` (`wilson_form`) and the scalar covariant difference
  `‖φ' − Uφ‖²/4` (`linkFlag`). If all three are priced by the same event (one toll, one repair
  length `m`), each costs `toll·m/4·‖·‖²` (`common_normalization`). That shared normalization is a
  premise of the pricing, not a derived result: `common_normalization` only factors out the
  prefactor that `responseCost` puts there. `carrier_chain` evaluates the whole chain
  on the actual carriers: the E8 root reflection's averaged response is `toll·m/4`.

Still model inputs: the repair length `m`, the reference-branch preparation, and the
squared-amplitude readout (not a Born-rule derivation). The scalar's small-angle expansion to
`|θφ|²` (Paper III `LinkMass`) and the absolute scale of `toll` are not derived here.

## Scalar link at small angle

`LinkExpansion`: for a Hermitian generator in a unitary eigenbasis, `θ = V diag(λ)V†`, and its
transport `U_ε = V diag(e^{iελ})V†`, the event-law link cost satisfies
`|‖φ − U_εφ‖² − ε²‖θφ‖²| ≤ (5/48)ε⁴Σ|c_k|²λ_k⁴` whenever every `|ελ_k| ≤ 1` (`link_expansion`),
from `|1 − e^{ix}|² = 2 − 2cos x` and mathlib's cosine bound. The leading scalar response is the
quadratic form `‖θφ‖²` used by Paper III's `LinkMass`.


## Current carrier/event bridge

See [CARRIER-EVENT-RESPONSE.md](CARRIER-EVENT-RESPONSE.md) for the actual carrier
and E8 root-operation connection, counted trace cost, explicitly normalized
phase-sensitive readout, primitive repair ledger and controlled response limits.
Latest complete check.sh: 3393 jobs, 677 declarations passed strict axiom audit.
The manuscript now includes these results and their preparation/readout/repair
premises. CommonResponse and LinkExpansion supplied by the companion work are
included and reviewed. Full physical representation/current selection remains
open; a shared parameter in a cost definition is not its microscopic derivation.
