# Paper II review and completion order

The cross-paper review in CROSS-PAPER-BRIDGE-REVIEW.md supersedes the historical
priority lists below: first connect actual carriers, primitive costs and common
response. Keep the finite-tick spectral work as a specific admissibility test.

Current update: VACUUM-PRESERVATION.md supersedes the earlier open task of
preserving the known vacuum zero modes. The corrected ordering now preserves
them exactly, retains unitarity/locality and has the same first-order generator.
Excluding extra finite-tick unit eigenphases remains open.

Reviewed 2026-10-28 against the current text and actual Lean theorem statements.
The starting package passed check.sh: 3350 build jobs, 202 audited PMAction
declarations. The new files from the other AI were reviewed in place; no
existing proofs were removed.

## Where the paper is now

The triangle area tensor, two-sector kernel conditions and detuning polynomial
are substantial positive additions. The old manuscript still asserted stronger
results than those statements and sometimes contradicted them. The text pass
now separates exact results, conditional models, continuum limits, numerical
checks and proposed physical identifications. All prior section/equation labels
and the acknowledgments are retained. Older citations and their metadata remain
in the bibliography; English language codes were normalized to fix compilation.
The earlier paper sources are saved at:
/Users/kate/Documents/Codex/2026-10-26/for-x20/work/paper2-before-text-tefrhy9u/paper/

## First completion: actual gauge-action continuum limit

D4Gauge.normalization established the quadratic coefficient algebraically,
conditional on a triangle phase and cell-volume convention. It did not itself
prove the limit of the cosine action. GaugeContinuum now closes the Abelian
constant-field part:

- scaled_error bounds |(1-cos(h²a))/h⁴-a²/2| by (5/96)|h|⁴|a|⁴ when h!=0 and
  |h²a|<=1, using mathlib's proved cosine bound.
- scaled_sinc gives an exact nonsingular expression away from h=0.
- scaled_limit proves the punctured-spacing limit a²/2.
- density_limit sums the ACTUAL finite triangle cosine action and uses the
  existing area tensor, giving (beta*g²/2)*sum F².
- maxwell_limit gives coefficient 1/4 at beta=1/(2*g²), g!=0.

This is a genuine continuum theorem rather than an assumption of exact finite-
spacing truncation. Its scope is the supplied constant Abelian triangle flux;
nonconstant-field geometry errors and non-Abelian path ordering are not covered.
Neither it nor the old normalization theorem selects beta or a physical coupling.

## Highest-priority remaining Lean work

1. **Full two-sector matrix spectrum.** Define the actual Hermitian Hamiltonian
   with real momentum and the chosen Wilson parameters. Derive its squared block
   from the hop/Clifford algebra. Prove the eigenvalue branches and multiplicities,
   identify the light root, and rule out zeros throughout momentum space. Corner
   gaps and scalar characteristic-polynomial identities alone do not do this.
2. **Discrete time, bandwidth and locality.** The scalar update_zero_mode theorem
   requires |tau*E|<2pi. Prove a uniform spectral bound and matrix-level update
   statement. An exponential of a local Hamiltonian is not automatically a
   finite-stencil quantum walk; choose and prove the required locality notion.
3. **Complete the gauge limit.** Bound varying-field triangle flux errors and
   non-Abelian/path-order remainders. Derive the relevant representation/trace
   normalization. A speed-matching hopping coefficient is not a gauge coupling.
4. **Common scalar/fermion response.** Derive scalar kinetic normalization and
   the physical bridge field. The DetuningMass parameter adds an on-site beta
   term with fixed hops; it is not automatically a detuned hopping link. Relate
   its nonlinear mass root to a Yukawa/VEV law before using Paper III formulas.
5. **Reconstruction linked to the update.** Detailed balance and injectivity of
   the symmetrized statistical transfer operator are explicit premises. A
   bijective realized update does not prove them. Establish the common state,
   observables and continuation, then causal/continuum reconstruction.
6. **Gravity and measurement.** These require new constructions, not a few
   missing algebraic lemmas. No current Lean proof derives metric equations,
   ghost-free spin-two dynamics, Born probabilities or apparatus basis selection.

The order follows mathematical dependencies and usefulness for Paper III's
shared response, rather than attempting numerical constants from separate
geometric formulas. Fermion spectrum and the extended gauge analysis can proceed
as independent branches; neither needs another abstract eta encoder.

## Main text corrections

- Forward Euler is labeled an approximation and its gradient sign is consistent
  with the stated Hamiltonian. The Hamiltonian and Lorentzian Clifford sign
  conventions are stated consistently.
- The two-sector candidate is explicitly Wilson/domain-wall, replacing the
  contradictory Wilson-free footnote. Kernel conditions are not promoted to a
  global spectrum or fixed chiral multiplicity theorem.
- The leading dimension-four list is conditional. Finite state count does not
  imply exact absence of phi-six, higher derivatives or curvature corrections.
- Gauge normalization is not inferred from link speed; exact finite-spacing
  Wilson truncation is replaced by the new controlled limit.
- Scalar sign/minimum selection is separated from numerical coefficients,
  kinetic response and hierarchy/naturalness claims.
- Detailed balance, operator injectivity and quantum amplitude data are exposed
  as hypotheses. Finite survival weights do not delete all alternatives.
- Gravity, measurement and particle-exclusion claims are presented as open
  program targets. The logarithmic Born-rule assignment is not a derivation.
- The QED cross-section remains a heuristic comparison; the rejected winding
  argument and uncompleted vertex/vacuum-polarization tasks remain visible.

## Builds

The complete revised main.tex compiled successfully with the desktop compiler
(with actual bibliography, no stubbed constants). Removed an unused constants
extraction and normalized bibliography language=en to language=english; the
acknowledgments, author information and legacy links are unchanged. The full
Lean audit result for the new module is recorded in README.md after completion.


## Final verification, 2026-10-28

Complete check.sh passed: 3353 build jobs and 222 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound are
permitted. The full current paper/main.tex compiled successfully with the actual
bibliography and without stubbed numeric macros. Source checks found no missing
cross-reference labels or citation keys; acknowledgments match the saved pre-pass
text byte-for-byte. No new dependencies were installed. The built-in compiler
was used; no terminal TeX installation is required.


## Spectrum pass after the upstream comparison

DomainWallSpectrum now proves the full squared matrix and its polynomial from
the projector/hop algebra. All real-energy eigenpairs satisfy
E²=s+m(delta)² or E²=s+(m(delta)+1)². For sine momentum and Wilson detuning on
the whole momentum cell, a nonzero zero mode requires k=0. The real-energy
bandwidth is uniformly below 8; 0<|tau|<=1/2 suffices to avoid unit-phase aliases.
These results replace the earlier open squared-block, off-corner-zero and
bandwidth tasks. They do not assert branch existence/multiplicities or choose
a physical clock step. Next: an explicit Hermitian representation and its
spectral multiplicities, then discrete-time locality and physical response.

The origin/main text comparison and selective integration are recorded in
UPSTREAM-TEXT-REVIEW.md. Its application framing, local/integrated density
clarification and publication naming are incorporated without restoring
unsupported uniqueness, exact truncation or Schwinger derivation claims.


## Concrete representation and squared-branch count

ConcreteFermion now verifies an explicit Pauli/Clifford representation and the
Hermiticity of the full eight-component Hamiltonian. The zero kernel is linearly
equivalent to C^4, with two opposite-chirality wall components each.
ConcreteSpectrum factors the full H² characteristic polynomial and proves
algebraic multiplicity four for each of its two distinct roots. This closes the
concrete-example, zero-kernel and squared-branch tasks above. See
CONCRETE-SPECTRUM.md for precise scope. The next finite algebraic task is signed
H eigenvalue counts; the next construction task is a discrete update with an
explicit locality contract. Physical species assignment and parameter selection
remain open, rather than consequences of the chosen matrices.


## Concrete-spectrum verification, 2026-10-28

Complete check.sh passed: 3356 build jobs and 324 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound
are permitted; no sorry, native_decide or custom proof axioms were introduced.
The revised full manuscript compiled successfully with the desktop compiler.
Source checks found no missing reference labels or citation keys. Acknowledgments
match the pre-cleanup backup byte-for-byte. No dependencies were installed.


## Current priority after signed counts and local construction

See SIGNED-AND-LOCAL.md. Signed energy multiplicities and a concrete unitary,
finite-propagation eight-component split update are now formalized. The split
symbol has the correct first derivative at zero tick. The next task is its
own finite-tick spectrum, starting with exact origin-zero preservation and
extra unit eigenphases. The earlier Hamiltonian bandwidth theorem does not
settle that question for a noncommuting product. If this ordering fails, seek
an origin-preserving ordering under explicit constraints. Then establish
many-tick error bounds and the gauge/scalar response bridge. Do not proceed
to numerical physical matching by importing the Hamiltonian roots as the
finite-step eigenphases without proof.


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


## Carrier-event completion checkpoint

The new mainline results and exact remaining contracts are in
CARRIER-EVENT-RESPONSE.md. The actual carrier/E8 root operation, primitive event
accounting, conditional trace/cosine readout and controlled common link response
now pass the 677-declaration audit. Next derive the carrier gauge action and
resource requirements, rather than treating representation labels or empirical
parameter selection as consequences of counting alone.
