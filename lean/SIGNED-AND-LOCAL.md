# Signed spectrum and an exact finite-range split update

Current update: VACUUM-PRESERVATION.md supersedes the earlier open task of
preserving the known vacuum zero modes. The corrected ordering now preserves
them exactly, retains unitarity/locality and has the same first-order generator.
Excluding extra finite-tick unit eigenphases remains open.

## Signed Hamiltonian spectrum

SignedSpectrum verifies a real symplectic matrix J with J²=-I and
J Hᵀ=-H J for the concrete eight-component Hamiltonian. Transpose is intentional;
it is not an assertion of linear anticommutation JH=-HJ. It gives equal
characteristic polynomials for H and -H. A generic determinant identity links
charpoly(H)*charpoly(-H) to charpoly(H²) composed with X². Monicity selects the
positive polynomial square root, proving exactly

    charpoly(H) = (X²-(s+m²))² * (X²-(s+(m+1)²))².

EnergyCounts then establishes:

- each positive and negative heavy energy has algebraic multiplicity two;
- each positive and negative light energy has multiplicity two when nonzero;
- the light energy vanishes exactly when s=0 and delta=0;
- at the origin, charpoly(H)=X⁴(X-1)²(X+1)² and zero has multiplicity four.

The previous explicit zero-kernel equivalence supplies geometric dimension
four at the origin independently. No numerical eigensolver or assumed equal
sign split is used. Species, charges and channel identification remain open.

## Locality is now a constructed property

LocalUnitary uses A_j=(beta+i alpha_j)/2. Exact complex arithmetic proves
A_j²=0 and A_j A_j†+A_j† A_j=I. With a position permutation S and its inverse,
B_j=S tensor A_j+S† tensor A_j† is Hermitian and squares to identity. Hence
R_j(tau)=cos(tau)I+i sin(tau)B_j is exactly unitary, for every real tau.

SplitUpdate doubles these coefficients to eight internal components and proves
unitarity of an on-site coin followed by three directional factors. It proves
the global finite-state inner product and total squared amplitude are preserved.
Its support proof controls every matrix entry, and its input-dependence theorem
applies to arbitrary states, rather than only plane waves.

PropagationBounds identifies the support with three successive choices from
{stay, forward, backward}; there are at most 27 reachable spatial sites,
independently of lattice size. It supplies literal coordinate shifts on
(Fin N)^3, including wraparound and coincident-neighbor cases.

WilsonSplit fixes the on-site coin to exp(-i tau H0), H0=H(0,3). Only the
8-by-8 internal matrix is exponentiated. The resulting cubic update has
unconditional proved unitarity, total-amplitude conservation and finite
propagation for every real tau and every finite periodic size N.

The on-site and directional generators sum exactly to the chosen sine/Wilson
Hamiltonian. SplitSymbol checks the directional phase-weight identity. SplitGenerator proves
U_symbol(k,0)=I and the actual derivative U_symbol'(k,0)=-i H(k,delta_W(k)).
This is first-order consistency, not a fit of the finite-tick spectrum.

## Remaining boundary and best next task

The Hamiltonian eigenvalues are not automatically the eigenphases of a product
of noncommuting factors. In particular none of the old unit-phase no-alias
results has been transferred to this split product. Even exact preservation of
the origin's light zero modes must be checked for this ordering; matching the
first derivative does not establish it. The finite-tick spectrum, an admissible
physical tick, and an origin-preserving factorization if needed are the next
priority. A many-tick approximation/error theorem also remains open.

The construction uses the existing chosen Wilson Hamiltonian. Persistence alone
has not selected the representation, factor order, physical tick or on-site
coin uniquely. Gauge-covariant links, the scalar/Yukawa bridge and shared
response normalization still need proofs before Paper III's physical matching.

No Paper III file was edited during this pass.


## Diagnostic: the first ordering needs a vacuum-preservation fix

The optional `diagnostics/split_origin.py` evaluates the exact formulas above
in double precision, using NumPy/SciPy already available locally. It is not a
Lean theorem. At k=0 it reports:

| tau | Largest change of a zero-basis component | Nearest eigenphase magnitude |
|---|---:|---:|
| 0.1 | 0.0145188132 | 0.000746752745 |
| 0.25 | 0.076192127 | 0.0114031552 |
| 0.5 | 0.232743992 | 0.0838632061 |

Thus this ordering should not be treated as the finished physical update.
The numerical issue is much larger than floating-point roundoff, but its exact
analytic obstruction still needs formalization. A useful next candidate is to
split the on-site beta rotation from the wall hopping, so the three zero-momentum
spatial rotations cancel the on-site beta rotations exactly. The remaining
on-site hopping then acts trivially on the known zero kernel. This is a proposed
constraint-driven next proof, not a result already contained in WilsonSplit.


## Verification, 2026-10-28

The complete check.sh passed: 3375 build jobs and 445 project declarations
passed the strict transitive axiom audit. Only propext, Classical.choice and
Quot.sound are allowed. No sorry, native_decide or custom proof axioms were
introduced. All eight new proof modules are imported by PMAction.lean.
The complete revised manuscript compiled with its actual bibliography. Source
cross-reference and citation checks passed; acknowledgments remain byte-for-byte
unchanged. No dependencies were installed, and no Paper III file was changed.
