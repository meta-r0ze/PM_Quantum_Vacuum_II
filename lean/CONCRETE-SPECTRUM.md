# Concrete two-wall representation and branch count

Current update: VACUUM-PRESERVATION.md supersedes the earlier open task of
preserving the known vacuum zero modes. The corrected ordering now preserves
them exactly, retains unitarity/locality and has the same first-order generator.
Excluding extra finite-tick unit eigenphases remains open.

## What is proved

`ConcreteFermion.lean` specifies beta=[[0,I],[I,0]], Gamma=diag(I,-I),
and alpha_j=diag(sigma_j,-sigma_j), using exact complex entries. Lean checks:

- all Clifford relations and commutation of alpha_j with Gamma;
- Hermiticity of these matrices, the sine-momentum operator and the full
  eight-component Hamiltonian for every real k and delta;
- rank two for each Gamma chirality projector;
- an explicit linear equivalence between ker H(0,0) and C^4. Every zero mode
  is exactly ((u0,u1,0,0),(0,0,u2,u3)); the wall components have opposite chirality.

`ConcreteSpectrum.lean` reindexes H² into four exact 2-by-2 blocks, without a
floating-point computation. With s=sum sin²(k_j), m=sqrt(delta²+1/4)-1/2,

    charpoly(H²) = (X-(s+m²))^4 * (X-(s+(m+1)²))^4.

The two roots are strictly distinct for every real delta, since m>=0. The
separate `square_branch_multiplicities` theorem proves root multiplicity four
for each. These are actual algebraic multiplicities, not only necessary
constraints on possible eigenpairs. At k=delta=0, the explicit kernel proof
also supplies the geometric dimension four directly.

Both modules are imported by PMAction.lean and covered by AuditStrict.lean.
The chosen representation contains eight complex components before selecting
low-energy modes. Four complex kernel dimensions do not mean four physical
fermion species, nor four generations.

## What this does not select

The representation, two-wall construction and Wilson point are explicit model
data. These proofs do not derive them uniquely from persistence or E8. They do
not assign the wall components to physical gauge representations or connect
them to Paper I's actual channel carriers. The multiplicity theorem is for H²;
it does not establish how those multiplicities split between positive and
negative energies of H away from zero. No physical clock step, field scale,
Yukawa coefficient or coupling is fixed.

The generic DomainWallSpectrum results still supply the all-momentum zero
exclusion and uniform bandwidth. An exponential of this finite-range
Hamiltonian needs a separate locality analysis before it can be called a
strictly finite-stencil discrete update.

## Next useful tasks

1. Prove signed H spectral multiplicities, including the degenerate origin.
2. Define the discrete-time update and its exact locality requirement; prove
   the update satisfies it rather than inferring locality from Hermiticity.
3. Derive the common scalar/fermion bridge and normalization before using it
   for Paper III's numerical matching.


## Concrete-spectrum verification, 2026-10-28

Complete check.sh passed: 3356 build jobs and 324 PMAction declarations in the
strict transitive axiom audit. Only propext, Classical.choice and Quot.sound
are permitted; no sorry, native_decide or custom proof axioms were introduced.
The revised full manuscript compiled successfully with the desktop compiler.
Source checks found no missing reference labels or citation keys. Acknowledgments
match the pre-cleanup backup byte-for-byte. No dependencies were installed.


## Superseding progress

SignedSpectrum and EnergyCounts now prove the signed characteristic polynomial
and multiplicity two at each nonzero signed branch. LocalUnitary through
SplitGenerator supply a concrete finite-propagation unitary split update with
the correct first-order Wilson generator. See SIGNED-AND-LOCAL.md for exact
scope. The finite-tick origin-zero/eigenphase analysis remains a separate task.


## Verification, 2026-10-28

The complete check.sh passed: 3375 build jobs and 445 project declarations
passed the strict transitive axiom audit. Only propext, Classical.choice and
Quot.sound are allowed. No sorry, native_decide or custom proof axioms were
introduced. All eight new proof modules are imported by PMAction.lean.
The complete revised manuscript compiled with its actual bibliography. Source
cross-reference and citation checks passed; acknowledgments remain byte-for-byte
unchanged. No dependencies were installed, and no Paper III file was changed.
