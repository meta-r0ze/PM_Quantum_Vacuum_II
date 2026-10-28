# Full two-sector operator: proved spectral constraints

Current update: VACUUM-PRESERVATION.md supersedes the earlier open task of
preserving the known vacuum zero modes. The corrected ordering now preserves
them exactly, retains unitarity/locality and has the same first-order generator.
Excluding extra finite-tick unit eigenphases remains open.

DomainWallSpectrum defines H with diagonal K+delta*beta and the actual hops
-beta Pplus and -beta Pminus. Pplus/minus=(1 +/- Gamma)/2. Its assumptions are
beta²=Gamma²=1, anticommutation of beta/Gamma, K²=sI, anticommutation of K/beta
and commutation of K/Gamma. These describe the chosen Wilson-point model,
not a proof that persistence uniquely selects that model or its parameters.

## New proofs

1. hamiltonian_square gives diagonal blocks (s+delta²)I+Pminus and
   (s+delta²)I+Pplus, and off-diagonal blocks -delta I. Every momentum/hop
   cross term is explicitly cancelled.
2. hamiltonian_polynomial proves on the FULL operator:

       (H²-(s+delta²)I)(H²-(s+delta²+1)I) = delta² I.

3. energy_constraint applies it to a nonzero real-energy eigenvector.
   energy_branches then proves E²=s+m(delta)² or s+(m(delta)+1)², using the
   existing mass_relation. The scalar polynomial is now a consequence of H.
4. kernel_requires_zero proves that nonnegative s and a nonzero zero vector
   require s=0 and delta=0.
5. kinetic_relations supplies the K hypotheses from the actual sine-momentum
   operator, the existing Dirac.Clifford contract and chirality commutation.
6. wilson_point_zero_only_at_origin proves no additional Hamiltonian zeros
   anywhere in the CLOSED cell [-pi,pi]^3 for delta=sum(1-cos k). This is not
   just a finite grid scan or a corner assertion.
7. energy_bandwidth proves |E|<8 uniformly for real eigenpairs, from s<=3,
   0<=delta<=6 and the derived light/heavy branches. This coarse bound suffices.
8. eigenphase_one_only_at_origin combines that bound with the existing phase
   theorem: 0<|tau|<=1/2 suffices to exclude nonzero energies aliasing to unit
   phase. The result is about unit-phase eigenmodes, not a constructed local
   discrete-time walk or all possible quasienergy band phenomena.

The original DetuningMass.hop_products rational-algebra API is retained as a
wrapper around a generalized characteristic-zero field proof. No new physical
proof axiom or numeric fit was introduced.

## Remaining limits

The generic branch theorem constrains every real-energy eigenpair. The new
ConcreteFermion and ConcreteSpectrum modules now give an explicit Hermitian
example, an exact four-dimensional zero kernel, and two distinct squared-energy
roots each of algebraic multiplicity four. See CONCRETE-SPECTRUM.md. Signed
energy counts and physical species/channel assignment remain open.

The admissible time-step bound is a sufficient mathematical condition, not a
selection of the physical tick. Matrix-exponential unitarity and strict finite-
stencil locality are different requirements. The physical scalar link/detuning
map, interaction representation, shared velocities and numerical coupling
normalization remain open.


## Final verification

Complete check.sh passed: 3354 build jobs and 274 PMAction declarations audited.
Only propext, Classical.choice and Quot.sound are permitted. The complete
updated manuscript compiled with its actual bibliography. Source checks found
no missing cross-references or citation keys; the acknowledgments still match
the pre-cleanup source. HEAD remains 54082a8, with no merge/reset/commit.


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
