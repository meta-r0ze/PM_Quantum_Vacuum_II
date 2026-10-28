# Exact vacuum preservation in the local update

## Constraint and correction

The original WilsonSplit coin exp(-i tau H(0,3)) gives the correct first-order
Hamiltonian but the diagnostic does not preserve its exact vacuum eigenphases
at nonzero tick size. The correction is driven by preserving the known zero
modes, retaining exact unitarity, finite spatial propagation and the same tangent.
No measured constant or fitted coefficient is used.

Let W=H(0,0), beta8=diag(beta,beta), and
R_beta(tau)=cos(tau) I + i sin(tau) beta8. Define

    Q_new(tau) = exp(-i tau W) * (R_beta(tau)†)^3,
    U_new(tau) = onsite(Q_new(tau)) * R_0(tau) * R_1(tau) * R_2(tau).

The directional factors are the previously proved neighboring-site factors.
At zero momentum all three are R_beta, and their inverse cube cancels exactly.
The factor three counts the three existing spatial factors; it is not a fit.

## Checked results

VacuumSplit.lean proves:

- the new coin and complete finite-lattice update are unitary for every real
  tau and every periodic lattice size N;
- the total squared amplitude is conserved;
- the previous exact spatial support/locality contract is retained. Together
  with PropagationBounds this gives at most 27 input sites per tick;
- origin_update: U_new(0,tau)=exp(-i tau W), exactly for every real tau;
- vacuum_preserved: W*v=0 implies U_new(0,tau)*v=v, exactly for every real tau.

The last proof uses P0=diag(Pplus,Pminus). Lean checks W*P0=0 and that P0
fixes every vector of the explicitly characterized vacuum kernel. An exponential
semiconjugation identity proves exp(-i tau W)*P0=P0. Thus it is a proof about
all vectors in that kernel, not a floating-point check of four basis vectors.

VacuumGenerator.lean proves the on-site decomposition W+3 beta8=H(0,3),
U_new(k,0)=I, and the actual derivative

    d/dtau U_new(k,tau)|tau=0 = -i H(k,delta_W(k)).

VacuumUniform.lean connects the symbol calculation to the actual finite-lattice
matrix. For every N, tau and kernel vector v, the spatially uniform state
psi(x,a)=v(a) is fixed by the complete lattice update. This includes all the
known four independent internal vacuum modes on a nonempty lattice.

All three modules are imported by PMAction.lean and covered by AuditStrict.

## Remaining limits and next priority

Preserving the known four modes is not an exhaustion theorem for the update's
fixed space. At tau=0 the entire state space is fixed, so an exact-four claim
cannot hold for unrestricted ticks. Next prove a suitable nonzero tick range
and rule out additional unit eigenphases, both at the origin and away from it.
The Hamiltonian's old no-alias theorem cannot be applied automatically to this
noncommuting product. Many-tick convergence/error bounds remain open.

These are constructions within the already specified Clifford/Wilson model.
They do not prove unique selection of the representation, ordering or physical
clock from persistence. Gauge/scalar interactions and the physical channel and
species identification remain open. Paper III was not edited in this pass.


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
