# One joint kinetic--Schwartz sequence and scalar positive-time increments

Parent commit: `a10d5fe6` — derive initial physical trace from cofinal
kinetic sequence and Schwartz data.

## New analytical frontier

The sampled energy condition from the previous checkpoint is retained,
but Schwartz matching is now given only along ONE COMMON right-zero
sequence. No full weak right trace is supplied. A test-dependent
L¹ scalar increment equation only for STRICTLY POSITIVE times,

    <F(t), Phi> - <F(s), Phi> = integral_s^t g_Phi(r) dr,

manufactures a finite right limit for each test and identifies the
integration constant against the sampled weak initial value.

The generic scalar theorem upgrades these positive-time increments
and the weak matching sequence to the exact anchored scalar FTC.
The old Schwartz-FTC strong trace and cofinal-energy theorems then
supply the actual physical initial trace and the kinetic-energy trace.
The scalar sources may depend on the test and have no uniform in-test
integrability bound. Pointwise HasDerivAt is NOT assumed.

Independently, the joint sampled kinetic upper limit plus Schwartz
weak convergence forces strong physical L2 convergence ALONG THE
SAMPLED SEQUENCE even without temporal scalar increment assumptions.
It is the scalar increments that upgrade the sampled strong trace to
full right-time strong continuity.

## Public API

- `h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence`
- `H3AuditInitialSchwartzScalarPositiveIncrementsOn`
- `h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_jointSequence`
- `h3Audit_initialJointKineticSchwartzSequence_sampledStrongTrace`
- `H3AuditInitialJointKineticSchwartzIncrementData`
- `h3Audit_initialJointKineticSchwartzIncrements_physicalAndKineticRightTrace`

## Remaining obligations

The existence of a common kinetic/weak initial sequence and positive-time
Schwartz scalar increment equations are STILL INDEPENDENT initial-value
premises. The open-time H3 path does not imply the sampled initial
compatibility and cannot by itself fix the integration constant.
Terminal actual-vorticity strong H3 remains a separate issue;
no unconditional 3D Navier--Stokes smoothness is proved.

## Build

After extraction and root/contracts registration, run the REQUIRED
`python3 proof/generate_index.py`, followed by `--check` and
`proof/check_fragment.py --all` before any Lake build. The regenerated
`proof/order.txt` must be included in the commit. Compile module,
root library, Contracts, and full default build before pushing.
