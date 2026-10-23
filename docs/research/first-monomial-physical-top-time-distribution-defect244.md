# Physical time-distribution defect: homogeneous derivative reduction

Base: `186cd276` on `master`.

The actual physical momentum regular distribution and the source primitive
regular distribution are now both well defined on each strict positive-time
interval. The previous checkpoint proved, unconditionally,

    ∂_t T_J = T_R,
    J(t) = ∫_a^t <phi,R(s)> ds.

Define the distributional difference `D_phi = T_M - T_J`. By linearity,

    ∂_t D_phi = 0   iff   ∂_t T_M = T_R

for each compact solenoidal spatial test phi. The new theorem is the precise
Lean equivalence of those two statements.

**Neither direction supplies the original PDE time-distribution identity.**
`OneComponentInitialActualPhysicalSourceIdentification.lean` proves that the
space integral of the *pointwise* temporal derivative is the projected source
pairing. Identifying this spatial integral with the distributional derivative
of `t ↦ <phi,U(t)>` is still a genuine interchange/weak formulation task.

Even after obtaining `∂_t D_phi = 0`, one must prove the connected-interval
kernel result: any regular distribution with zero time derivative is locally
constant, hence constant on `(a,b)`. Continuity then gives

    M_phi(t) - M_phi(a) = ∫_a^t <phi,R(s)> ds.

Only after that scalar conclusion, compact solenoidal weak-test density and
Leray-fixedness can close the physical Hilbert FTC defect. No missing
regularity, L² pressure gradient, or distributional uniqueness theorem is
introduced as an axiom in this module.

This ZIP has not been Lean-compiled in the assistant's environment. Run the
pinned local `lake env lean` and `lake build` checks before committing.
