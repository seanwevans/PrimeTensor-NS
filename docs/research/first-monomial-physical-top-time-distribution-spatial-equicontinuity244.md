# Signed physical momentum from spatial equicontinuity

**Base:** `49901cee` — reduce signed PDE domination to compact temporal oscillation.

The old Navier--Stokes PDE supplies two separate continuity properties of its
signed momentum forcing F_j(t,x) = ∂ₜu_j(t,x): time continuity at each fixed x
and spatial C1 at each fixed t. Those do **not** yield uniform time continuity
on a compact test support automatically.

## New bridge

If on a neighborhood of each elapsed time s the signed forcing has a **single
spatial Lipschitz constant** L on the compact test support K, then the already
proved pointwise-in-time continuity upgrades to uniform temporal oscillation:

  sup_{x in K} |F_j(t,x)-F_j(s,x)| → 0 as t→s.

Proof: choose δ=ε/(8(L+1)), cover K by finitely many δ-balls, use continuity
at their finitely many centers, and estimate F_j(t,x)-F_j(s,x) by three terms
using two spatial Lipschitz estimates and one center-time estimate. The
spatial Lipschitz assumption is retained explicitly and is strictly local to
compact test supports and the observation time. We do not assume full joint
spacetime continuity.

This closes a new PDE-to-time-distribution sufficient-condition chain:

  local spatial equicontinuity + old pointwise temporal continuity
    → signed compact temporal oscillation
    → signed compact temporal domination
    → physical Hilbert strong derivative
    → genuine physical momentum distribution.

A nonzero actual physical FTC defect implies the failure of the stated
spatial-equicontinuity condition on some interior time.

## Open obligation

The H3 path and spatial C1 regularity yield a finite Lipschitz constant at
any single fixed time on suitable compact convex hulls, but do not presently
yield one bound uniform over a time neighborhood. Such a bound would follow
from suitable additional uniform higher-derivative estimates; it cannot be
inferred from separate continuity alone. The theorem does not establish
unconditional Navier--Stokes continuation.

## Validation

`lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSpatialEquicontinuity244.lean`

`lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionSpatialEquicontinuity244`

`python3 proof/generate_index.py`
