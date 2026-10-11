# Initial kinetic escape excluded by dyadic time averages

Parent checkpoint: `e199bd26` (`derive initial kinetic escape or weak uniqueness alternative`).

New Lean module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialDyadicKineticAverageRelativeEnergy.lean`.

## Mathematical content

The existing path class gives a physically exact kinetic energy `E₀(t)` that is
nonincreasing on the strict positive-time interval `(0,T)`. Its derivative
identities give positive-time continuity. For any `t` in `(0,T)`:

    E₀(t) * (t/2) <= integral from t/2 to t of E₀(s) ds.

Thus any finite uniform dyadic average bound

    integral from t/2 to t of E₀(s) ds <= B * (t/2)

for all `0<t<b` implies `E₀(t) <= B` on `(0,b)`. This is a direct,
non-circular way to exclude the kinetic-escape branch from the preceding
dichotomy without postulating initial right kinetic convergence or an initial
kinetic energy balance. No integral through zero is used.

The existing initial compact weak-test comparison and actual physical zero-jet
and upper H³ traces then follow, **conditional on** the separately stipulated
old/selected epsilon-vanishing relative-energy comparison and initial datum.
The independent terminal actual-vorticity strong-H³ endpoint remains.

## Audited dependency boundary

This patch **does not** derive the uniform dyadic average from
`LoggedPreterminalH3PathAdmissible` alone. It is a new, concrete and quantified
PDE-side sufficient condition, not the elimination of an analytic assumption.
It also does not derive the vanishing residual inequality or prove unconditional
Navier--Stokes regularity.

## Local validation

Run `lake env lean` on the new module, then `lake build`, regenerate the source
index, and execute the repository baseline audit. The assistant environment
has no `lean`/`lake` executable, so successful Lean elaboration must be
confirmed by the local run before pushing.
