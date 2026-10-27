# The final Fourier shell at the canonical first crossing

Base commit: `def93c2e`, coupling the minimal ninth/eighth PDE cutoff to its own
raw Fourier annular kinetic mass on the same physical disjoint witnesses.

## The missing localization

Let `R=n+1`, and let the least integer `N>=n` satisfy

    D_low(N+1,t) - D_low(R,t) > 3*R^3/4.

For every earlier integer `n<=m<N`, the difference stays <= `3*R^3/4`.
In particular, `N>n`, and hence it has an integer predecessor `m=N-1`
with `n<=m`. Its last frequency shell `[m+1,N+1)` has dissipation jump

    J = D_low(N+1,t) - D_low(m+1,t) > 0.

More precisely, write the *overshoot*

    omega = D_low(N+1,t) - D_low(R,t) - 3*R^3/4 > 0.

First-crossing minimality implies `omega <= J`. It DOES NOT imply
`J>=c R^3` for a fixed c>0: the crossing may barely exceed its threshold.
That distinction prevents a spurious kinetic-mass lower floor.

## Actual physical Fourier kinetic mass on this last shell

The already-proved literal-band localization is reusable at `m+1` and
`N+1`. Its eighth-order multiplier bound gives

    J <= 4*(N+2)^8*K_raw([m+1,N+1), t).

Combining the inequalities:

    0 < omega <= J <= 4*(N+2)^8*K_raw([m+1,N+1),t).

Thus the raw Fourier kinetic mass of the **last single integer shell** is
strictly positive. This is a genuinely shell-local bound, not an estimate
for the entire original annulus `[R,N+1)` or a global L2-energy surrogate.

The final Lean theorem transfers this to actual strictly interior
no-strong-terminal-L2-trace first-crossing snapshots. That cofinal
selector is the same canonical first-crossing construction used earlier
for the quadratic-sharp clocks. The present module does not newly export
ninth/eighth scale separation on that cofinal selection; joining the
shell overshoot to those *exact disjoint-window* witnesses is a separate
proof step.

## What is still missing

Even when the minimal outer cutoff grows superlinearly beyond `R^(9/8)`,
`omega` may tend to zero arbitrarily fast. No uniform last-shell raw kinetic
mass lower bound, no upper bound on outer radius, and no contradiction with
finite physical L2 or time-integrated H3 dissipation is claimed.

## Verification

The ZIP is archive-checked and statically validated. The user must run
`lake env lean` on the new module, `lake build` for that module, index
and audit checks, and the whole repository build before committing.
