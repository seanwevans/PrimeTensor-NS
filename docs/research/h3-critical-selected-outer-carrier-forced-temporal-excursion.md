# Selected outer carriers: rate-free temporal excursions and physical-state movement

Local base: `86d2d8751` (`force selected outer H3 carrier temporal rate amplification`). This package imports the committed rate-amplification module but does **not** assume any of its hypothetical temporal Lipschitz bounds. The remote GitHub installation did not yet expose this local commit when the package was prepared; verify its prefix in the guarded installer.

## Genuine new mathematical step

The earlier physical instantaneous theorem establishes

    119 * margin * sigma^6 <= 80 * D_H3(s)

where the selected kinetic excess is at least `margin` and the *exact* nonlinear annular Young-width deficit is nonnegative. The integrated-window theorem gives the same inequality integrated whenever the excess and deficit persist throughout a right-time interval.

Fix one strict physical snapshot `x`, a selected annulus with `rho>0`, `sigma>=2 rho`, excess `margin>0`, and actual deficit `G(x)>=2 epsilon>0`. Set

    A(t) = ((rho^2+sigma^2)/2) * actualSharpHighpassMass(t,rho)
    G(t) = actualAnnularKineticDeficit(b,t,rho,sigma)
    V(x) = integral_x^T D_H3(t) dt.

For any `delta>0`, `x+delta<T`, if

    V(x) < delta * (119 * margin * sigma^6 / 160),

there must be a *real physical time* `s in (x,x+delta]` with either

    A(x)-A(s) > margin/2,

or

    G(x)-G(s) > epsilon.

**Proof**: otherwise the two genuine observables preserve a half-margin and nonnegative deficit for all `t in [x,x+delta]`. Apply the existing integrated physical viscous-charge theorem with half the original margin. Its lower bound contradicts the strict upper bound on `V(x)`. No continuity, derivatives or assumed time rates enter this argument. The left endpoint is excluded because neither strict drop can occur at `s=x`.

With `delta=(T-x)/2`, this becomes the sharp half-tail alternative whenever

    V(x) < (119/320) * margin * sigma^6 * (T-x).

For cofinal `x_k -> T`, finite full physical H3 dissipation forces `V(x_k)->0`. Thus if the *additional, explicit* frequency-time scale hypothesis

    eventually c <= margin_k * sigma_k^6 * (T-x_k), c>0

holds, then the half-tail alternative occurs eventually for the entire cofinal family. Importantly, the scale hypothesis is **not** shown to follow from Navier--Stokes or from finite dissipation.

## Physical transfer: actual states, not proxies

By the existing real physical sharp-cutoff two-time variation inequality, a kinetic-mass drop gives

    margin < (rho^2+sigma^2) * ||U(s)-U(x)||_L2 * (||U(s)||_L2+||U(x)||_L2),

for `U=h3AuditInitialOldPhysicalHilbertTotal hH3`. The positive time gap may be arbitrarily short, but it cannot support negligible L2 motion relative to the indicated spectral scale.

On the second arm, the original **exact** Young-width deficit polynomial gives

    epsilon/2 < |M(s)-M(x)| * |exact two-time slope|
       OR
    epsilon/2 < M(s) * |Young(s)-Young(x)|.

The previously proven sharp mass and nonlinear Young-width two-time inequalities further bound these terms respectively by physical L2-state increments and original H3 spectral-state increments times exact finite-radius coefficients. This isolates the actual PDE analytic task: establish a sufficiently strong radius-dependent forward time modulus that rules out both physical-state alternatives at the necessary scale.

## Lean results

- `thirdFullPhysical_selectedOuterMargin_lowTail_forcesRightExcursion244`
- `thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesExcursion244`
- `thirdFullPhysical_selectedOuterMassDrop_forcesPhysicalL2Increment244`
- `thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesVelocityOrDeficit244`
- `thirdFullPhysical_selectedOuterDeficitDrop_massOrYoung244`
- `thirdFullPhysical_selectedOuterDeficitDrop_forcesStateMovement244`
- `thirdFullPhysical_cofinalSelectedOuterMargins_forceVelocityOrDeficit244`

No proof placeholders or new axioms are introduced. Compilation has not been checked locally against the full pinned project; the run script must compile and audit the module before committing.
