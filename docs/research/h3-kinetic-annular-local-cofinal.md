# Kinetic annular PDE windows without finite terminal H3 dissipation

**Base commit:** `01a83e8c831c316d46ad414ae7a5455374ae2ce1`.

## Structural correction

The previous endpoint annular charge used `IntervalIntegrable D a T` to
compare a finite annulus with the full terminal dissipation integral. That
assumption is **not** required to obtain the annular persistence radius or its
ordinary finite-band integral. For a no-trace scenario, the full terminal
integral may be infinite, and imposing finite terminal dissipation alongside
**no physical L2 trace** is already inconsistent by
`h3Critical_physicalL2_terminal_trace_of_finite_dissipation`.

We extract a local certificate that remains meaningful in the
nonintegrable case. This also avoids applying the contradictory no-L2-trace
plus finite-dissipation branch to infer frequency growth.

## Actual kinetic PDE estimate

Fix a physical kinetic anchor `b` and a strict time `x` with

    M > 0,  D_high,n+1(x) > M.

The pointwise high-tail convergence permits selecting a finite `N>=n` with

    D_high,N+1(x) < M/4.

The exact physical radial partition gives an annulus of height

    Ann[n+1,N+1](x) > 3M/4 > M/2.

Let `E=velocityH3Energy0At u b` and

    L_j(E) = thirdFullPhysicalKineticLowBandDissipationRate244 j E,
    Lambda = L_n(E) + L_N(E).

Using the compiled kinetic-only natural-annular temporal Lipschitz estimate,
choose

    delta = min ((T-x)/4) ((M/4)/(2*(Lambda+1))) > 0.

For every physical `r ∈ [x,x+delta]`:

    M/4 < Ann[n+1,N+1](r) <= velocityH3DissipationAt u r.

The finite annulus is continuous on strictly preterminal time, hence its
ordinary real integral exists on `[x,x+delta]`. It pays the explicit cost

    delta*(M/4) <= I = integral_x^(x+delta) Ann[n+1,N+1](r) dr.

The previous, already compiled scalar annular clock lemma supplies

    (T-x)*(M/2) <= 16*I
      or
    (M/2)^2 <= 8*(Lambda+1)*I.

No terminal `IntervalIntegrable D a T` is needed at any point.

## Original secondary two-slice preservation

`thirdFullPhysical_secondaryTwoSlice_kineticLocalAnnularWindow244` keeps the
original selected `zState,zSource` in their midpoint interval and uses a
physical high-radial spike at either one. It produces the same local window
certificate at that exact original time without finite terminal H3
integrability. The cutoff may be selected afterward, but the times are not
reselected.

## Local cutoff-escape implication

For any proposed maximum `n0`, write `S_n0(E)=sum_{j=0}^{n0}L_j(E)`.
For a selected window, if

    16*I < (T-x)*(M/2)
    8*(S_n0(E)+L_n(E)+1)*I < (M/2)^2,

then its actual finite outer cutoff necessarily satisfies `n0<N`.
These are **conditional** inequalities in the real finite-annulus integral
of that same window, not an unconditional bound on all frequencies.

## Cofinal no-H3-trace lift

`thirdFullPhysical_noH3Trace_kineticLocalAnnularCofinal244` uses the original
arbitrary-height diagonal theorem, with no `IntervalIntegrable D a T`
hypothesis. It retains the original cofinal observation sequence `tau`,
chooses finite `N(n)>=n` and explicit positive `delta(n)`, and carries the
new certificate at every prescribed height `M(n)>0`. The selected windows
are NOT asserted disjoint and their local charges are NOT added.

The no-H3-trace premise is distinct from failure of a physical L2 terminal
trace; no contradiction or global regularity is claimed.

## Validation status

The Lean module has no intentional `sorry`, `admit` or new axioms.
The registrar and source structure have been checked locally, but a pinned
Lean/mathlib compilation is still required in the project environment.
