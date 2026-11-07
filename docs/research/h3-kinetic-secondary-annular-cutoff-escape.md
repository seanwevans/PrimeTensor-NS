# Cofinal secondary natural annular kinetic clock and outer-cutoff escape

**Base:** `3785f9dee9bfb21450be838f448fcfb3782862f9`.

## New PDE consequence

The earlier high-radial cofinal ledger fixes the original two secondary
observation times `zState,zSource` and secondary cutoff `J2` before a lower
natural Fourier radius `n+1` and demanded height `M` are supplied. Under the
same active deep-excess physical two-slice gate, one ORIGINAL observation
`x` has `D_high,n+1(x)>2M`.

At that **same** time, the exact physical Fourier radial partition and
pointwise high-tail convergence select an outer natural cutoff `N+1` with
`D_high,N+1(x)<M/2`. Hence the actual finite annulus has

    D_[n+1,N+1](x) = D_high,n+1(x)-D_high,N+1(x) > 3M/2 > M.

By the compiled kinetic-only finite-annulus PDE rate theorem (previous commit),
let

    E=velocityH3Energy0At(u,b)
    L_j=thirdFullPhysicalKineticLowBandDissipationRate244(j,E)
    Lambda=L_n+L_N >=0
    delta=min((T-x)/4, (M/2)/(2*(Lambda+1))).

The actual physical Navier--Stokes evolution establishes

    0 < delta, x+delta<T,
    M/2 < D_[n+1,N+1](r) <= D_H3(r) for r in [x,x+delta],
    delta*M/2 <= B = integral_m^T D_H3(r) dr.

Since original secondary observations lie in
`[s,s+(T-s)/2]`, the existing scalar midpoint-clock lemma gives

    (T-s)*M <= 16 B   OR   M^2 <= 8*(L_N+L_n+1)*B.

No new full-H3 source/state maxima are used in this certificate. `N` is
selected after the fixed inner radius and physical spike height; it is not
assumed bounded or constant along the terminal sequence.

## Quantitative frequency escape

For a proposed finite cutoff `n0` define the finite kinetic rate ceiling

    S_n0(E) = sum_{j=0}^{n0} L_j(E).

The established rate nonnegativity implies `L_N <= S_n0(E)` if `N<=n0`.
Thus **if** the clock branch is excluded and the actual terminal budget obeys

    16 B < (T-s)*M,
    8*(S_n0(E)+L_n(E)+1)*B < M^2,

then the selected outer frequency necessarily satisfies `n0<N`.
This is a real, quantified cutoff-escape consequence; it does **not**
assume any uniform bound on the moving outer frequency and does not assert
these additional inequalities hold automatically for every cofinal witness.

## Cofinal bookkeeping and scope

`ThirdFullLateRetainedPrimarySecondaryNaturalKineticAnnularCofinalLedger244`
retains the prior high-radial cofinal ledger verbatim as its first component,
including original first-window disjoint charges and time/frequency escape.
The second component upgrades the same two-slice physical branch for each
natural lower cutoff and positive height. The no-H3-trace endpoint theorem
reuses the prior selected minimal-crossing sequence and preserves its
original tail-dissipation limit. It does not sum new annular windows because
they may overlap previously charged physical windows.

The ancestor endpoint theorem also assumes both failure of a terminal H3
trace and finite terminal H3 dissipation. Those assumptions alone are not a
proof of global continuation, and related no-physical-L2-trace plus finite
dissipation hypotheses have separately been shown incompatible. The new
nonvacuous mathematical content is the local kinetic charge and its necessary
frequency-escape implication under the stated explicit clock/budget tests.

The Lean file is source-only pending compilation on the pinned project
Lean/mathlib toolchain; no `sorry`, `admit`, or new axiom is intended.
