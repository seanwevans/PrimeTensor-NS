# Kinetic-only disjoint annular clocks and extended physical H3 costs

Base HEAD: `ff15d43488a4b054c54e441b71d9a8df1cf08f43`.

## Purpose

The preceding `ThirdFullKineticNaturalAnnularLocalWitness244` supplies, on
an arbitrarily high cofinal H3-dissipation diagonal under failure of an H3
terminal trace, a separate physical finite-annulus window for each natural
frequency index. Its actual width is

    delta_n = min((T - tau_n)/4,
                  (M_n/4)/(2*(L_{N_n}(E0)+L_n(E0)+1))) > 0.

At every time in the window, the actual physical annular dissipation exceeds
`M_n/4` and is bounded by the full physical H3 dissipation. The original
local certificate also contains the actual ordinary finite-band time
integral charge and the midpoint-clock / kinetic-rate alternative.

## Disjointness and exact preservation

`thirdFullPhysical_noH3Trace_kineticDisjointAnnularWindows244` uses the
already proved `h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244`.
The strictly increasing selector `v` satisfies

    tau(v(k)) + delta(v(k)) < tau(v(l))     for k < l,
    tau(v(k)) -> T,
    k <= v(k).

It retains the original `N(v(k))`, `M(v(k))`, `delta(v(k))`, and entire local
annular kinetic witness certificate. No endpoint is moved and no interval is
shortened. The underlying no-H3-terminal-trace assumption is NOT strengthened
to absence of a physical L2 trace.

## Extended full physical cost without terminal L1

For each separated window let `D(r)=velocityH3DissipationAt(u,r)`, then

    ofReal(M_{v(k)}/4) * ofReal(delta_{v(k)})
      <= lintegral_{(tau(v(k)),tau(v(k))+delta(v(k))]} ofReal(D(r)) dr.

The proof reuses the established exact constant-window formula
`h3Critical_extendedConstantWindow_eq_heightWidth` and nonmeasurable
pointwise extended integral monotonicity
`h3Critical_extendedWindowCost_of_pointwiseFloor`. Both sides are ENNReal.
An arbitrary finite sum of these inequalities holds. The result **does not**
claim an upper bound on the total terminal dissipation, nor does it assert
that the finite sums diverge. A further disjoint-set integral union theorem
would be needed to compare this finite sum directly with the one global
extended terminal integral; that is not claimed in this patch.

## A finite extended physical-budget frequency test

On *any* actual kinetic local annular witness, if the full extended cost of
its one half-open time window is at most `ofReal C`, with `C >= 0`, then

    (T-x)*(M/2) <= 16*C
        OR
    (M/2)^2 <= 8*(L_N(E0)+L_n(E0)+1)*C.

This follows by translating the established extended height-width bound
back into the real inequality `delta*M/4 <= C`, and then applying the exact
scalar secondary clock/rate alternative. No integrability of full H3
terminal dissipation enters this argument.

Given a proposed finite outer cutoff n0, if the clock branch is excluded
and the extended budget is too small to pay the finite kinetic-rate sum,

    16*C < (T-x)*(M/2),
    8*(sum_{j=0}^{n0}L_j(E0)+L_n(E0)+1)*C < (M/2)^2,

then `n0 < N` for the **actual selected** outer cutoff. These are visible
conditional inequalities, not automatically asserted for cofinal indices.

## Limits

No global H3 continuation or endpoint tightness is obtained. Even with
genuine disjointness, positivity of each window cost does not guarantee
divergence of their sum. The moving outer cutoff and the possible rapid
shrinking of selected widths remain the principal hard analytic obstacles.

The Lean patch has static registration checks; successful Lean compilation
must be established with the pinned project toolchain.
