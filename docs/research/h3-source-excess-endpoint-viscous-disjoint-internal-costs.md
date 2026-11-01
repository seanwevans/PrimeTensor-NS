# Fivefold H³ source windows: disjoint internal endpoint-viscous costs

**Base:** `50712271` — accepted finite-band persistence of actual physical
H³ viscous spikes at the attained spectral maximizers.

## The geometric gap

The predecessor shows that a strict spike of full H³ dissipation `D(s)` at
an attained spectral maximizer has a positive right-hand interval with a
finite-band lower bound and an extended physical dissipation integral.
But its right-hand interval may extend beyond the original source window;
even if the original source windows are pairwise separated, these new
right-hand intervals need not be. Pointwise spike costs cannot simply be
summed across overlapping time intervals.

The stronger original theorem
`h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts`
actually returns **strict separation of the full source windows**:

    t(v k) + w(v k) < t(v l)             (k<l).

This information was omitted from some later cofinal theorem statements,
which only exposed disjointness of the shorter calibrated subwindows.

## New internal finite-band persistence

Suppose `x in (a,T)`, `w>0`, `x+w<T`, `s in [x,x+w]`, and `H<D(s)`.
The accepted fixed-time radial-tail vanishing and exact dissipation
partition yield a finite cutoff `N+1` with

    H < D_low(N+1,s).

`D_low(N+1,.)` is continuous on the strict physical energy interval.
Choose a local radius `eta0>0` where `H<D_low` and a smaller positive
`eta = min(eta0/2,w/4)`. If `s<=x+w/2`, use the right-hand window
`[s,s+eta]`; otherwise use the left-hand window `[s-eta,s]`.
Both possibilities remain **inside the original source window**, including
when the maximizing time equals the source window's right endpoint.

For a selected start `p`, the formal conclusions are

    0 < eta,    x <= p,    p+eta <= x+w,
    H < D_low(N+1,r) <= D(r)       for every r in [p,p+eta],
    ofReal(H)*ofReal(eta) <= ∫⁻_(p,p+eta] ofReal(D(r)) dr.

No continuity of the full unbounded-gradient H³ dissipation is assumed.

## Cofinal disjoint selection with zero-width nonspike slots

On the same fixed-component cofinal fivefold source construction, choose
attained maxima of the actual projected momentum source and spectral state
inside each original source window. For arbitrary strictly positive cutoff
and threshold profiles `R(k)>0` and `eps(k)>0`, set

    H(k) = R(k)^2 * eps(k)^2 / 8.

For each k, **if** `R(k)^2 eps(k)^2 < 8 D(sState(k))`, select a positive
internal finite-band window with floor `H(k)`. Otherwise select `eta(k)=0`
and an empty integration window. Thus no assumption that the viscous spike
branch occurs at every index is introduced.

The new cofinal theorem retains:

- the original fixed Fourier source component and fivefold source-excess
  plus high-radial dissipation floors on every full source window;
- strict separation of the **original** windows;
- the original summed enhanced full-H³ dissipation cost;
- attained source and spectral maxima;
- internal spike subwindow containment and strictly separated subwindows;
- the **additional** finite summed integrated costs

      sum_{k<m} ofReal(H(k))*ofReal(eta(k))
       <= sum_{k<m} ∫⁻_(p(k),p(k)+eta(k)] ofReal(D(r)) dr.

The new costs are on nonoverlapping physical time intervals, not merely
formal sums of possibly overlapping right neighborhoods. Nothing adds the
original and new sums as if they were disjoint from *each other*, and the
new eta widths may tend to zero. A total terminal viscous budget or a
terminal-uniform lower bound on these new widths remains unproved.

## New Lean declarations

- `h3Critical_fullViscousSpike_has_internalFiniteBandCost`
- `h3Critical_internalWindows_strictlySeparated`
- `h3Critical_internalWindows_finiteCostSum`
- `h3Critical_noL2Trace_cofinalAttainedMax_disjointConditionalViscousCosts`

Four `#check` and four `#print axioms` registrations. Source is a proof
candidate until compiled using the repository's pinned Lean/mathlib toolchain.
