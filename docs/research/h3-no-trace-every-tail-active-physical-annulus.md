# No-terminal-L2-trace: all-active physical cubic annuli on every tail

Base `50c72216`.

## Hard mathematical step

The existing fixed-radius physical dissipation theorem produces a genuine high-frequency H3 dissipation spike above any threshold on every strict terminal tail, with no terminal L1 hypothesis. Set the inner cutoff to n+1 and the threshold to (n+1)^3. The established canonical exact-anchor first-crossing theorem turns this into an actual finite outer cutoff N>=n, an attained physical projected momentum source envelope C, and a strictly positive exact anchored PDE annulus width delta, with t+delta<T.

At every r in [t,t+delta],

  (n+1)^3/2 < D_{<N+1}(r)-D_{<n+1}(r) <= D_3(r).

The finite annular mass is continuous on the strict physical interval, so integrating yields

  delta (n+1)^3/2 <= integral_t^(t+delta) (D_{<N+1}-D_{<n+1}) dr.

This integral is strictly positive. No uniform lower bound on delta, global summability of disjoint annuli, positive terminal kinetic limit, or finite terminal H3 dissipation is assumed. The selected annulus is active for EVERY given (tail, inner cutoff), unlike the prior synchronized multiway gate's optional annular branch.

The theorem retains the exact quadratic anchored width, the attained physical source envelope, and the spectral-anchor energy comparison. It is a necessary obstruction for a hypothetical failure of the physical strong terminal L2 trace, not a proof of Navier-Stokes regularity.

Lean declarations:
- h3Critical_noL2Trace_everyTail_activeCubicPhysicalAnnulus
- h3Critical_noL2Trace_everyTail_positiveCubicAnnularIntegral
