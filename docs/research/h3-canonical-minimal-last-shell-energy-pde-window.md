# Same-anchor minimal first crossing, last-shell kinetic mass and exact H³ PDE clock

Base: `4aafc62a`. The earlier disjoint quarter-cubic physical annuli had exact
source and clock certificates but discarded the *minimality* of the outer
integer crossing. This module makes that property part of a single Prop
certificate and selects those certificates on every terminal subtail, a
cofinal sequence and pairwise-separated disjoint windows.

At actual anchor t and integer inner n, let N be the first cutoff with

    D_(N+1)(t) - D_(n+1)(t) > 3(n+1)^3/4.

Then N=m+1 for some m>=n; all smaller j>=n have annular dissipation at
most 3(n+1)^3/4. Let A be the actual annulus dissipation at the crossing.
The shell [m+1,N+1) has *strictly positive* raw Fourier kinetic mass, with

    0 < A - 3(n+1)^3/4 <= 4(N+2)^8 M_raw([m+1,N+1),t).

The same N and physical spectral anchor carry

    (n+1)^3 < 4(N+2)^2 E_3(t),

and the same C is the attained (not enlarged) projected-source norm maximum
on [t, t+(T-t)/2]. Delta is exactly the sharp quadratic PDE selector built
from that actual C and actual spectral anchor norm. The local integral cost

    delta (n+1)^3/2 <= integral_[t,t+delta] finite annular dissipation

is retained.

The overshoot may be arbitrarily small. No uniform shell mass lower bound,
terminal full H³ dissipation integrability, or smooth continuation is asserted.
The new minimal-shell disjoint selection is not yet equated to every earlier
nonminimal selected sequence; the next result should transfer the existing
sixth/ninth energy-source alternatives to these new minimal-shell windows.

The assistant container lacks `lean` and `lake`. The run script performs
local typechecking, all-build and audit before committing.
