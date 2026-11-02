# Half-height annular dissipation localization on synchronized endpoint windows

**Base:** `efae4951` (eighth-power active endpoint frequency barrier).

For the same cofinal selected source and spectral maxima and internal physical
persistence windows, let

- `H(k) = R(k)^2 ε(k)^2 / 8`, the positive endpoint threshold;
- `E0 = velocityH3Energy0At u b`, the physical kinetic anchor;
- `Q(k) = N(k)+1`, the capturing finite radial frequency;
- `P(k) = L(k)+1`, any independently proposed lower frequency;
- `D_low(P,t)` the actual low-radial spectral H³ dissipation below P.

The verified kinetic anchor bound and exact radial polynomial inequality imply
`D_low(P,t) <= 4 E0 P^8` at each strictly preterminal time.

If the spike branch is active (`η(k) ≠ 0`) and
`8 E0 P(k)^8 < H(k)`, then for every physical time t in its previously
selected persistence interval `[p(k),p(k)+η(k)]`,

    H(k)/2 < D_low(Q(k),t)-D_low(P(k),t) <= D_full(t).

In particular `L(k)<N(k)`: the capturing finite band must include a genuine
annulus above the lower cutoff. The result is an actual physical time-window
frequency localization, rather than only an endpoint amplitude inequality.

The original four-way alternative (non-spectral branch, projected source PDE
clock, anchor viscous spike, or internal finite-band spike) is preserved
unchanged for the **same witnesses**. No terminal `IntervalIntegrable` premise
is needed in this patch. If finite terminal dissipation is additionally
available, previous disjoint-window results furnish the finite integral budget.
The proof does not provide a lower window width, uniform modulus in time,
or terminal continuation.

## Registered theorems

- `h3Critical_scalar_twiceLowerBandCeiling_forces_halfAnnularGap`
- `h3Critical_physicalLowRadialSpike_forces_halfHeightAnnulus`
- `h3Critical_noL2Trace_cofinalFivefold_activeAnnularLocalization`
