# Synchronize attained H³ source-clock alternatives and disjoint internal viscosity

**Base commit:** `0fc83f02` — established disjoint internal physical costs
for conditional viscous spikes at attained spectral maxima.

## The missing connection

The previous disjoint-cost theorem selects full, pairwise-separated fivefold
source windows and their attained source and spectral maxima. Separately,
the predecessor's endpoint PDE-clock theorem selects its own maxima, with no
uniqueness assertion. Its endpoint spike cannot legitimately be assigned to
the integrated-cost interval attached to a *different* maximizer.

The first new theorem, `h3Critical_fivefoldWindow_fixedMaximaPhysicalFourWay`,
accepts prescribed maximizing observations `sSource,sState` whose norms
bound the original full source window. It runs the accepted calibrated
fivefold physical PDE source theorem **with those fixed observations**, using

    C = ||ProjectedMomentumSource(sSource)||,
    E = ||H3WeightedSpectralState(sState)||.

The returned exact radius/width coefficients are

    A = 3 + C_L (||U(t)||+||U(sState)||),
    B = 12 ||ProjectedMomentumSource(sSource)||² + 2(D(t)+H).

The already proved Riccati, compression, cutoff, physical spectral/source,
instantaneous viscosity, and enhanced floor alternatives are retained.
No new independently selected maxima are involved.

## Synchronized cofinal theorem

`h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts`
starts with `h3Critical_noL2Trace_cofinalAttainedMax_disjointConditionalViscousCosts`
and retains its **same** fixed Fourier source component, full fivefold
source windows, strict full-window separation, attained `sSource(k)` and
`sState(k)`, disjoint internal endpoint intervals `(p(k),p(k)+eta(k)]`, and
both physical dissipation-cost sums.

It invokes the fixed-maxima quartic gate on that precise source window.
For each specified positive cutoff `R(k)` and threshold `eps(k)`, if

    3 + 4*C_L*eps(k) <= max(1,sigma(v(k)))+1,

it concludes, for the *same selected witnesses*, that either:

- one of the accepted non-spectral-excursion outcomes holds;
- the finite-band physical projected-PDE clock pays

      eps(k)^2 <= 6 K(R(k)) C(k)^2 w(v(k))^2;

- actual full H³ viscosity at the original peak pays

      R(k)^2 eps(k)^2 < 8 D(t(v(k)));

- or the actual physical viscosity at the **same** `sState(k)` pays the
  positive internal finite-band floor

      H(k) = R(k)^2 eps(k)^2 / 8 < D_low(N(k)+1,r) <= D(r)

  for all `r∈[p(k),p(k)+eta(k)]`, with `eta(k)>0`.

The internal intervals are pairwise separated by the original full-window
separation, and their finite extended Lebesgue costs satisfy

    sum_{k<m} ofReal(H(k))*ofReal(eta(k))
       <= sum_{k<m} ∫⁻_(p(k),p(k)+eta(k)] ofReal(D(r)) dr.

The original fivefold full-source windows have their own distinct summed
physical dissipation floor. The two families can overlap for the same k;
**their budgets are not added as though mutually disjoint**. Neither a
terminal-uniform lower bound for eta nor regularity/continuation follows.

## Lean declarations and status

- `h3Critical_fivefoldWindow_fixedMaximaPhysicalFourWay`
- `h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts`

The registrar inserts two checks and two axiom inspections. Compilation in
the pinned local Lean/mathlib toolchain and full baseline audit are required.
