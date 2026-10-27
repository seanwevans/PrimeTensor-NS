# Kinetic-energy bandwidth requirements at canonical cubic first crossings

Base commit: `b687fdc5` — divergent high-frequency H3 dissipation below minimal ninth/eighth cutoffs.

## Physical multiplier bridge

For the actual physical spectral state at `t`, with fixed kinetic anchor
`a < b < t < T`, the repository already proves

    lowH3Diss(Q,t) <= Q^2 * W(Q) * E0(b)
    W(Q) = 1 + Q^2 + Q^4 + Q^6.

At `Q>=0`, `Q^2 * W(Q) <= 4*(Q+1)^8`. If a canonical first crossing at
inner `R=n+1` and outer `Q=N+1` has

    3*R^3/4 < lowH3Diss(Q,t) - lowH3Diss(R,t),

and the low-radial dissipation is nonnegative, the exact physical
kinetic-bandwidth necessary condition is

    3 * R^3 < 16 * (Q+1)^8 * E0(b).

The Lean proof invokes the established anchored kinetic low-dissipation
bound, the checked eighth-power radial Sobolev weight, and the positivity
of the actual radial Fourier integral. It does not assume a global H3 bound.

## Canonical cofinal physical selection

The existing no-strong-terminal-L2-trace branch selects a least integer
outer annulus for every high-radial cubic snapshot. The new cofinal theorem
preserves the first-crossing minimality and proves the kinetic necessary
condition eventually after **every** strict kinetic anchor `b`.

This bound by itself is far weaker than the conditional forced ninth/eighth
cutoff separation: as `Q>=R`, an eighth-power RHS may already dominate a
cubic LHS. The present bridge is useful as a correct finite-band kinetic
interface, not an asserted contradiction.

## The high-H3 / kinetic-L2 distinction

A second generic theorem proves that `tail(k)->+infinity` and
`0<=kinetic(k)<=E` eventually imply

    tail(k)/(1+kinetic(k)) -> +infinity.

A physical theorem instantiates this with actual high-frequency H3
dissipation and the nonincreasing physical zeroth-order kinetic energy,
using the proved Plancherel equality and kinetic anchor. It explicitly
requires the physical sampled times to lie strictly after the anchor.
A sixth theorem applies this on the **same canonical disjoint-window**
ninth/eighth witness, with that eventual strict-time condition visible
as an implication hypothesis.

**Important:** The last physical theorem retains the already-exported
canonical disjoint-window witness. Its eventual strict-time condition
after the chosen kinetic anchor is explicit, not silently inferred from
convergence to `T` alone. Enriching that witness interface would let us
discharge this time condition rather than assuming it in an implication. Moreover, divergence of high-frequency H3 dissipation
does not imply divergence of high-frequency kinetic Fourier L2 mass.

No terminal regularity or Navier-Stokes global regularity conclusion is
claimed; full terminal H3 dissipation integrability remains a conditional
hypothesis in the earlier disjoint-window theorem.

## Verification

Register the six declarations, regenerate the source index, compile this
module with `lake env lean` and `lake build`, audit the module and full
project, and commit/push only after all checks pass. The patch environment
has no Lean toolchain, so package-level validation is not compilation.
