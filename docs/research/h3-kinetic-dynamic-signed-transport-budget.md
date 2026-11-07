# Signed physical H³ energy accounting on exact kinetic annular PDE windows

**Base:** `527d2641ca0c6d2f7ba407c9b709d308b3006edb`.

## What the prior theorem does and does not say

On genuine disjoint physical windows `[t_k,t_k+δ_k]` selected by the kinetic-only PDE persistence construction, the accepted `FullThirdSolenoidalTerminalProfileKineticDynamicRawWindowTransport` theorem keeps the annular viscous floor `D_3(s)>M_k/4`, shows the raw Fourier kinetic mass in precisely that annulus vanishes uniformly over *each entire window*, and derives vanishing **absolute** physical projected-momentum-source L¹ action under finite ordinary full-H³ dissipation. It does not control the signed cubic nonlinear H³ transport, which differentiates the velocity and is not dominated by the unweighted source action without additional information.

## Integrated exact signed energy budget

The repository already proves the actual physical H³ balance at every strict energy-class time:

```
(velocityH3EnergyAt u)'(s) + 2 * velocityH3DissipationAt u s
    = -velocityH3TransportDerivativeAt u s.
```

It also proves automatic **compact strict-time** derivative and signed-transport interval-integrability assuming finite ordinary full-H³ dissipation, with an integral version of the exact balance. Apply this to each *unchanged* kinetic-selected interval and combine it with the actual `D_3(s)>M_k/4` floor and integrated positivity:

```
2 * δ_k * (M_k/4)
  <= E_3(t_k) - E_3(t_k + δ_k)
     - integral_[t_k,t_k+δ_k] Transport_3(s) ds.
```

This is an integrated statement about the **genuine signed physical H³ transport**. It is not a surrogate for a source maximum, unsigned cubic norm or projected momentum action.

Define `q_k = δ_k*(M_k/4)` (positive). A scalar rearrangement proves the sharp, exhaustive integrated alternative:

```
q_k <= E_3(t_k) - E_3(t_k+δ_k)
    OR
q_k <= - integral_[t_k,t_k+δ_k] Transport_3(s) ds.
```

If less than one full charge is drained from H³ energy, the **negative signed transport integral** must pay at least a full viscous window charge. There is no claim that this amount is uniformly positive independently of `k`; the accepted finite-dissipation theorem says `q_k -> 0`. Neither arm is ruled out by raw kinetic tightness.

The same actual window retains the pointwise signed/Riccati alternative:

```
E_3'(s) + M_k/2 < -Transport_3(s)

E_3'(s) <= -M_k/4  OR
M_k/4 < K * sqrt(E_3(s)) * E_3(s)
```

for every `s` in its original closed window. This does **not** assume that `E_3'` is nonnegative or that `Transport_3` has one fixed sign.

## Same-witness physical conclusion

The final theorem reuses the complete existential result from `thirdFullPhysical_noH3Trace_kineticDynamicRawWindowConcentration244` and appends the signed pointwise and integrated budgets. Thus it preserves, on one and the same sequence: strict cofinality, exact positive kinetic PDE widths, natural inner and outer radii, disjointness, global extended H³ dissipation charge packing, vanishing absolute physical projected-source L¹ action, uniform raw kinetic tightness, normalized critical-eighth carrier collapse, and the new signed drain/injection alternative.

## Unresolved mathematical obligation

A genuine lower bound on the sum of the negative signed flux charges, or an upper bound for differentiated transport in terms of vanishing raw kinetic mass and a usable higher-frequency moment, is still missing. Finite disjoint viscous cost and source L¹ decay by themselves do not preclude either the drain or the replenishment alternative. This is not a Navier–Stokes regularity theorem.

## Lean declarations

- `thirdFull_scalar_doubleViscousCharge_signedDrainOrFlux244`
- `thirdFullPhysical_kineticWindow_signedIntegratedBudget244`
- `thirdFullPhysical_noH3Trace_kineticDynamicSignedWindowObstruction244`

No `sorry`, `admit` or new axioms are introduced. A pinned Lean 4/mathlib compilation is required to establish elaboration; static audits are not a substitute.
