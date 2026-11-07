# Finite global extended H3 dissipation: kinetic charge collapse and exact clock/rate fork

**Base commit:** `9b92f75b2efb43c3b708a118e04264e843e45f5c`.

The previous accepted theorem constructs **the same physical cofinal windows**
`[tau(v(k)),tau(v(k))+delta(v(k))]` for any prescribed positive high-radial
height profile M and strictly separates their supports. The physical full H3
extended dissipation globally dominates every finite sum of window costs:

```
sum_{k<m} ofReal(M(v(k))/4) * ofReal(delta(v(k)))
  <= lintegral_(a,T) ofReal(D_H3(r)) dr.
```

## New real summability consequence

Add the *explicit independent* finite global ENNReal budget

```
lintegral_(a,T) ofReal(D_H3) <= ofReal(C),  0 <= C.
```

Because all widths and heights are nonnegative, exact conversion of finite
`ENNReal` sums to ordinary real sums yields

```
forall m, sum_{k<m} delta(v(k)) * (M(v(k))/4) <= C.
```

The existing theorem `h3Path_nonnegativeBoundedRangeSums_summable244` therefore
proves the real series of exact kinetic height-width costs is summable and

```
delta(v(k)) * (M(v(k))/4) -> 0.
```

No ordinary full-dissipation time integral is constructed or assumed here.
Only the extended global budget is hypothesized.

## Exact kinetic-width dichotomy

The already accepted kinetic physical source transport theorem defines the
width on each ORIGINAL selected window by

```
Lambda = L_{N(v(k))}(E) + L_{v(k)}(E) >= 0,
E = velocityH3Energy0At(u,b),
delta = min((T-x)/4, (M/4)/(2*(Lambda+1))).
```

For any epsilon with `delta*(M/4) <= epsilon`, comparing the two branches
of `min` and clearing the positive denominator gives the SHARP algebraic fork

```
(T-x)*M <= 16*epsilon
  OR
M^2 <= 32*(Lambda+1)*epsilon.
```

No hidden constants are introduced. In particular, for **every** positive
`epsilon`, this fork holds at all sufficiently late retained cofinal indices,
because the real height-width charges converge to zero. Thus a finite global
extended budget forces either true terminal-time compression or a growing
physical kinetic PDE-rate cost at each late sampled physical event.

The theorem is a necessary rate-versus-time concentration law under finite
extended dissipation and absence of a strong terminal **H3** trace. It does
not furnish an upper bound on `Lambda`, on the outer Fourier cutoff, or a
contradiction to Navier--Stokes blow-up. Those require independent PDE input.

## Lean declarations and audit

- `thirdFull_scalar_finiteExtendedBudget_forces_realChargeSummable244`
- `thirdFull_scalar_exactKineticWidth_smallCharge_fork244`
- `thirdFullPhysical_noH3Trace_finiteExtendedBudget_kineticChargeCollapse244`

Module is source-only pending Lean and mathlib compilation under the pinned
project toolchain. Registrar checks source placeholders and registers both
`#check` and `#print axioms` for all three declarations.
