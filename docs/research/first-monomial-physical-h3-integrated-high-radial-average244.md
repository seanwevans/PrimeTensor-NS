# Kinetic-anchored high-radial physical H³ time averages

Base: `c45a6149` — *bound low radial H3 dissipation by anchored kinetic budget*.

## Exact physical comparison

Fix a strict kinetic anchor `b` and radius `ρ ≥ 0`. Define the actual physical low and high Fourier H³ viscous dissipation from the canonical weighted state as `D_low(ρ,t)` and `D_high(ρ,t)`, with `D(t) = D_low(ρ,t) + D_high(ρ,t)`. The previously closed kinetic-anchored ceiling states

```
0 ≤ D_low(ρ,t) ≤ C(b,ρ)
C(b,ρ) = ρ² K(ρ) E₀(b)
```

for every `b < t < T`, where `K` is the proved Sobolev radial weight ceiling. With the appropriate strict-time interval integrability of `D` and `D_high`, the present proof derives

```
∫[s,t] D_high ≤ ∫[s,t] D ≤ ∫[s,t] D_high + C(b,ρ) (t-s)
```

for every `b < s ≤ t < T`. No unproved continuity of the unbounded full H³ viscous functional is used.

For a real threshold `m`, if the full dissipation integral exceeds `(t-s)(C(b,ρ)+m)`, the high-frequency integral exceeds `(t-s)m`. This identifies precisely which part of the accumulated cost cannot be supplied by any bounded radial carrier.

## Quantitative time-average concentration

Choose **any** sequence of ordered strict subtail windows `s_n < t_n` such that both dissipations are interval-integrable and

```
(n+1) C(b,ρ) (t_n-s_n) < ∫[s_n,t_n] D.
```

Then on the **same** windows,

```
∫[s_n,t_n] D_high / ∫[s_n,t_n] D → 1.
```

The proof first establishes the general algebraic lemma for nonnegative ceiling `C_n`, nonnegative widths, and scalar integrated total/high masses. The inequality `0 ≤ D_n - H_n ≤ C_n width_n` gives a defect fraction bounded by `1/(n+1)`, proving the limit by squeezing.

## Analytic frontier

This theorem is a **conditional temporal reduction**. An arbitrarily high value of `D_high(n+1,t_n)` at isolated times does not automatically imply `(n+1) C(b,ρ) (t_n-s_n) < ∫D` on any interval. The substantive unsolved bridge is a quantitative physical persistence modulus/width, not a Fourier normalization or scalar rearrangement.

The repository separately proves strong continuity of the actual weighted H³ spectral velocity on `(0,T)` (`h3Audit_initialActualSpectralVelocity_continuousOn`). This is insufficient *by itself* for continuity of full H³ dissipation: multiplication by the unbounded Fourier gradient magnitude is not a bounded operator on weighted H³ L². Low-frequency truncated dissipation should be continuous via bounded multipliers, which is a separate formalization target.
