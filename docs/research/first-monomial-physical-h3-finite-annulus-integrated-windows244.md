# Physical H³: cubic high-frequency peaks have finite-annulus integrated windows

Checkpoint: `ce7ab5e1` (`prove automatic positive-time continuity of low radial H3 dissipation`).

## Analytic point

At any strict positive physical time the real spectral H³ dissipation density
`q(ξ) Σ_j |G_j(ξ)|²` is integrable. The decreasing high-radial sets
`{|D(ξ)| ≥ n+1}` exhaust the empty set. The previously used
`Antitone.tendsto_setIntegral` establishes **fixed-time** decay of actual
high-radial dissipation as the outer cutoff tends to infinity.

At a cubic witness `D_high(n+1,t_n) > (n+1)^3`, select `N_n ≥ n` with
`D_high(N_n+1,t_n) < (n+1)^3/4`. The exact physical partition then gives

`D_low(N_n+1,t_n)-D_low(n+1,t_n) > 3(n+1)^3/4`.

The low-frequency positive-time continuity theorem at checkpoint
`ce7ab5e1` makes the finite-band difference continuous. There is therefore
a right-hand strict-time interval `[t_n,t_n+δ_n]`, δ_n>0, on which

`D_low(N_n+1,t)-D_low(n+1,t) > (n+1)^3/2`.

The finite-band function is automatically interval-integrable and obeys

`∫_[t_n,t_n+δ_n] (D_low(N_n+1)-D_low(n+1)) ≥ δ_n(n+1)^3/2`.

The same pointwise height applies to the FULL high-radial dissipation because
its exterior contribution beyond `N_n+1` is nonnegative.

This discharges the otherwise unresolved **full H³ dissipation continuity**
hypothesis of the preceding cubic *window-height* statement. The result
integrates the finite-band observable, not the possibly time-nonintegrable
unbounded high-radial observable. Ordinary real interval integration of the
latter requires its interval-integrability, which is not inferred here.

## Scope of the result

The terminal no-strong-physical-kinetic-L²-trace branch remains an explicit
assumption. The outer radii `N_n` and window widths `δ_n` can both vary with
`n`. No lower bound on the latter is claimed, so no accumulated terminal
dissipation divergence, H³ blowup exclusion, or smooth continuation is claimed.

## Axiom audit

All five declarations should be checked with Lean and their `#print axioms`
outputs through the standard PrimeTensor audit before merging. This archive
contains no `sorry` or new axioms, but is not Lean-verified by the package
creation environment.
