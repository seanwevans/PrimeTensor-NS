# Kinetic-anchored low-radial physical H³ dissipation budget

**Base commit:** `62168f9a` — retain physical H3 high radial dissipation height on temporal windows.

## New genuinely physical bound

For a strict anchor `b` and every physical time `b<t<T`, the already established
low-radial *spectral H³ square mass* kinetic ceiling combines with the genuine
pointwise Fourier dissipation comparison to give

    D_low(ρ,t) ≤ ρ² K(ρ) E₀(b),    ρ≥0.

The estimate holds uniformly over all subsequent strict times. Unlike prior
conditional temporal-window results, it requires NO continuity of either
full H³ dissipation or its low-frequency part.

## Integrated separation

When low-frequency interval integrability is available on a compact strict
time interval `[s,t]` after `b`, its accumulation is at most

    ∫_s^t D_low(ρ,r) dr ≤ (t-s) ρ² K(ρ) E₀(b).

When the full and high-frequency intervals are integrable, the exact physical
spectral partition gives

    ∫_s^t D_full(r) dr
      ≤ (t-s) ρ² K(ρ) E₀(b) + ∫_s^t D_high(ρ,r) dr.

Thus every excess above the kinetic band budget must be paid by physical
high-frequency dissipation; the statement is **conditional on the indicated
integrability**, not a new terminal divergence theorem.

## Absolute high-frequency witness

Existing moving-radial **energy mass** escape under positive terminal kinetic
mass and absence of a strong physical L² terminal trace supplies ONE sequence
`τ(n)→T` with `H_{n+1}(τ n)>n+1`. The already verified high-region spectral
density inequality now gives on that very sequence

    D_high(n+1,τ n) ≥ (n+1)² H_{n+1}(τ n) > (n+1)³.

This is stronger than mere normalized escape but still only at snapshots. The
missing high-order time regularity or quantitative persistence width is not
smuggled into any statement.

## Validation status

Archive/registrar validation performed in the producing environment. `lake`
and `lean` are unavailable there; local Lean compilation and full CI remain
the acceptance tests.
