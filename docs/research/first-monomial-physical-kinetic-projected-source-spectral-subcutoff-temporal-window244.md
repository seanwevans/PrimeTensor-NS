# Subcutoff physical H³ dissipation evacuation and temporal-window frontier

**Base:** `beeedce5` (fixed Fourier-radius dissipation evacuation).

## Unconditional strengthening: profiles, not just fixed radii

On one terminal physical sequence selected by the existing four-channel theorem, with
`R_n=n+1`, true physical spectral H³ dissipation satisfies

    R_n D_{< R_n}(t_n) < D_{>= R_n}(t_n),
    D_{< R_n}(t_n) + D_{>= R_n}(t_n) = D(t_n).

The monotonicity of the genuine restricted Fourier integral implies for *each
arbitrary profile* `rho_n <= R_n` eventually, without selecting a new sequence,

    0 <= D_{< rho_n}(t_n) / D(t_n) < 1/(n+2)   eventually,
    D_{< rho_n}(t_n) / D(t_n) -> 0.

This quantifies the same-path high-frequency dissipation evacuation and is
stronger than limits for each individually fixed radius.

## Conditional positive-width local persistence

If, for each n, the actual full H³ dissipation and actual low-radial
Fourier dissipation are continuous at the selected time t_n, then the
normalized low share is continuous there, because D(t_n)>0. The strict
pointwise inequality extends to *some* delta_n>0:

    |s - t_n| < delta_n  ==>  D_{<R_n}(s)/D(s) < 1/(n+2).

Those continuity hypotheses are explicit, not silently inferred from
H³ energy-class differentiability. The theorem proves neither a uniform
lower bound on delta_n nor positive accumulated dissipation over the windows.
In particular spikes can be arbitrarily narrow. The missing mathematical
step toward integrated terminal control is a quantitative temporal modulus
or a spacetime lower estimate compatible with the full Navier–Stokes PDE.

## Formal contracts

The six Lean theorems prove: snapshot subcutoff bound; all eventual-subcutoff
profiles on one sequence; continuity of ratio from two scalar components;
strict continuous inequality on a local metric ball; conditional selected-time
local windows; and the no-kinetic-trace profile evacuation consequence.

No new axiom, `sorry`, H³ nonextension equivalence, or uniform continuity
premise is introduced.
