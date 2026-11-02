# Canonical minimal last-shell H³ annuli: exact physical sixth/ninth PDE alternatives

Base commit `964cd566` (minimal last-shell / exact physical PDE clock bridge).

## Main point

The previous sixth/ninth-order energy/source bound and the canonical minimal
last-shell construction were established on different existential selections.
One cannot substitute the minimal-shell mass of one construction into the PDE
rate alternative of another construction without demonstrating that the
witnesses agree. The new theorem derives the rate alternative directly from
the *same* canonical `h3CriticalMinimalShellEnergyWindow` diagonal.

At selected index `v k`, denote

- `R = v k + 1`, `Q = N (v k) + 1`, `E = velocityH3EnergyAt u (t (v k))`,
- `C` the attained projected-source maximum on the half-terminal interval,
- `δ` the exact quadratic-sharp PDE width,
- `M_last` the actual raw Fourier kinetic mass of the final integer shell.

The minimal first crossing has predecessor `m` with `N = m+1` and
`v k ≤ m`. Its strict positive overshoot `ω` satisfies

    0 < ω ≤ 4 * (N+2)^8 * M_last.

It also preserves the physical energy crossing

    R^3 < 4 * (N+2)^2 * E.

The disjoint exact PDE windows satisfy the positive annular integral charge
lower bound and the same aggregate charge alternative: unbounded certified
cumulative charges, or (for every `ε>0`, eventually) one of

    R^3 * (T-t)/4 ≤ ε,
    R^12 ≤ 512 ε² [2304 E C² (N+2)^10 + 1],
    R^9 ≤ 16 ε² [36 C² ((N+2)^8+(R+1)^8) + 1].

`N` in every line is **the minimal** first crossing, not an independently
selected or enlarged outer cutoff. No terminal H³ dissipation L¹ bound,
source cap, or outer radius cap is assumed.

## Limits of this step

Last-shell kinetic positivity gives no fixed fractional cubic lower bound.
The rate alternative does not imply that charge divergence, source growth,
outer-frequency escape, or clock compression has been excluded. It is a
necessary-condition dichotomy, not a Navier–Stokes regularity proof.

## Local verification

Run the packaged registrar with `--apply`, followed by `--check`; regenerate
and verify the proof index; run `lake env lean` on the new Lean module, the
individual module build and complete Lake build, root/audit Lean checks and
the baseline audit. The staging environment does not include Lean.
