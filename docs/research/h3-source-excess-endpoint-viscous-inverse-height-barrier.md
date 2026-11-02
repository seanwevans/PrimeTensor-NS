# Critical inverse-height persistence obstruction for cofinal H³ spectral spikes

**Base:** `c8e429d9` — full physical H³ dissipation exposure collapse on synchronized windows.

The exact cofinal `h3Critical_noL2Trace_cofinalFivefold_endpointViscousChargeCollapse`
selection has nonnegative finite-terminal viscous charges

    C(k) = η(k) * H(k),   H(k) = R(k)^2 ε(k)^2 / 8 > 0,

and `C(k) → 0`, with the charge series bounded by the single full physical
H³ dissipation integral on `(a,T)`.

Because each `H(k)` is strictly positive, every fixed `γ > 0` forces

    eventually,   η(k) < γ / H(k).

Equivalently a full cofinal tail **cannot** carry persistence widths
`η(k) ≥ γ/H(k)` at any positive fixed `γ`. This holds without assuming
that `H(k)` diverges, but does not bound individual isolated pulse widths.

The new same-witness four-way gate upgrades the fourth (high radial
physical-dissipation persistence) branch to include this strict inverse-height
width restriction on all sufficiently late indices, while retaining the
non-spectral, physical PDE-clock and anchor viscosity alternatives unchanged.

**This does not rule out terminal failure**: endpoint windows may shrink
arbitrarily rapidly. The remaining hard analysis is a lower bound on
persistence width, a sharpened exclusion of other source/PDE branches, or a
physical terminal-trace compactness argument.

## Lean declarations

- `h3Critical_scalar_vanishingCharge_eventualInverseHeightWidth`
- `h3Critical_scalar_vanishingCharge_noEventualCriticalPersistence`
- `h3Critical_noL2Trace_cofinalFivefold_inverseHeightEndpointPersistenceGate`

The registrar registers one root import and the three axiom audits. The normal
workflow regenerates `proof/order.txt` via `proof/generate_index.py` and checks it
via `--check`, then runs the Lean module, project build and baseline audit.
