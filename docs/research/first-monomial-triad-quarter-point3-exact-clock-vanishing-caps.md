# Vanishing exact cubic PDE caps

Base commit: `0a8ad1b1` (Lean CI passing).

For the exact persistence selector

`δ_n = min(b_n/2, 1, gap_n/(2*(Λ_n+Ξ_n+1)))`,

the finite H³ dissipation assumption gives a disjoint cofinal sequence `v(k)` with

`δ_{v(k)} (v(k)+1)^3 → 0`.

Therefore, for **every ε>0**, eventually

`(v(k)+1)^3 b_{v(k)}/2 ≤ ε`

or

`(v(k)+1)^3 gap_{v(k)}/(2*(Λ_{v(k)}+Ξ_{v(k)}+1)) ≤ ε`.

The unit cap is excluded because `(v(k)+1)^3` diverges; the result is
stronger than the former dichotomy expressed in terms of a fixed total
dissipation integral. A further conditional theorem shows that an eventual
positive lower bound on the cubic-weighted geometric cap forces the
normalized PDE gap below every positive ε.

**Scope:** This is a necessary alternative conditional on finite terminal
H³ dissipation and the no-terminal-L²-trace branch. It does not prove a
positive geometric lower bound, a bound on source coefficients, or global
Navier–Stokes regularity.

**Validation:** Requires the repository's Lean 4 toolchain; the ZIP was
prepared without running Lean locally. Run the single-module build,
`proof/generate_index.py`, index validation, audit and full CI build.
