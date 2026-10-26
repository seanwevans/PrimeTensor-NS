# Bounded sixth-order PDE coefficients force terminal clock compression

Base commit: `bafba53c` — retain quarter-cubic gaps and derive super-sixth PDE concentration.

## Mathematical statement

Use the *same* strict, separated and cofinal witnesses as the exact-width
physical projected-PDE construction, with `R = v(k)+1`, initial annular
surplus `gap > R³/4`, and actual linear/quadratic PDE rates
`Z = Λ+Ξ+1 > 0`. Finite terminal H³ dissipation (an additional assumption)
gives `R³ δ → 0` for the exact selector

`δ = min ((T-τ)/4) (min 1 (gap/(2Z)))`.

The quantitative two-scale barrier states: for every `ε>0`, eventually

`R³*(T-τ)/4 ≤ ε  OR  R⁶ ≤ 8 ε Z`.

The second branch follows from `gap ≥ R³/4` and
`R³ gap/(2Z) ≤ ε`, without an unproved bound on the outer Fourier cutoff.

Consequently, if on these same witnesses `Z ≤ B R⁶` eventually for some
fixed `B>0`, the second branch is impossible at sufficiently small ε. We get

`R³*(T-τ) → 0`.

This is the complementary statement to the previous conditional
`Z/R⁶ → +∞` conclusion under a positive geometric floor. It directly
pinpoints the terminal-time compression that a PDE-side argument would
have to exclude before the coefficient barrier can become contradictory.

## Scope and validation

The physical statement assumes no strong terminal L² trace, positive terminal
kinetic mass, and interval-integrable full H³ dissipation, as in the previous
proof. It does not derive an O(R⁶) bound from admissibility. No terminal
regularity or Navier–Stokes global smoothness assertion is made.

Four Lean theorems, no `sorry`, `admit`, or new axioms. Verify with the
repository Lean version, run proof index generation/check, Lean audit, and
full `lake build`; the patch was packaged without a Lean runtime locally.
