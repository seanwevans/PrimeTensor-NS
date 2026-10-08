# Kinetic control and the normalized quartic coefficient

Based on `c204a1e9`. Implementation:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/KineticQuartic.lean`.

The previous criterion retained the entire normalized remainder R/E.
The closed orderwise energy derivative identities already prove that E₀ is
nonincreasing on an energy-class tail (a,T). Fixing b in (a,T) therefore
gives E₀(t) ≤ E₀(b) for b < t < T without another analytic assumption.

For B ≥ 1 and ε = 2,

    R = B + (3B + (81/8) B⁴) E₀
      ≤ (1 + 14 E₀(b)) B⁴.

Here B ≤ B⁴, and 3B + (81/8)B⁴ ≤ 14B⁴. The coefficient 14 is a
convenient upper bound, not an optimized constant. The exact PDE balance
and positivity of E give

    E′ ≤ [(1 + 14 E₀(b)) B⁴/E] E.

Consequently integrability of B⁴/E on (b,T) supplies continuation whenever
|T_H3| ≤ B E. A final theorem uses B = 4422(1 + |h|) from the closed
gradient-envelope estimate. There is no extra kinetic-bound hypothesis.

The remaining assumption is still temporal: integrability of B⁴/E.
For the coarse coefficient proportional to sqrt(E), this requires control
of a quantity growing like E. The kinetic identity alone does not provide
that control. No unconditional regularity result, improved Fourier estimate,
or strict comparison with all earlier continuation criteria is claimed.

The new results are included in the root imports and selected contract/axiom
audit. Packaging checks source coverage, generated index, compatibility
paths, and whitespace. Lean compilation must run via the local baseline;
Lean is unavailable in the packaging environment.
