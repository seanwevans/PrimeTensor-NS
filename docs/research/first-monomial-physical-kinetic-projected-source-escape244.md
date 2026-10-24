# Physical angular-speed escape transfers to the actual projected PDE source

Baseline: `c615e297` — derive cofinal unbounded physical angular speed from terminal trace failure.

This extension follows the genuine physical `L²` Hilbert velocity `U`, actual projected
momentum source `R = U'`, kinetic loss `D`, transverse source `Q`, normalized unit
direction `N = U / sqrt(E)`, and canonical terminal kinetic mass `L > 0`.

The exact orthogonal identity from earlier work gives

    ||R||² = ||Q||² + D²/E,

so `||Q|| ≤ ||R||`. The kinetic infimum `E(t) ≥ L` and derivative identity
`N'(t) = Q(t)/sqrt(E(t))` show pointwise that

    sqrt(L) ||N'(t)|| ≤ ||Q(t)|| ≤ ||R(t)||.

The committed angular-speed escape theorem gives, if there is no strong
physical terminal `L²` trace, that for every cutoff `b` and every `M`,
some `r ∈ (b,T)` satisfies `||N'(r)|| > M`. Positivity of `sqrt L` then
transfers the cofinal escape to `Q` and to the physical projected source `R`.

The source is definitionally the exact physical Hilbert spectral difference

    R(t) = h3AuditInitialActualSpectralLaplacianTotal(t)
         - h3AuditInitialActualSpectralLerayTotal(t).

A source norm ceiling on any positive terminal subtail thus suffices for a
strong physical `L²` terminal trace, and either this trace exists with
squared norm `L`, or the source norm is cofinally unbounded.

## Boundary of inference

- This is an implication from *failure of an L² trace*, **not** from H³ nonextension.
- The projected PDE norm is the **difference** of Laplacian and Leray terms;
  no lower bound for either summand individually is inferred.
- No source ceiling is established here. The result is not a global smooth
  Navier–Stokes continuation theorem.
- No new axioms, admits or proof placeholders are introduced.
