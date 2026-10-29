# Higher radial spacetime budget: actual physical source or spectral cutoff gain

Base `2ed72e8e` (amplify canonical physical PDE rates under higher radial spacetime budgets).

On the very same exact-anchor disjoint PDE windows, when the physical extended
q^(4+m) top-order moment has a nonnegative time-integrable real majorant,
the previous higher-rate result forces, for every eps>0 eventually, at least
one of the three clock barriers (time, linear Lambda, quadratic Xi).

The **actual** clock coefficients are exact polynomials in the attained
projected physical momentum-source norm C_k:

    Lambda_k = C_k * G_linear(R_k,Q_k,K_k)
    Xi_k = C_k^2 * G_quadratic(R_k,Q_k).

Here K_k = ||U_3(t_k)||, and the proof obtains K_k^2 <= E_3(t_k)
from the established exact physical H3 energy / Fourier identity.
C_k is the maximum, *actually attained* on the original compact strict-time
half-terminal interval, of the physical projected source norm.

For ANY proposed nonnegative source threshold S and eps>0, eventually
one of these four mechanisms must occur:

  1. An actual physical projected-source observation in that half-terminal
     interval has norm > S;
  2. R_k^(2m+3) (T-t_k)/4 <= eps;
  3. (R_k^2)^m R_k^6 <= 16 eps (S G_linear(R_k,Q_k,K_k)+1);
  4. ((R_k^2)^m)^2 R_k^9 <= 16 eps^2
         (S^2 G_quadratic(R_k,Q_k)+1).

Both gains are the previously defined Fourier multiplier quantities, NOT
assumed uniformly bounded. A separate real scalar theorem says, provided
R<=Q and K^2<=E, a linear rate A<=16 eps (Lambda+1) implies

    A^2 <= 512 eps^2 (2304 E C^2 (Q+1)^10 + 1).

This is a necessary energy/source cost, not an independent PDE upper budget.
The only additional analytic premise for the canonical result is the
explicit higher-order integrable real envelope. No contradiction or smooth
continuation is claimed.

Formal declarations:
- `h3Path_higherBudget_linearRate_eq_sourceGain244`
- `h3Path_scalar_higherBudget_sourceOrCutoffGain244`
- `h3Path_scalar_higherLinearRate_forces_energySourceSquare244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_physicalSourceOrGain244`

Local Lean compilation with the pinned Mathlib toolchain is still required.

## Lean correction (fix1)

Three additive-order mismatches in monotone comparison witnesses were
resolved by explicitly deriving `x + 1 ≤ y + 1` from the original scalar
comparison before applying the nonnegative scaling factor. This avoids
using a commuted `1 + x ≤ 1 + y` as if Lean considered it definitionally
equal. The four theorem statements and mathematical constants are unchanged.
