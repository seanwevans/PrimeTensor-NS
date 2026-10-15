# Complete physical Schwartz adjacent-energy Cauchy, with axis-cardinality loss

Base checkpoint: `8a53c44b`.

The existing slotwise integral Cauchy–Schwarz bounds are assembled with
Mathlib's `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`, jointly over all actual
components and directional derivative slots. The nonnegative repeated-axis
diagonal second/third energies are bounded by the *complete* second/third
energies, with no artificial Fourier normalizations or auxiliary assumptions.

Consequently the new unconditional theorems state

    E1(f)^2 ≤ card(Axis Depth.three) E0(f) E2(f),
    E2(f)^2 ≤ card(Axis Depth.three) E1(f) E3(f).

The cardinal is three. These are not yet the **sharp coefficient-one** estimates
needed in the cubic log-convexity bridge: to remove the extra axis count, prove
the mixed-derivative Laplacian/Hessian contraction identity, or transfer the
exact Fourier radial symbol identity to the real Schwartz energy totals.
No global critical-half coefficient or Navier–Stokes continuation is inferred.
