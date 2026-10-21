# Adjustable fifth radial dissipation vs cubic Leray forcing

Base checkpoint `a9af178c`: retaining a full fifth-moment share against cubic Leray forcing.

## Exact adjustable Young inequality

For `ε>0`, Fourier weight `q>=0`, velocity `z` and projected forcing `f`,

    2 q^4 |Re <z,f>| <= ε q^5 |z|^2 + ε^(-1) q^3 |f|^2.

This comes from the nonnegative square `q^3 (ε q |z| - |f|)^2`.
The strict-time integrability of the fifth velocity and cubic forcing densities
is already proved by the global Fourier PDE Hilbert construction, so integration
and the finite coordinate sum are justified:

    G(t) <= ε M5(t) + ε^(-1) M3(t).

The zero-cutoff signed PDE identity is `D3'=-2 M5+Leray_global`, and the
previous full-space absolute transfer bounds `Leray_global <= G`. Therefore

    D3'(t) + (2-ε) M5(t) <= ε^(-1) M3(t).

For `0<ε<2` this retains a positive fifth-moment dissipation share. At
`ε=1/2`, `D3' + (3/2) M5 <= 2 M3`.

## Sharpness and limitations

If `M3 <= ε(2-ε) M5`, top dissipation cannot increase. But `ε(2-ε) <= 1`
for every real ε, with equality only at ε=1. Thus the adjustable family
**does not strengthen the prior universal forcing-fraction threshold**
`M3 <= M5`. It allows the coefficients to be tuned for future estimates
with independent bounds on fifth moments and cubic forcing.

Crucially this is an **upper** bound on `D3'`, not on the positive production
of normalized Fourier variance. Substituting it into the normalized-variance
rate in the wrong orientation would be invalid. No unconditional continuation
is claimed.

## Audit

Register the module in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`,
include `#check` and `#print axioms` for all six theorems, regenerate index,
verify all fragments, check the module and full build, and rerun baseline.
