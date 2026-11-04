# Complex transverse polynomial and the exact longitudinal resonance

**Parent:** `8dbb8734` — repaired the longitudinal H³ flux majorant and exposed the exact uncorrected-limit criterion.

## Complex Fourier numerator, not a real-polarization substitute

The corrected physical Fourier formula has complex bilinear amplitudes. For real frequency ξ and complex polarization A, construct

    N_ξ(A) = (ξ·ξ) A - (ξ·A) ξ.

The new theorem proves ξ·N_ξ(A)=0 for *every* ξ (including zero) and arbitrary complex A. Also N_ξ(N_ξ(A))=(ξ·ξ)N_ξ(A), and if ξ·A=0 then N_ξ(A)=(ξ·ξ)A. The fixed-center germ N_ξ(A)/(η·η) is transverse at varying ξ and agrees exactly with a transverse A at the nonzero anchor η; the inverse radius is fixed, not 1/(ξ·ξ).

Applying this numerator separately to p, q, r makes the already established longitudinal H³ defect identically zero, so the complete twelve-term six-orbit becomes the three-term sixth-power flux with no additional hypothesis on the unprojected input amplitudes. This is a *pointwise* result, not yet a construction of the required globally real, Schwartz, derivative-matched approximants.

## Genuine resonant obstruction for the unprojected symbol

At (p,q,r)=(p,0,-p), for arbitrary complex A,B,C, put R=p·p, α=p·A and Z=B·C. Then

    S₆(p,0,-p;A,B,C) = 0,
    F₆(p,0,-p;A,B,C) = -Z α R³,
    D_long(p,0,-p;A,B,C) = +Z α R³.

All three equations are recorded as Lean theorems. For high p with |p|≈N and fixed nonzero longitudinal α≈N, each isolated term has degree N⁷, while two high-frequency H³ factors provide only N⁶. This is a **symbol-level** obstruction to a universal, naive product-weight bound on the separate terms; it does not by itself prove failure of any specific integrated estimate. The exact S₆ cancellation is therefore essential.

## Remaining analytic challenge

For a genuinely solenoidal weighted H³ state, construct real physical Schwartz approximants by applying transverse Fourier cutoffs **before** passing to the completed derivative graph. Show they preserve Fourier reality and converge in the exact pointwise decoder and second/third jet matching required by `H3MatchedSchwartzGradientCompletion244`, not merely in a weak L² topology. Alternately, obtain an integrated divergence error bound with sufficient frequency gain to control the high-high-low region.

The proof module contains no axioms, `sorry`, or `admit`. The generated source and registrar were syntax/structurally checked. Lean compilation must be performed in the user's project Lake environment.
