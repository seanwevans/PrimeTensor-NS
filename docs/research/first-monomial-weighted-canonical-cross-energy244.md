# Two-state cross-energy continuity of the canonical weighted H³ matched Schwartz construction

Base: `8401167b`, October 17, 2026.

## Target

The canonical signed first-monomial completion is reference-independent for a
fixed weighted spectral state and satisfies a quartic bound continuous at zero.
To address nonzero-state continuity, two *different* spectral limits U and W
must be compared without assuming their Schwartz representatives converge
to the same spectral target.

For ordered second and third jets define

    D₂(U,W) = Σ_{j,a,b} ‖D_aD_b U_j − D_aD_b W_j‖²_L²,
    D₃(U,W) = Σ_{j,a,b,c} ‖D_aD_bD_c U_j − D_aD_bD_c W_j‖²_L².

Here each derivative is the existing actual physical L² reconstruction,
transported through the repository's real Fourier-coordinate isometry; the
numbers of slots remain 27 and 81.

The new Lean module proves joint continuity of D₂ and D₃ in (U,W), zero on
the diagonal, and their **exact** identification with the limits of genuine
Schwartz E₂/E₃ cross-difference integrals for two separately constructed
matched approximation witnesses. This works when U ≠ W.

## Remaining hard math

Quantify the 243-slot trilinear perturbation in terms of D₂, D₃ and bounded
second/third jet energies, uniformly over Schwartz approximants. Passing that
inequality to the limit will establish local continuity of the canonical
signed functional at arbitrary U. The separate solenoidal density and physical
Navier–Stokes transport identification problems are not solved by this module.
