# Physical Schwartz divergence and Fourier triad incompressibility

Base: ac1d0bb8, identify Schwartz first-monomial aggregate with shell cancellation.

## Result

For a vector of complex Schwartz functions on H3FourierPoint3, define

    div u = Σ_j ∂_{e_j} u_j.

The new module proves its exact Fourier symbol:

    Fourier(div u)(q) = (2πi) Σ_j q_j Fourier(u_j)(q).

The proof uses linearity of the Schwartz Fourier transform, the existing
pointwise derivative multiplier, and the coordinate-direction inner product
identity. The bundled Schwartz divergence is also identified pointwise with

    Σ_j (fderiv ℝ u_j x)(e_j).

Thus pointwise physical divergence zero implies the exact polarization
condition used by the triad cancellation theorem. Only the constant 2πi is
cancelled. No division by a frequency coordinate or frequency norm occurs,
and zero frequency needs no separate case.

## Consequence

The full Schwartz first-monomial aggregate now has the shell identity under
physical incompressibility alone:

    2 A = (2πi)^7 ∫ S,
    2 Re A = (2π)^7 Im ∫ S.

The final statements no longer require an independent Fourier divergence
hypothesis. Shell-kernel integrability is also supplied from the same
physical hypothesis and Schwartz regularity.

## Remaining boundary

These physical derivatives are on the Euclidean H3FourierPoint3 carrier.
Identification with the existing Point3 path aggregate, including its sum
order, remains to be formalized. The theorem is for Schwartz fields and does
not assert that arbitrary preterminal H3 path data are Schwartz. Extending
the identity to the needed regularity class and proving a critical estimate
from the shell difference are still separate tasks.

## Validation

The audit file checks the symbol, incompressibility transfer, and physical
shell identities and prints their axioms. The source index and prose-fragment
checks accompany the patch. Lean compilation is pending in the user's pinned
toolchain; Lean is unavailable in the preparation environment.
