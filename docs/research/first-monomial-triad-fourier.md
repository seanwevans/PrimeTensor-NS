# Physical Schwartz monomials and the exact Fourier phase

Base: 42f82aee, prove Schwartz integrability of first-monomial triad kernels.

## Exact identity

The new module uses the existing H3FourierPoint3 carrier and the project's
Schwartz product-to-convolution theorem. For complex scalar Schwartz f,g,h,
with F,G,H their forward Fourier transforms, it proves

    ∫ f(x) g(x) h(x) dx = ∫∫ F(p) H(r) G(-(p+r)) dp dr.

This is a bilinear Fourier identity. No complex conjugation is inserted.
The sign in q=-(p+r) follows from the inverse Fourier transform in the
bilinear pairing. The normalization contributes no extra constant.

The product measure integral is absolutely convergent, by two L1 factors
and one bounded factor. Its conversion to an iterated integral is justified
by that integrability theorem.

## The first monomial

For directions a,b,c,d, define q=-(p+r) and

    K(p,r) =
      (<p,a><p,b><p,c> F(p))
      (<r,a><r,d> H(r))
      (<q,b><q,c> G(q)).

The new theorem proves

    ∫ (∂a∂b∂c f)(∂b∂c g)(∂a∂d h)
      = (2πi)^7 ∫∫ K(p,r) dp dr.

Linear frequency multipliers preserve Schwartz regularity; a separate
integrability theorem covers K itself. Each derivative contributes 2πi,
and the exact phase is

    (2πi)^7 = -i (2π)^7.

Consequently,

    2 Re ∫ (∂a∂b∂c f)(∂b∂c g)(∂a∂d h)
      = 2 (2π)^7 Im ∫∫ K.

The factor two is retained explicitly for the physical energy pairing.
This phase matters: taking only the real part of the polynomial frequency
kernel would not recover the physical monomial.

## Connection to the previous cancellation

Choose a,b,c,d to be the i,k,l,v coordinate directions; set f=h=u_j
and g=u_v. The frequency polynomial then matches the coordinate summands
in PrimeTensor.FirstMonomialTriad.amplitudeKernel_eq_coordinate_sum.

The next bridge must formally sum those slots and transport between the
Euclidean Fourier carrier and the project's Point3 physical carrier. It must
also establish the appropriate Schwartz realization of the physical fields.
This patch does not identify arbitrary preterminal H3 path data with Schwartz
data or assert the full path aggregate identity. Extending the Schwartz
identity to the needed regularity class remains a separate analytic task.

The interpolation multiplicity three is already proved in the physical
aggregate module and must be applied only after this identification. No
critical shell estimate or continuation conclusion is claimed here.

## Validation

The patch extends tools/audit/FirstMonomialTriad.lean with the new statements
and axiom reports, and updates the source index. Source-index, prose-fragment,
and whitespace checks run during preparation. Lean is unavailable in the
preparation environment; the pinned-toolchain build remains the user's gate.
