# First integrated shell bound

Base: bfaf663f, Euclidean polarization bounds and smaller outer frequency.

Write A(p)=|U(p)|_2. The minimum-radius bound implies

    min(P,R)(P+R) <= 2PR,
    |S(p,r)| <= 2 [P² A(p)] [R² A(r)] [Q³ A(q)],

where q=-(p+r). The map (p,r) -> (p,q) preserves product volume and is
its own inverse. For real F,H with H nonnegative, F² integrable and H
integrable, the elementary inequality 2F(p)F(r)<=F(p)²+F(r)² therefore gives

    |integral K| <= 2 (integral F²) (integral H)

whenever K is integrable and |K(p,r)|<=2F(p)F(r)H(-(p+r)). The proof uses
both outer-frequency orders, the exact change of variables, and an
integrable sum majorant. No formal exchange of divergent integrals occurs.

Specializing to the existing shell kernel gives

    |integral S| <= 2 E2 M3,
    E2 = integral |p|⁴ A(p)²,
    M3 = integral |q|³ A(q).

## What this does and does not establish

This is an actual integral estimate, not merely a pointwise comparison.
The specialization currently takes integrability of the two weighted moments
as explicit hypotheses. Those hypotheses are valid for Schwartz data, but
their automatic derivation for this vector amplitude is not part of this patch.

E2 is the homogeneous second-order Fourier L2 energy. M3 is a third-order
Fourier L1 moment. M3 is not controlled by the H3 norm alone: applying
Cauchy-Schwarz with homogeneous H3 weight leaves an infinite-volume factor.
Using inhomogeneous Hs alone controls M3 by this argument only for s>9/2
in three dimensions. Consequently the bound does not close H3 absorption.

For the previously established physical shell identity, the corresponding
formal consequence is |physical aggregate| <= 2 (2 pi)^7 E2 M3, and the
interpolation multiplicity adds another factor three. This patch states the
shell integral estimate; it does not add a separate physical wrapper.

## Next mathematical decision

Preserve the separated-frequency gain in a dyadic or comparable-frequency
analysis rather than treating the new M3 factor as a controlled H3 quantity.
The comparable-frequency contribution is still the critical issue. Derive
Schwartz moment finiteness for the vector amplitude when removing the
explicit analytic hypotheses from this interface.

## Checks

Source indexing, fragment consistency and whitespace checks are run before
packaging. Lean compilation and the theorem audit remain pending locally.
No axioms, sorry declarations or existing theorem changes are introduced.
