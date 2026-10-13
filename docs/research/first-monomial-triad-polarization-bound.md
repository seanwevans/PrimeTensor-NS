# Complete pointwise polarization bound

Base: c816e0ac, shell kernel bounded by middle-frequency gain.

Let q=-(p+r), P=||p||, R=||r||, Q=||q||. The polarization norm in this
patch is the Euclidean complex l2 norm, explicitly represented by
EuclideanSpace, rather than the sup norm of a coordinate function.

The bilinear contraction satisfies

    |sum_j a_j c_j| <= |a|_2 |c|_2.

This follows by the triangle inequality and real Cauchy-Schwarz on the
coordinate magnitudes. It does not change the bilinear contraction into
a Hermitian one. Real frequencies embedded in the complex Euclidean
carrier preserve their norm, giving |p·b| <= P |b|_2.

When q·b=0, momentum implies p·b=-r·b. Consequently

    |p·b| <= min(P,R) |b|_2.

Combining these statements with the preceding shell-gap bound gives the
pointwise estimate for the existing Schwartz shell kernel:

    |S(p,r)| <= P R min(P,R) (P+R) Q³ |U(p)|_2 |U(q)|_2 |U(r)|_2.

Only incompressibility at the middle frequency is required by the final
theorem. The previous physical-divergence transport supplies that hypothesis
for the physical Schwartz realization. Zero frequencies require no special
case or division.

## Scaling and next question

For P,R of size N and Q of size L much smaller than N, the frequency
coefficient is O(N⁴ L³), against the unsymmetrized O(N⁵ L²) estimate.
When all frequencies have size N, it remains O(N⁷). Thus the gain helps
separated interactions but alone does not settle the comparable-frequency
contribution or critical H3 absorption.

Next work must estimate the resulting integral, separate frequency regimes
when useful, and compare against the actual energy and dissipation terms.
A pointwise symbol bound alone is not a continuation result. Extending the
physical identity beyond an explicit Schwartz realization is also pending.

## Checks

Source index, fragment consistency and whitespace are checked when packaging.
Lean compilation and the theorem audit remain pending the pinned local build.
The patch introduces no axioms or sorry declarations.
