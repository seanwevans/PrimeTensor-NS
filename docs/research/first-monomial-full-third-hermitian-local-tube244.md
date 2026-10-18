# Full-third transport: strict Hermitian sign tube and positive-volume local integral

Base: `a9bbffd3` (complete real third transport Fourier identification).

The complete third-order H3 spatial commutator has now been identified with the
real part of its actual Schwartz Fourier integral, while the corrected fully
permuted finite-dimensional derivative symbol and Hermitian phase have been
proved separately.

This module establishes the **local**, six-dimensional sign geometry of the
latter symbol. With momentum constraint `q = -(p+r)` and the explicit
solenoidal center, its Hermitian phase orbit equals **-192**. The exact
continuous six-order polynomial is strictly negative throughout some closed
ball of positive radius around this center. Since the momentum-pair carrier
has product Lebesgue volume, the **unweighted local integral** of that
polynomial over this closed ball is strictly negative.

This is a measurable nonzero-volume neighborhood, as opposed to evaluating a
symbol at an isolated momentum triad. The result is still **not the integral
of the actual Hermitian Schwartz Fourier amplitudes** and **not a global sign
claim**. Other momentum resonances and the Fourier support of the eventual
packet must be handled rigorously.

The module also defines the polynomial transverse lift on the actual positive
axis carrier:

    P_xi(a) = (xi . xi) a - (xi . a) xi.

Its divergence `xi . P_xi(a)` vanishes identically, even for `xi=0`. The lift
is continuous and reproduces the original transverse polarization at each
center, multiplied by the center's squared frequency norm. This provides the
relevant real-axis polynomial germ for eventual smooth compact cutoffs; the
project previously implemented the analogous germs for `Fin 3` in its
first-monomial six-packet construction.

## Open tasks

1. Normalize the actual three center germs without introducing a singular
   denominator, assign the selected relative complex phase, and Hermitianize
   the six localized modes on `Axis Depth.three`.
2. Exclude spurious triad resonances uniformly for a sufficiently small
   cutoff width; prove the entire kernel support lies in the coherent sign
   regions.
3. Identify the localized Hermitian packet integral with the full real
   Fourier coefficient `fullThirdSchwartzFourierCoefficient244` and prove it
   nonzero, then invoke the existing conditional static-obstruction theorem.

No Navier--Stokes continuation theorem is asserted here.
