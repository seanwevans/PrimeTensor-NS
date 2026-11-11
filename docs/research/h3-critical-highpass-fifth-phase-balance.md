# Native highpass cubic Leray forcing versus fifth velocity and signed phase

**Pinned HEAD:** `246ff297ac75765176991a004f853d3f288e3a9a`.

## A direct answer to the spatial derivative loss

The accepted localized fourth-Q PDE proof derives a true highpass source
estimate with full fifth dissipation preserved, but the high temporal and
high-sixth velocity L2 remainders cannot be upper-bounded uniformly near T
by the H3 class alone. These are **one derivative too high** compared with
the naturally available fifth velocity moment.

The existing exact signed phase defect provides an independent bridge,
**without passing through fourth-Q**. Let q=(2pi)^2|xi|^2, z the actual
velocity Fourier coordinate, and f the genuine projected Leray nonlinearity.
The repository proves

    Phase(q,z,f) >= q^3 (q|z|-|f|)^2 >= 0.

The exact polynomial square identity

    2 q^5 |z|^2 + 2 q^3 (q|z|-|f|)^2 - q^3|f|^2
      = q^3 (2q|z|-|f|)^2 >= 0

therefore proves **without any derivative or extra regularity**

    q^3|f|^2 <= 2 q^5|z|^2 + 2 Phase(q,z,f).

This bound is dimensionless and frequencywise sharp at the amplitude level;
the coefficient two is the unavoidable square-completion cost unless more
information about signed phase alignment is supplied.

## Strict physical highpass

For S_rho={sqrt(q)<rho} and U(t) the *actual* spectral velocity, at every
strict physical PDE time and for every real rho,

    sum_j integral_{S_rho^c} q^3 |N_j(U,U)|^2
      <= 2 sum_j integral_{S_rho^c} q^5 |U_j|^2
         + 2 sum_j integral_{S_rho^c} Phase(q,U_j,N_j(U,U)).

The integrability of all three densities is already established by the
physical fifth velocity mass, cubic Leray forcing mass, and signed physical
transfer integrability lemmas. The proof uses restriction to a measurable
Fourier band and does not assume a terminal supremum, a raw eighth moment,
or a full sixth-order velocity moment.

This proves a *native high-frequency cost dichotomy*: large high-frequency
cubic forcing can only arise through correspondingly large high fifth-order
velocity expenditure or signed phase mismatch on that same band. This does
not assert those high-band costs vanish, nor does it close the H3
continuation argument. A follow-up will identify the exact sharp highpass
third-radial Hilbert norm with the cubic band integral and transfer this
necessary cost to the critical dyadic witness.

## Lean declarations

- `thirdFullKinetic_cubic_le_twoFifthPhase_density244`
- `thirdFullKinetic_bandCubic_le_twoFifthPhase244`
- `thirdFullPhysical_highCubic_le_twoHighFifthPhase_coordinate244`
- `thirdFullPhysical_highCubic_le_twoHighFifthPhase244`

No new axioms or proof placeholders. Actual Lean kernel compilation is
required before accepting the commit.
