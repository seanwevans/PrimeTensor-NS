# Sharp physical Fourier low/high splitting at the critical H3 source peak

Base commit: `572637bdbe4a8b79a2c5f5539bc4a13e62a985c3`.

## New formal mathematical interface

The preceding physical net-growth source gate pays an artificial factor of
**two** to split the genuine order-three Leray forcing Fourier state into
low and high sharp frequency projections. The generic Hilbert triangle
inequality gives such a bound, but the actual Fourier sharp cutoff is an
indicator and its complement has disjoint Fourier support. The exact L2
Pythagoras identity is therefore available *without any extra moments*:

    ||F||_2^2 = ||P_rho F||_2^2 + ||(I-P_rho) F||_2^2.

The formal proof uses the existing a.e. representatives for both cutoffs,
the exact norm-square integral identity for complex Fourier L2, and the
Lebesgue `integral_add_compl` identity. No abstract orthogonal projection
hypothesis is postulated; this is the actual physical Fourier indicator.

At strict physical time r, let E=E0(b), let D3(r) be the true third-order
physical dissipation and define

    L_rho(E) = rho^6 * volume(S_rho) * (18*rho*E)^2,
    H_rho(r) = sum_{j=0}^2 ||(I-P_rho)F3_j(r)||_2^2,
    C=(2*pi)^6.

The exact physical cubic forcing identity and kinetic-only low-band bound
then imply

    (signed_log_rate(r) + fifth_rate(r) + phase_rate(r)) * D3(r)
         <= C * (3*L_rho(E) + H_rho(r)).

In particular, at the single interior dyadic net-growth witness already
proved in the library, selected **before** rho and valid for every rho>=0,

    (K + fifth_rate(r) + phase_rate(r)) * D3(r)
         < C * (3*L_rho(E) + H_rho(r)),

and hence the unconditional (at that witness) deficit inequality

    (K + fifth_rate(r) + phase_rate(r))*D3(r) - 3*C*L_rho(E)
         < C * H_rho(r).

Compared with the previous bound `2*C*(3L+H)`, this recovers the sharp
coefficient 1 before the exact highpass square mass and all viscous loss.

## Boundary / missing estimate

This is a new Lean theorem proving an **established mathematical fact**
(exact orthogonality of disjoint Fourier projections), and an improvement
to the genuine Navier--Stokes source gate. It does **not** establish the
new mathematical upper bound on nonlinear high-frequency forcing needed
to exclude critical saturation. The next problem is to control the
solenoidal quadratic highpass source relative to its fifth/phase viscous
expenditure and the high-H3 spectral state, at the same physical time,
without assuming order-eight raw Fourier moments.

## Audit

Register with `python3 tools/audit/register_h3_critical_dyadic_sharp_fourier_highpass.py --apply`,
regenerate the project index, compile the source and full PrimeTensor target,
then run the registered axiom audit before committing.
