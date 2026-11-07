# Kinetic-only physical PDE time modulus for natural-cutoff H³ annuli

**Pinned base:** `04ac85e9b91e8537ae162710c354ee1e9f07af4e`.

The prior verified patch proved a true physical projected-source bound on each
fixed Fourier ball, depending only on the earlier kinetic energy anchor E0(b),
and used the physical Hilbert FTC to deduce

    ||P_n U(t) - P_n U(s)||_{H³} <= W_n C_{n+1}(E0(b)) (t-s).

The new result crosses the missing step from state evolution to actual
**H³ dissipative quadratic variation**. Its first theorem proves an exact
L² multiplier identity: the sharp H³ radial gradient at radius n+1 acts
identically on U and P_n U. There is no hidden full-H³ norm of U in this
identity. The second theorem transports this identity to the exact
physical low-band H³ dissipation, a sum of three squared multiplier norms.

The **same physical kinetic anchor** bounds ||P_n U(t)||_{H³} at every later
strict time by W_n sqrt(E0(b)). Both ends of polarization therefore have
the same fixed height, not a growing H³ state bound. The previously proved
localized polarization lemma and Fourier multiplier norm bound yield:

    |D_low,n+1(s)-D_low,n+1(t)| <= L_n(E0(b)) (t-s),

with the fully explicit, nonnegative constant

    L_n(E) = 6 (n+2)^2 [W_n sqrt(E)] [W_n C_{n+1}(E)],

    C_rho(E) = rho² sqrt(E)
               + sqrt(vol(B_rho) (18 rho E)²).

For any two NATURAL cutoff indices `R,Q`, subtracting the two low-radial
quadratics gives the true finite-annulus PDE modulus

    |D_[R+1,Q+1](s)-D_[R+1,Q+1](t)|
       <= [L_R(E0(b))+L_Q(E0(b))] (t-s).

The coefficient depends only on the two finite frequencies and the fixed
physical kinetic anchor. It contains no full H³ spectral-state maximum, no
full H³ projected-source maximum and no new pressure or time-integrability
hypothesis. The lemma is a real PDE consequence because the underlying
low-band state Lipschitz bound was derived using the actual projected
Navier--Stokes source and physical momentum FTC.

## Physical annular persistence and real terminal viscous cost

For any natural cutoffs R,Q and any actual strict physical time x, the new
radius-only annular Lipschitz modulus also gives a certified persistence
interval, without an attained H³/source maximum. Write

    L = L_R(E0(b)) + L_Q(E0(b)),
    A > 0,      2A < D_[R+1,Q+1](x),
    delta = min ((T-x)/4) (A/(2(L+1))).

The theorem `thirdFullPhysical_kineticNaturalAnnularRightTailCharge244`
constructs this **exact** delta, proves `0<delta` and `x+delta<T`, and shows

    A < D_[R+1,Q+1](r) <= D_H3(r),       x <= r <= x+delta,
    delta*A <= integral_m^T D_H3(r) dr.

The charge uses the existing interval-integrability of actual physical
H³ dissipation and does not add any charge from a potentially overlapping
first-crossing interval into a disjoint sum.

**Remaining obstruction:** this does not bound the OUTER annular capture
cutoff as the terminal horizon shrinks. Although every FIXED annulus has a
uniform kinetic-only temporal rate, allowing Q to grow sends L_Q upward.
The next math step should attach this natural-cutoff modulus to the previously
selected secondary high-radial capture and quantify the minimal radius/width
cost rather than assume a terminal-uniform outer cutoff.

No additional axioms, admits or placeholders are introduced. Compile with
the repository's pinned Lean 4.34.0-rc1 and mathlib toolchain. A green
Python/ZIP audit alone does not certify the Lean theorem proofs.
