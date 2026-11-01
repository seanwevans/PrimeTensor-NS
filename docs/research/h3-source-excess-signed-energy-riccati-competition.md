# Actual Fourier-source excess, signed H³ energy, and Riccati competition

Base checkpoint `247bcde5`: verified source-excess quintic cofinal three-way cost gate.

## Physical signed identity, not a positive-part rate

The accepted exact path-energy balance establishes on all strict physical
H³ times:

    E'(s) + 2 D(s) = -Transport_H3(s).

The accepted Fourier-source surplus estimate gives, at any source peak above
the kinetic-anchored barrier by Q:

    D(s) > M + Q/κ,       κ=3(3+C_L)>0.

Consequently, at those very same times:

    E'(s) + 2(M+Q/κ) < -Transport_H3(s)
    E'(s) + 2(M+Q/κ) < K sqrt(E(s)) E(s),

where K is the existing proved `h3PathSqrtEnergyRiccatiCoefficient`. This
uses the **signed** derivative, not its positive part; it is valid when
E' is negative and also when it is positive.

The second bound forces the pointwise genuine alternative

    E'(s) <= -(M+Q/κ)  OR
    M+Q/κ < K sqrt(E(s)) E(s).

In particular, on nondecreasing-energy slices `E'(s) >= 0`, squaring the
positive Riccati bound forces the cubic physical H³ energy condition

    4 (M+Q/κ)^2 <= K^2 E(s)^3.

This links actual Fourier-source peaks to a **signed energy drain or large
instantaneous H³ energy**, without assuming either type of behavior.

## Cofinal transfer uses the original quintic windows

The main theorem reuses the entire witness construction from
`h3Critical_noL2Trace_cofinalFivefoldSource_quinticThreeWayCostGate`:
strictly separated cofinal windows, their enhanced actual full-H³
dissipation floors, the *same* physical integral costs, and the same three-way
quintic budget gate. Every physical time in each already certified window
now additionally satisfies the exact signed transport bound, retained-viscosity
Riccati bound, drain/energy alternative, and cubic energy charge if E'≥0.

This does not prove a terminal bound on the energy or its derivative and does
not conclude global Navier–Stokes regularity. It identifies the missing
quantitative signed-energy ingredient: ruling out a terminal family with
simultaneously unrestricted negative energy excursions and nonlinear H³
energy amplification.

## Lean checks

Six theorem declarations, 12 axiom audits. No added axiom, sorry or admitted
lemma. The static checks do not replace Lean elaboration in the pinned toolchain.
