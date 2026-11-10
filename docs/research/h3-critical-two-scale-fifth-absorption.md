# Two Fourier radii absorb half of the actual H³ fifth-order viscosity

Base HEAD: `46693727b82887f6528a3f8cf12b83710cb7fd3f`.

## The missing scale separation

The accepted same-cutoff gate for a critical dyadic net-growth witness r is

  (K + Φ5(r) + Φphase(r)) D3(r)
    < 3(2π)^6 L_rho(E0(b))
      + (2/rho²)(T4(r) + rho² M5(r) + H6_rho(r)).

Here M5=Φ5 D3, T4 is the true fourth-radial temporal square-mass, and H6 is
exactly the highpass square-mass of the q³ velocity state. The identical
forcing and heat cutoffs multiply M5 by 2 on the right, so a naive fifth-
order absorption does not follow.

However the kinetic low-band forcing estimate only needs the forcing radius
rho; the Fourier split of the third-Q heat may use an independent radius
sigma. The exact physical estimate is, at the SAME physical time r and for
ALL rho>0 and sigma>=0,

  (K + Φ5 + Φphase)D3
    < 3(2π)^6 L_rho(E0(b))
       + (2/rho²)(T4 + sigma² M5 + H6_sigma).

Take sigma=rho/2. Then (2/rho²)*sigma² M5 = M5/2. Moving it left yields

  (K + Φphase + Φ5/2)D3
    < 3(2π)^6 L_rho(E0(b))
       + (2/rho²)(T4 + H6_{rho/2}).

This is a real positive viscous fifth-moment coefficient, not a new assumed
upper estimate. The price is that H6 is measured above rho/2 (a larger tail
than above rho). Since the cutoff is chosen AFTER the net-growth witness, no
independent time-selection assumption enters.

Equivalently, the high-sixth residual must exceed the signed charge after
subtracting the kinetic low-band and fourth-temporal costs:

  (K + Φphase + Φ5/2)D3 - 3(2π)^6 L_rho - (2/rho²)T4
    < (2/rho²)H6_{rho/2}.

## Declarations

- `thirdFullKinetic_twoScale_halfFifth_scalar244`: exact scalar radius algebra.
- `thirdFullPhysical_nearCriticalAnchor_forces_twoScaleFifthHeat244`: one
  physical witness, two independently chosen spectral radii.
- `thirdFullPhysical_nearCriticalAnchor_forces_halfFifthAbsorption244`: one
  half of the actual positive fifth dissipation retained on the left.
- `thirdFullPhysical_nearCriticalAnchor_forces_highSixthDeficit244`: precise
  residual high-sixth charge without an assumed high-tail bound.

## Mathematical frontier

The remainder H6_{rho/2} is still the full high-sixth *velocity* Fourier tail
at a strict physical time. It is not uniformly controlled near a possible
terminal singularity by H³ admissibility alone. The fourth-radial temporal
cost T4 is also not absorbed. The new result is a valid coercive separation
and does not prove global regularity or continuation.
