# Native signed LowMax sixth flux from an adverse physical H³ snapshot

**Base commit:** `cadf7142f8c51c88ddcbc6acc6bf765022c14c95`.

## Missing physical-to-Schwartz interface

`thirdFullPhysical_adverseThird_arbitraryRadiusTailOrLowMax244` previously
returned solenoidal Schwartz fields and a signed one-sided low-maximum flux
alternative, but **discarded** the strong weighted-H³ spectral approximants
and their exact Fourier identifications. The one-sided closed-gap theorem
requires that spectral data in order to charge its *actual* physical PDE clock,
not merely an arbitrary unrepresented Schwartz flux.

## New high-tail or precisely recovered LowMax flux

At a genuinely adverse physical H³ third-order transport time `t`, fix a
natural radius `R`, an adverse physical margin `eta>0`, and arbitrary positive
recovery tolerances `gamma` and `epsilon`. Write

- `C = (2*pi)^7/3`, the *physical* Fourier normalization;
- `B = 1944*C1*(velocityH3EnergyAt(u,t)+1)`;
- `U(t)`, the actual weighted-H³ spectral state;
- `P_R U(t)`, the actual high-radial tail.

Then either

`eta/2 < C*B*(||P_R U(t)||+gamma)^2`,

or there is a real-solenoidal complexified Schwartz profile `p` and exactly
represented weighted Fourier state `V` such that

- `||V-U(t)|| < epsilon`;
- `V_j = W3*(Fourier p_j)` almost everywhere for all axes;
- the complex spatial Fourier divergence of `p` vanishes at every frequency;
- `eta/2 < -C*Im Phi_LowMax(R)(p)`.

The proof retains the approximation witnesses from
`exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244`, with
strong spectral recovery and Fourier representation. On the prescribed
HighMax(R) complement it uses the exact diagonal mixed-polarization identity
`thirdFullKineticMixedPolarSixthFlux_schwartz244`. The true high-maximum
bound and literal complex integral splitting preserve all signed phases;
neither a spectral-tail-free normalization nor a false pointwise Fourier
representative equality is introduced.

## Original strict physical kinetic-gap consequence

With an independently realized earlier reference `q,W` at time `s` in the
**same original gap** `[x,y]`, the actual adverse top-third observation at
time `t` has the following verified logical alternatives:

1. the actual high-H³ radial tail pays the quadratic physical threshold;
2. an exactly represented, arbitrarily close Schwartz recovery `p,V` exists,
   and its original baseline/clock/viscous trichotomy applies against `q,W`.

The unscaled LowMax one-sided margin is exactly

`mu = (eta/2)/((2*pi)^7/3)>0`.

The third branch of that trichotomy is a *real, inside-gap* annular physical
H³ viscous charge (including its right-endpoint backward clock). The earlier
reference baseline remains explicit; the theorem does NOT claim that `q`
is automatically small, that the growing seventh-power signed-flux
Lipschitz coefficient is controlled, or that cofinal adverse top-third
observations are forced on every late gap.

## Next hard-math obligation

Connect the original *integrated* signed replenishment witness to adverse
physical third-order samples in a cofinal family, and control the reference
baseline and weighted recovery/source cost relative to the physical margin.
The radius/amplitude factors and shrinking annular persistence widths remain
separate; no terminal H³ continuation theorem is asserted.

## Verification

Run `proof/generate_index.py`, the registrar, targeted Lean elaboration,
module Lake build, full Lake build, and fragment audit on the pinned base.
Static packaging checks cannot establish Lean elaboration.
