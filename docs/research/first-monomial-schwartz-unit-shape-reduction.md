# The intrinsic first-monomial shape problem on the unit-endpoint class

Base checkpoint: `9423399f` — normalize intrinsic physical Schwartz critical-half shape orbits.

The exact dimensionless shape ratio is `R(f) = M(f)^12 / (D(f)^12 E0(f)^5 E3(f))`, with the same real Schwartz signed 243-slot monomial and full fourth-order dissipation as the main H3 analysis.

This module establishes an **if and only if** between bounding `R` on *all* solenoidal Schwartz profiles with `E0>0` and `E3>0`, and bounding it by the **same constant** on solenoidal Schwartz profiles with `E0=E3=1`. The proof uses the committed positive-endpoint orbit representative and physical divergence preservation under actual spatial and amplitude transformations, rather than an informal quotient argument.

The exact coefficient-one adjacent interpolation implies on the unit-endpoint class `E1<=1`, `E2<=1`, and `E0+E1+E2+E3<=4`. For positive `D`, the ratio inequality `R<=K` is literally `M^12<=K*D^12`; if `D=0`, the division convention gives `R=0`.

A proposed universal solenoidal critical-half coefficient `C>=0` forces the normalized ratio threshold `R<=(2*C)^12`. Strict excess on a normalized solenoidal Schwartz witness rules it out. These statements do **not** prove the converse to the uniform endpoint estimate, the existence of a universal coefficient, nondegeneracy of E3, or existence of a strict-excess witness. The remaining substantial analytic question is the behavior of the signed first monomial on the normalized class, particularly its interaction with the full top-order dissipation.
