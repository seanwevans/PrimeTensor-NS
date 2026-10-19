# Sharp endpoint-only lower transport budget for H3 Schwartz realization

Base repository checkpoint: `b242cd75` (reserved kinetic/top-third energy).

## Hard-math increment

The existing coefficient-one adjacent Schwartz energy Cauchy estimates are

    E1^2 <= E0 E2,         E2^2 <= E1 E3,

with E0,E1,E2,E3 the complete sums over 3, 9, 27, 81 differentiated velocity
slots, respectively. For x,y >= 0 and z^2 <= xy, the arithmetic-geometric
mean bound `2z <= x+y` follows directly by comparing the two squares. Hence

    2E1 <= E0+E2,         2E2 <= E1+E3.

Eliminating E1,E2 gives **endpoint arithmetic convexity**:

    3E1 <= 2E0+E3,       3E2 <= E0+2E3.

The exact coefficients from the path commutator estimate satisfy

    6E1 + 18E2 <= 10E0+14E3.

Thus the real-Schwartz realization of an admissible 3D NS H3 path has

    |T1+T2| <= H (10E0+14E3),   H=C1 sqrt(E).

The complete signed balance therefore implies

    E' + 2Dfull <= H (10E0+14E3) - (G3+3M).

Importantly, the **positive slope** proof uses the **exact** signed energy
identity, not this one-sided upper bound.

For M>=0, high unabsorbed normalized growth has the alternative

    (4422+M) E < H (10E0+14E3)
         OR
    2Dfull < -(G3+3M).

A ceiling on the endpoint term rules out the first branch. On hypothetical
nonextension tails, obtaining an actual top-adverse representative at a high
rate requires explicit Schwartz-realization and the endpoint ceiling on the
tail. Neither is inferred from static noncoercivity or formal admissibility.

## Scope and next obstruction

This is a rigorous, division-free upgrade of lower transport to endpoint
energies, not an exclusion of 3D NS singularities. The remaining hard problem
is to control the signed **top** commutator on actual evolving slices or to
derive the endpoint ceiling from dynamic PDE information, rather than assuming
one of these effects.

Run `lake env lean` and the project audit before treating the new theorems as
verified. The patch was authored without a local Lean installation.
