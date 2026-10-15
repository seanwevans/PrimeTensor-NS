# Critical-half balanced shape polynomial under two physical scale actions

**Baseline:** `9e0847e0` (`characterize uniform critical-half Schwartz shape threshold`).

The complete real physical first monomial `M(f)` has velocity-amplitude degree
three and spatial degree four. The true fourth-order Schwartz dissipation
`D(f)` has degrees two and five. The lowest H3 energy `E0(f)` has degrees two
and negative three; the highest H3 energy `E3(f)` has degrees two and three.

Thus the two terms of the division-free polynomial

    B_C(f) = M(f)^12 - C^12 D(f)^12 E0(f)^5 E3(f)

have exact matched amplitude degree **36** and spatial degree **48**:

    B_C(a f) = a^36 B_C(f),
    B_C(f(scale ·)) = scale^48 B_C(f),   scale > 0.

The code reuses the already certified *actual* five-axis-index physical
monomial, full 243-slot fourth-derivative dissipation, complete lowest and
highest H3 square-energy sums, and actual pointwise Schwartz dilation.
It proves physical Point3 divergence freedom is retained under spatial
dilation. Positive B_C therefore persists along any joint positive
amplitude/spatial dilation orbit of the original solenoidal Schwartz shape.

**Limitation:** This polynomial is a scale-invariant diagnostic, **not yet**
the sharp uniform endpoint shape threshold. The previous threshold involves
all four energies `E0+E1+E2+E3`. One must control the intermediate energy
orders (e.g. with an actual proved interpolation inequality) before using
this balanced polynomial to draw universal endpoint conclusions. The patch
does not prove a Navier–Stokes continuation theorem or claim singularity.

Validation: `lake env lean` for the new module, then `lake build` of that
module before `lake env lean tools/audit/FirstMonomialTriad.lean`, then
`lake build`. No `sorry`, `admit`, or new axioms are intended. Compilation
requires the user's Lean/mathlib checkout and has not been performed in
the archive-building environment.
