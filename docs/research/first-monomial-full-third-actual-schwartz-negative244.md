# True physical full-third Schwartz noncancellation — strict sign

Base commit: `041040e3` — identify actual full third Schwartz commutator with Hermitian integral.

The prior result identified the **complete actual** real Schwartz cubic H³
commutator, `T(f)=G(f)+3M(f)`, with

    T(f_{ρ,A,B,C}) = 2(2π)^7 ∫_{ℝ⁶} W_ρ(p,-p-r,r) H_projected(p,r;A,B,C) dp dr.

This patch proves the integral strictly negative for appropriately selected
real polarizations and sufficiently narrow **actual** compact Fourier windows.

## New proof components

* The three scalar `ContDiffBump` cutoffs are pointwise nonnegative.
* Nonzero common window product implies the independent Fourier momenta
  belong to the corresponding radius-ρ pair ball around the original sharp
  centers. This is on the axis sup-metric carrier, not an incorrectly
  substituted Hilbert `L²` ball.
* At the exact conserving sharp center, each cutoff equals one.
* The common-window Hermitian density is continuous and integrable on the
  actual Hilbert Fourier-pair product volume. Integrability is inherited
  from six previously proved true Schwartz-sector polynomial integrals
  through their measure-preserving permutations.
* A continuous integrable density which is globally nonpositive and strictly
  negative at one point has a strictly negative global integral, because an
  open neighborhood of that point has positive volume.
* The explicit center triad is `(1,0,0)`, `(1,1,0)`, `(-2,-1,0)`, with the
  original three transverse polarizations. The projected orbit equals
  `-192` there. Its continuity gives a negative radius `R`; selecting
  `ρ=min(R/2,1/8)>0` makes every nonzero window product lie inside that
  negative tube. Choosing sector radius `δ=1/4` satisfies all earlier
  support and disjointness assumptions.
* The resulting witness is the **actual recovered real physical Schwartz
  velocity**, whose physical Fourier divergence is identically zero.
  The complete cubic transport coefficient is strictly negative.

## Scope and what is still open

This is a **static** noncancellation result, not a singular Navier–Stokes
solution. The previously proved amplitude oddness and fixed-kinetic
concentration theorems can convert the witness into a counterexample to a
uniform constant-coefficient static H³ absorption estimate. They do not
imply finite-time blowup or universal unforced regularity. A genuine
unforced spacetime estimate remains a separate research frontier.

The new Lean file is not locally compiled in the assistant environment;
its proof must be checked by `lake env lean` and the project audit.
