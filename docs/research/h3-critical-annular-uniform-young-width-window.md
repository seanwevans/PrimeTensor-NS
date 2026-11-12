# Uniform actual-time Young-width windows at fixed finite Fourier radius

**Parent:** `91db857015a312aee6619c61397fec96d48af2ea`.

## Exact analytic input

The previous module proves for every `0 ≤ rho ≤ sigma ≤ R`

\[
 |Y_{\rho,\sigma}(U)-Y_{\rho,\sigma}(V)|
 \leq C_R(U,V)\,\|U-V\|_{H^3},
\]

where `Y` is the original cubic-weighted nonlinear Leray Young-gap **plus**
the physical raw-Fourier velocity-width integral, and `C_R` is independent of
the chosen pair of radii. Neither `Y` nor `C_R` is replaced by a surrogate.

The coefficient `C_R(U, V)` is jointly continuous in the state arguments;
the new file proves the needed fixed-second-argument direction explicitly,
using the true Fourier-residual strong continuity and a finite coordinate sum.

At any strict physical time `x`, let `U(t)` be the actual weighted Fourier H³
state and `L = C_R(U(x),U(x)) + 1 > 0`. By physical-time continuity, on a
small enough time neighborhood one has simultaneously

\[
 C_R(U(t),U(x)) \leq L,
 \qquad \|U(t)-U(x)\|_{H^3} < \varepsilon/L.
\]

The previous two-state estimate now gives, for **all** radii inside the ball,

\[
 |Y_{\rho,\sigma}(t)-Y_{\rho,\sigma}(x)| < \varepsilon.
\]

The neighborhood is converted to a common nonempty right window wholly
inside `(0,T)`. A common strict upper margin at the snapshot persists on
that entire window without choosing separate `delta_(rho,sigma)`.

## Simultaneous physical highpass control

The actual physical highpass is contractive in real three-coordinate L²,
so the genuine kinetic highpass mass satisfies for every cutoff `rho`

\[
 |M_\rho(s)-M_\rho(t)|\leq
 \|V(s)-V(t)\|_2(\|V(s)\|_2+\|V(t)\|_2),
\]

where `V` is the physical real Hilbert velocity. No factor of two or Fourier
representative substitution is needed. Strong strict-time physical L²
continuity supplies a **second** radius-independent temporal neighborhood.
Taking the minimum of that neighborhood and the Young-width common window
gives **one actual right-time interval** on which BOTH original quantities
have arbitrarily small preassigned errors for ALL bounded annuli. The radius
of this common interval is positive for every fixed snapshot and finite `R`.

## What this does not close

- This window controls the exact Young-width term. The matching radius-independent highpass modulus is now proved, but the
  polynomial excess/deficit identities must still be combined with the two
  common estimates to transport **strict excess** and the complete annular
  kinetic deficit with explicit margins.
- The window depends on fixed `R`, the snapshot and `epsilon`. No lower bound
  survives automatically as `R → ∞`, and no H³ continuation follows.
- This patch adds no axioms or placeholders and requires successful Lean
  kernel compilation on the repository's pinned toolchain.
