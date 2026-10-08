# Normalized absorption remainder and continuation

Based on `2bc2ab4c`. The implementation is
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/NormalizedRemainder.lean`.

Write E for normalized H³ energy, E₀ for kinetic energy, D for full
dissipation, and B for a nonnegative coefficient satisfying |T_H3| ≤ B E.
The existing spatial absorption estimate is

    E′ + (2 − ε)D ≤ R,
    R = B + (3B + (3B)⁴/ε³) E₀.

For 0 < ε ≤ 2, D ≥ 0 and E ≥ 1 give E′ ≤ (R/E) E.
The existing integrable linear-growth theorem therefore supplies a
SmoothContinuationExtension if R/E is integrable on one energy-class tail.
The new gradient specialization takes B = 4422(1 + |h|) from the closed
commutator estimate and ε = 2. Its coefficient is exactly

    [B + (3B + (81/8) B⁴) E₀] / E.

No separate integrability of B or of the unnormalized R is required by this
statement. The new hypothesis still requires proof for a particular path.
With the coarse gradient envelope proportional to sqrt(E), the quartic term
after normalization is proportional to E₀ E; its integrability is not supplied
by spatial absorption. This does not close unconditional continuation.

The existing Fourier frequency split already supports the closed BKM bound.
No sharper Gagliardo–Nirenberg or frequency-split estimate is added here.
The result isolates the precise temporal input needed to use the preceding
spatial estimate without adding new regularity or PDE assumptions.

Validation: source coverage, generated index, compatibility-path checks, and
whitespace checks are run when packaging. Lean is unavailable in the packaging
environment; the full local baseline remains the compiler and axiom check.
