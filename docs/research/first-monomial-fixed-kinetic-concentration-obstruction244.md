# Genuine obstruction: kinetic energy alone cannot absorb the signed first monomial

**Base:** `c8a40574`, *identify two-state weighted H3 Schwartz cross energies*.

A first-monomial-only estimate of the form

    M(f) <= C D4(f) + K E0(f)

with constants C,K independent of the data cannot hold throughout the divergence-free Schwartz class, even when E0 is fixed exactly.

For the already constructed REAL solenoidal Schwartz quarter packet with M(f)>0, define

    g_t(x) = t^3 f(t^2 x), t>0.

The explicit physical amplitude and spatial-dilation laws prove

    E0(g_t) = E0(f),
    E1(g_t) = t^4 E1(f),
    D4(g_t) = t^16 D4(f),
    M(g_t) = t^17 M(f).

The extra positive power of t in M/D4 makes the inequality fail for sufficiently large t. The proof chooses an explicit t using the original positive monomial and the absolute proposed coefficients; no asymptotic assumption, missing Schwartz hypothesis, or hypothetical counterexample is required.

**Mathematical interpretation.** A kinetic-energy anchor by itself cannot make the nonlinear signed first-monomial coefficient absorbable into fourth-order dissipation. An argument for global Navier--Stokes regularity must exploit evolution, signed cancellation among the *full physical* transport channels, a genuinely stronger control, or another PDE-specific invariant. The result does NOT exhibit a singular solution, nor refute cancellation or absorption for the full nonlinear transport after using Navier--Stokes dynamics.

**Validation:** source-only Lean patch; it must be compiled by the user's Lean 4 + mathlib version before the theorem can be regarded as formally checked.

## Targeted Lean proof repair after `c8a40574`

The scalar comparison `C (t^16 D) + K E < t^17 M` is now a separate
private theorem. The main existential concentration theorem uses the
previously established kinetic/dissipation/monomial scaling equations as
named equalities and closes with a three-step `calc`, rather than asking Lean
to normalize the full Schwartz expressions inside a nonlinear arithmetic
proof. This addresses the earlier 800000-heartbeat `whnf` timeout.

The quarter-packet divergence proof now first transports its real sum into
`ℂ` with the additive `Complex.ofReal` coercion, uses the preexisting
complex-solenoidality theorem, and returns to `ℝ` by `exact_mod_cast`.
This avoids leaving `Complex.re (∑ ...)` unreduced.

These repairs change no public mathematical theorem statements.
