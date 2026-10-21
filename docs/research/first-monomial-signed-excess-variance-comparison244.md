# Actual signed moment excess and anti-concentration comparison

Base checkpoint: `0807d59e` — physical normalized H³ Fourier variance evolution and signed moment excess.

The prior module derives the actual derivative of the normalized radial Fourier variance

    R(t) = 1 - E₂(t)²/(E₀(t)D₃(t))

using the already-closed physical derivative identities for E₀, E₂ and the fourth-radial Hilbert pairing for D₃. Define the **signed middle-moment excess**

    X = 2 E₂ E₂' E₀D₃ − E₂²(E₀'D₃ + E₀D₃').

The exact physical identity is

    R' = −X/(E₀D₃)².

This module registers X as an actual physical observable, not as a hypothetical forcing source, and draws the genuine calculus consequences. Assuming kinetic mass and top dissipation remain positive, an interval-wise bound X≤0 implies that R is nondecreasing, and C=1−R is nonincreasing. In particular, if s≤t both lie in the strict class interval, then R(t)≥R(s)>0. Any alleged normalized sharp-Young gap δ at the later t must therefore obey the explicit barrier

    27 K(t)⁴ E₀(t) R(s) ≤ 256 δ,

when K>0. Thus a normalized near-saturation sequence is incompatible with globally nonpositive signed middle-moment excess after a fixed positive-mass anchor.

There is also a *localized, assumption-light contrapositive*: if R(t)<R(s) for strict preterminal s<t and E₀,D₃ remain positive over [s,t], then X(r)>0 at some r∈[s,t]. This uses the preexisting differentiability closures to apply the monotonicity-by-derivative theorem on [s,t]. No sign estimate for X, uniform anti-concentration, or global Navier–Stokes regularity is asserted.

Audit: run registrar, regenerate proof index, run fragment checks, Lean-check the module, run central audit, full build and baseline audit. All exported results must be checked for axioms. No sorry/admit placeholders.
