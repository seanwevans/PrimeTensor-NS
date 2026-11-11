# Actual Fourier L² closure of the bounded-annulus Young-gap integral

Accepted base: `43f6d60b9a5550f650717e2084357b53860cfdf5` — localize actual critical H³ Young gap on bounded Fourier annuli.

## Mathematical increment

The preceding module proved the pointwise and integrated annular inequality, but the integral theorem explicitly assumed three fixed-time local square-integrability conditions. These hypotheses were not terminal assumptions, yet they were not discharged automatically.

For a genuine strict physical H³ time, let `Z` be its existing raw velocity Fourier `L²` state, `N` the genuine Fourier Leray forcing `L²` state, `L` its Fourier Laplacian `L²` state, and `R` the actual projected physical momentum source in Fourier `L²`.

The established Fourier multiplier representation is `L(ξ)=-q(ξ) Z(ξ)` almost everywhere. Consequently the exact Young-gap field has a **concrete, quotient-safe L² state**

    G = N - 2 L,
    G(ξ) = N(ξ) + 2 q(ξ) Z(ξ)  almost everywhere.

The constant-rate error has a separate concrete L² state

    E = R - rate · Z,     rate = (lo+hi)/2.

Therefore both `|E|²` and `|G|²` are integrable in frequency. For any measurable band `S` with `q(ξ) ≤ hi` on `S`, the nonnegative multiplier obeys

    ∫_S q³ |G|² ≤ (max(hi,0))³ ∫_S |G|².

The third required density `|Z|²` is integrable without even a band constraint.

Combining these facts with the committed pointwise annular theorem proves the **same integrated inequality without the three extra integrability hypotheses**:

    lo³ ∫_S |R-rate·Z|²
      ≤ 2 ∫_S q³ |N+2qZ|²
        + 2 hi³ ((hi-lo)/2)² ∫_S |Z|²,

assuming only `0 ≤ lo ≤ q ≤ hi` on a measurable band, plus the actual strict-time physical H³ path.

## What remains mathematically open

This eliminates a proof obligation at each finite frequency band, **not** the terminal concentration mechanism. As `hi → ∞`, the cubic weight bound grows like `hi³`, and the midpoint width term grows according to the annulus thickness. There is still no cutoff-uniform control of the Young-gap integral, no low/high physical compensation bound for the *moving annular* multiplier, and no terminal H³ continuation theorem.

A useful next target is to match the annular physical source error to the sharp Plancherel kinetic projector and isolate what must be paid on the annulus complement. This will require tracking the true moving outer cutoff rather than erasing it.

## Registration

Six Lean declarations are registered, including the bounded-band `L²` weight estimate, the three genuine physical integrability results, and the unconditional-integrability wrapper of the accepted annular theorem.

No new axioms or additional PDE hypotheses. Lean must be elaborated in the repository's pinned toolchain; local source and registration checks are not kernel verification.
