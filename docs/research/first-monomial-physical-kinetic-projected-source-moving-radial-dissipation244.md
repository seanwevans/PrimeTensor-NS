# Terminal moving-radial H³ mass and physical dissipation cascade

**Base:** `b37fedb6` — identify high radial spectral escape with complementary Fourier integral.

Write `S(t)` for the genuinely encoded physical three-component weighted Fourier H³ velocity and `q(ξ)=|D(ξ)|` for the project-native gradient-frequency magnitude.

The previous commit proved, *conditional on nonexistence of a strong terminal physical kinetic L² trace and a positive terminal kinetic limit*, that for every fixed `ρ≥0`, every terminal subtail and every real threshold, some time has arbitrarily large integrated H³ square mass on `{q≥ρ}`.

## Physical dissipation bridge

The existing canonical density identity is

    spectralDissipationDensity(S(t),ξ) = q(ξ)^2 * squareAmplitude(S(t),ξ).

On `{q≥ρ}` for `ρ≥0`, the pointwise right side is at least `ρ² * squareAmplitude`. At a strict physical H³ energy-class time the density is integrable, and its full Fourier integral is **exactly** the actual physical total H³ dissipation `velocityH3DissipationAt u t`. Therefore

    ρ² * ∫_{q≥ρ} squareAmplitude(S(t),ξ) dξ
         ≤ velocityH3DissipationAt u t.

This is a one-time instantaneous inequality. It makes no claim about the time integral of the higher dissipation near the endpoint.

## Moving radial cutoff and one cofinal terminal sequence

Let `R_n=n+1`. Choose a strict time anchor above both the midpoint `(a+T)/2` and `T-1/R_n`. By the fixed-radius cofinal escape theorem, select `τ(n)` beyond that anchor satisfying

    dist(τ(n),T) < 1/R_n,
    ∫_{q≥R_n} squareAmplitude(S(τ(n)),ξ) dξ > R_n.

The squeeze theorem then gives `τ(n)→T` and the physical dissipation inequality yields

    velocityH3DissipationAt u (τ(n)) > R_n³.

The cutoff is **moving**, rather than frozen: the same sequence exhibits mass growth outside balls whose radii diverge.

## Precisely what is *not* proved

No implication is assumed or claimed from H³ nonextension to failure of strong physical kinetic L² convergence. Even in the no-L²-trace branch, this is a necessary high-frequency/high-dissipation cascade, not a contradiction. The key remaining work is to obtain a dynamical constraint preventing such an escape or to otherwise construct the endpoint kinetic trace.
