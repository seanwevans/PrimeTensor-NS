# Actual H³ moving Fourier corridor from sharp Young near-saturation

Base commit: `649879a4` — force separated physical Fourier band depletion from sharp H3 Young near-saturation.

## Analytic improvement

The previous two-band result bounded only the *smaller* mass among two fixed separated spectral bands. Here the exact physical first-Cauchy variance identity yields a direct Chebyshev-type estimate for the **entire complement of a moving radial-frequency corridor**.

Let `S(t,ξ)` be the actual nonnegative physical Fourier velocity mass, `q(ξ)=(2π)²|ξ|²`, and `E₀=∫S`, `E₂=∫q²S`, `D₃=∫q⁴S`. Let

    F₁ = E₀ D₃ - E₂² ≥ 0,
    A_ρ(t) = { ξ : ρ ≤ |E₀(t) q(ξ)² - E₂(t)| },
    M_far(t,ρ) = ∫_{A_ρ(t)} S(t,ξ) dξ.

The exact identity from `ActualRadialVariance244` and the general centered-sector lower bound from `TwoBandRadialVariance244` imply, for `ρ≥0`,

    ρ² M_far(t,ρ) ≤ E₀(t) F₁(t).

No division is required, so the statement makes sense even if the kinetic mass vanishes. The Fourier moment hypotheses arise from the logged admissible Navier–Stokes path, not newly invented physical axioms.

The first-Cauchy term of the exact Young decomposition gives, for `D₃>0`,

    27 K⁴ F₁ ≤ 256 D₃ Δ_Y,
    Δ_Y = D₃ + (27/256) K⁴ E₀ - K E₃.

If the actual gap satisfies `Δ_Y≤δ`, combine these estimates:

    27 K⁴ ρ² M_far(t,ρ) ≤ 256 E₀ D₃ δ.

When `K>0` and `ρ>0`, divide by the positive coefficient:

    M_far(t,ρ) ≤ 256 E₀ D₃ δ / (27 K⁴ ρ²).

The module also specializes to the *actual* Landau coefficient `K=4398 C₁ sqrt(E)`, whose strict positivity has already been proved. This is stronger than fixed two-band depletion: it bounds all mass outside a moving, solution-selected radial corridor at once.

## Scope and remaining hard math

When `E₀>0`, this corridor is centered at the weighted mean squared-frequency `E₂/E₀` with half-width `ρ/E₀`. A small Young gap can force strong concentration only if the remaining coefficients and chosen corridor width are controlled. The theorem does not prove near-saturation occurs, does not infer uniform spectral thickness, and does not resolve global 3D Navier–Stokes regularity.

The next genuine PDE frontier is a dynamic anti-concentration estimate that prevents this moving corridor from narrowing quickly enough to support a terminal growth sequence. This requires using the signed Fourier evolution rather than only moment inequalities.

## Build and audit

Run `python3 -B tools/audit/register_first_monomial_moving_fourier_corridor244.py`, regenerate the proof index, perform fragment checks, compile this module and the central audit module, build all targets, and execute the baseline audit before committing.
