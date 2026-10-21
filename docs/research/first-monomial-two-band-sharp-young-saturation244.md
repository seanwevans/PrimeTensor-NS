# Sharp H³ Young near-saturation forces two-band Fourier mass depletion

Base commit: `5422d833` — physical two-band Fourier radial variance.

## Actual Fourier mass inputs

At an admissible H³ time write

- `E₀ = ∫ S`, where `S` is physical Fourier velocity mass;
- `E₂ = ∫ q² S`, `D₃ = ∫ q⁴ S`, and `F₁ = E₀D₃-E₂²`;
- `q(ξ) = (2π)²‖ξ‖²`;
- `ΔY = D₃+(27/256)K⁴E₀-KE₃`, the *actual* sharp Young gap.

For `lo<hi` consider two disjoint radial frequency bands

    B_low  = {ξ | q(ξ)² ≤ lo},
    B_high = {ξ | hi ≤ q(ξ)²},

and their actual physical Fourier masses `M_low` and `M_high`. Put
`m = min(M_low,M_high)`.

The preceding two-band physical variance theorem proves

    F₁ ≥ E₀ m ((hi-lo)/2)².

The independently proved exact sharp Young defect decomposition yields

    27 K⁴ F₁ D₃² ≤ 256 D₃³ ΔY.

Combine the two inequalities and cancel positive `D₃²` (without
assuming a positive lower bound on either band mass):

    27 K⁴ E₀ m ((hi-lo)/2)² ≤ 256 D₃ ΔY.

If `ΔY≤δ`, then for `K>0, E₀>0, D₃>0`:

    min(M_low,M_high)
      ≤ 256 D₃ δ / (27 K⁴ E₀ ((hi-lo)/2)²).

This is a **quantitative necessary spectral-concentration condition for
near-saturation of the optimal H³ Young inequality**. The final theorem
specializes the coefficient to the actual physical Landau multiplier
`K = 4398 C₁ sqrt(E)` and proves positivity from `C₁>0` and `E≥1`.

## The remaining hard-math frontier

An *upper bound* on the Young gap at specific physical times has NOT been
established. Neither does the present module prove persistence of low- and
high-frequency masses under Navier–Stokes evolution, an integrable terminal
remainder, or unconditional continuation. Dynamic shell collapse vs. a
quantitative PDE-enforced mass spread remains open in this proof program.

## Source-level verification

Registration adds the root module import plus `#check` and `#print axioms`
for the four new theorems. Run index generation and checks, fragment check,
module `lake env lean`, full `lake build`, and baseline audit. No `.sh`
files are included in this ZIP.
