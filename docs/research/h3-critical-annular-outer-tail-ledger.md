# Actual three-coordinate H3 annular Young-gap / outer-tail ledger

**Accepted base**: `3350b18548cad3af4004d47b1f32d144f9e613e6` — derive actual annular H³ Young-gap integrability from Fourier L² states.

## Mathematical result

For an actual strict-time physical Navier–Stokes state, write `q(ξ)=(2π)²|ξ|²`, `R_j` for the Fourier transform of the *actual* projected physical momentum source, `Z_j` for the genuine raw velocity Fourier representative, and `N_j` for the genuine Leray forcing. Fix `0 ≤ ρ ≤ σ`, with radial frequency `m(ξ)=2π|ξ|`.

The *actual* sharp highpass `m ≥ ρ` splits disjointly into

* the finite annulus `A={ρ ≤ m < σ}`;
* the outer tail `{m ≥ σ}`.

On `A`, `ρ² ≤ q < σ²`, so the accepted Young-gap theorem applies with `lo=ρ²`, `hi=σ²`, midpoint rate `r=(ρ²+σ²)/2`, and half-width `w=(σ²-ρ²)/2`. The new theorem proves

```
ρ^6 ∫_{m≥ρ} |R_j-r Z_j|²
 ≤ 2∫_A q³|N_j+2qZ_j|²
    +2σ^6 w² ∫_A |Z_j|²
    +ρ^6∫_{m≥σ}|R_j-r Z_j|².
```

It also proves the corresponding *three-coordinate* inequality by summing over `Fin 3`. All integrals exist by the accepted Fourier L² representative constructions and bounded-annulus integrability theorem. No separate `IntegrableOn` premises, terminal H³ ceiling, or outer-tail assumption enter.

## Exact obstruction

The last term is **not** discarded. When σ is moved outward to accommodate spectral excursions, the rate grows as σ² and the cubic width penalty as `σ^6(σ²−ρ²)²/2`. Consequently the ledger is not by itself a uniform continuation estimate: to combine with physical kinetic compensation, one must identify this Fourier highpass mismatch with the genuine real-Hilbert highpass norm (using coordinatewise Plancherel) and control or charge the outer tail separately.

This increment does not assert that the tail vanishes or that the Young gap alone dominates it. It retains the physical source throughout and does not add a PDE axiom or a new regularity hypothesis.

Kernel compilation must be verified in the repository's pinned Lean toolchain. The distributed static checks validate only package structure and registration.
