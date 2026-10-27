# Canonical physical projected-source exposure and finite-frequency temporal H³ modulus

Base: `3f91a801b2a78d36bcb8268b3a014d7a4ae23f5d`.

The actually attained, least projected-source envelope on `[a,(a+T)/2]` is `C`.  Existing physical Hilbert momentum FTC and radial Plancherel yield, for every `s` in that window and fixed `ρ≥0`,

```
RadialSquareDefect_ρ(S(a),S(s))
 ≤ 3 * (1 + ρ² + ρ⁴ + ρ⁶) * (C * (s-a))²
 ≤ 3 * (1 + ρ² + ρ⁴ + ρ⁶) * (C * (T-a)/2)².
```

Thus if `C_k*(T-τ_k)/2 → 0`, the actual weighted spectral square defect at any predetermined maximizing times vanishes below every **fixed** radial cutoff. This criterion does not force the full H³ spectral displacement to vanish or control its high-frequency complement. The first-crossing disjoint windows and conditional critical-width spectral-escape alternatives remain on the identical cofinal witness sequence.

Finite H³ dissipation is used upstream for the disjoint-window construction, but **does not imply** `C_k*(T-τ_k)/2 → 0`. The missing high-frequency estimate remains independent.

Proof dependencies: `h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244`, `h3Path_actualSourceWindowEnvelope_pointwise_le244`, and `h3Path_noL2Trace_canonicalWidth_physicalSourceSpectralTemporalBound244`.
