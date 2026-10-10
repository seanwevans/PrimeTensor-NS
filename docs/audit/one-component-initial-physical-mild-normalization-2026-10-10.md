# Physical-time old H³ mild data -> normalized uniqueness

Parent checkpoint: `9705fec1` — derive initial physical spectral overlap by mild uniqueness.

The previous theorem `h3Audit_initialOldNormalizedMildDataAt_implies_canonicalMildOverlap`
assumes a normalized `[0,1]` H³ spectral path of the actual old velocity,
together with its Picard equation, uniform `2A` bound, and physical matching.

This patch replaces that normalization-specific interface with a bounded
continuous OLD spectral velocity path `P` on the physical canonical restart
interval `[0,R(1,A)]`. It assumes only the corresponding **physical**
heat-minus-Duhamel identity and explicit physical Fourier matching on `(0,b)`.

The key independent, previously proved ingredients are:

- `h3SpectralFinHeatLerayPhysicalOverlapAtRestartRadius_normalized_unique`
  — the normalized physical old mild path equals the canonical Banach path.
- `h3PathPhysicalRealExtension_normalizedPhysical_apply`
  — extending the normalized path back to physical time recovers `P(q)`.
- `h3SpectralFinHeatLerayMildSolutionAtRestartRadius_satisfies_mild`
  — the unique selected path satisfies the normalized Picard equation.

The principal new implication is
`h3Audit_initialOldPhysicalMildDataAt_implies_normalizedMildDataAt`.
It entails the old/selected overlap, actual one-sided H³ spectral trace,
and full-time physical `L²_t Ḣ^(3/2)_x` for both transverse velocity components,
conditional on the same already stated terminal endpoint hypotheses.

**Remaining, not supplied by this patch:** actually constructing the old
physical-time H³ path `P` and establishing its bound, Fourier representation,
and physical mild equation from initial data and appropriate local strong
Navier–Stokes solution assumptions. The published Liu–Zhang continuation
criterion remains a separate theorem bridge.
