# Same-witness full physical H³ exposure on two disjoint window families

**Base:** `327dc5bf` — summability of the positive-width endpoint floor charges.

This module advances beyond height-times-width charges: with explicit
`IntervalIntegrable (velocityH3DissipationAt u) volume a T`, the **full**
physical dissipation integrals are summable on both the original fivefold
source intervals and the internal intervals around the already selected
spectral-state maximizers. Its cofinal witnesses are exactly those from
`h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts`.

Write `D₃(r)=velocityH3DissipationAt u r` and

    I_source(k) = ∫_{t(v k)}^{t(v k)+w(v k)} D₃(r) dr,
    I_internal(k) = ∫_{p(k)}^{p(k)+η(k)} D₃(r) dr.

For every finite `m`, each series separately satisfies

    Σ_{k<m} I_source(k)   ≤ ∫_a^T D₃(r) dr,
    Σ_{k<m} I_internal(k) ≤ ∫_a^T D₃(r) dr.

Both are summable and both terms tend to zero. **Do not add the two sums:**
the source and internal intervals may overlap within a fixed index.
Zero-width intervals simply have zero integral.

If the explicit endpoint threshold height

    H(k)=R(k)^2 ε(k)^2/8

tends to infinity, the normalized physical exposure

    I_internal(k) / H(k) → 0.

This is conditional on finite terminal full-H³ dissipation and diverging
height; neither follows from preterminal admissibility. In particular the
result does not supply a uniform lower persistence width, does not exclude
non-spectral alternatives, and does not establish terminal continuation.

## Registered Lean declarations

- `h3Critical_disjointPhysicalWindow_fullMassCollapse`
- `h3Critical_disjointPhysicalWindow_divergingHeight_exposureCollapse`
- `h3Critical_noL2Trace_cofinalFivefold_fullPhysicalTwoWindowExposureCollapse`

The registrar installs one root import and three pairs of declaration/axiom
checks. Run the full local baseline and wait for both Linux CI architectures
and the release publication job before considering the change validated.
