# Full physical H³ dissipation exposure on exact canonical disjoint windows

Base commit: `efa06ea1` — force canonical H3 physical dissipation escape and normalized anchor rate.

## New physical estimate

The exact-anchor cubic witnesses give the same strict disjoint intervals
`I_k=[τ(v k), τ(v k)+δ(v k)]` inside `(a,T)`, where the full physical H³
dissipation `D₃(t)=velocityH3DissipationAt u t` is nonnegative and explicitly
interval-integrable on `[a,T]`. The already proven *full integral* disjoint
sum theorem, rather than the cubic height-floor summation theorem, implies

    ∑ₖ ∫_{I_k} D₃(t) dt ≤ ∫_a^T D₃(t) dt < ∞.

Consequently `I_k^phys := ∫_{I_k}D₃(t)dt` is summable and tends to zero.
This is a statement about the actual physical viscous dissipation, not a
surrogate annular height `δ R³/2`.

By the same exact-anchor three-quarter-cubic first crossing,

    D₃(τ(v k)) > 3(v k+1)³/4 → +∞.

The normalized **actual dissipation exposure time** therefore satisfies

    [∫_{I_k} D₃(t)dt] / D₃(τ(v k)) → 0.

The previously proved persistent annular floor gives the sharp lower charge

    δ(v k)(v k+1)³/2 ≤ ∫_{I_k}D₃(t)dt.

These statements coexist because the source-aware sharp persistence widths
can shrink rapidly. They do not establish a uniform time continuity modulus
for the full (unbounded) H³ dissipation, nor a lower bound proportional to
the *left-endpoint total* H³ dissipation.

## Conditional relative peak exposure lemma

For any nonnegative summable integral mass `I_k`, a separately established
relative persistence charge `θ height_k width_k ≤ I_k` with `θ>0` forces
`height_k width_k → 0`. This diagnoses the exact missing estimate needed
to turn high physical pointwise dissipation into integrated cost at its
actual peak level. **No such relative persistence premise is asserted.**

## Formal statements

- `h3Path_disjointNonnegativeWindows_fullIntegral_summable244`
- `h3Path_scalar_summableMass_divergingHeight_exposureCollapse244`
- `h3Path_scalar_relativePeakCharge_forces_heightWidthCollapse244`
- `h3Path_noL2Trace_exactAnchor_actualPhysicalExposureCollapse244`

The full theorem keeps the original `LoggedPreterminalH3PathAdmissible`,
`PreterminalH3EnergyClass`, positive terminal kinetic mass, no strong L²
trace, and finite full H³ dissipation hypotheses. The critical ninth/eighth
annular-width cap, geometric noncompression, and PDE rate ceilings are **not**
assumed. It is not an unconditional continuation or blowup proof.

The ZIP file was checked for integrity and the registrar for idempotence;
local Lean/Mathlib compilation still must be run in the pinned project.
