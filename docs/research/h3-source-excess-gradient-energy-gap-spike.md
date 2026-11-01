# Source-window overdraft forces a physical gradient/energy gap spike

Base: accepted `9416cc82` (`TerminalActualSourceExcessGradientTransportBudget`).
This patch is independent of the not-yet-accepted single-span module.

Let `a_k=t(v k)`, `e_k=a_k+δ_k`, `E(s)=velocityH3EnergyAt u s`,
`C(s)=4422*(1+|h3PathCanonicalSqrtEnergyGradientEnvelope u s|)` and
`H_k=h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))`.
The committed theorem gives the finite alternative:

    large Riccati-energy witness on some [a_k,e_k], k ≤ m,
    OR ∑_{k≤m} H_k δ_k + 1 ≤ E(a_0) + ∑_{k<m} ∫_{e_k}^{a_(k+1)} C(s) E(s) ds.

The separated nonoverlapping windows satisfy

    ∑_{k<m} (a_(k+1) - e_k) ≤ a_m - a_0.

For any *proposed* nonnegative scalar ceilings C,U, if

    E(a_0) + C U (a_m-a_0) < ∑_{k≤m} H_k δ_k + 1,

then the same witnesses force either:

1. an actual Riccati-energy observation on one of the first m+1 source windows; or
2. a real time s inside one of the m intervening gaps where
   `E(s)>U` **or** `4422*(1+|h(s)|)>C`.

The result is a quantitative physical *pointwise* gate. It does not assert
that the overdraft premise occurs; the source charges may be tiny because the
window widths may be tiny. It does not infer bounded physical H³ energy or
continuation. The trichotomy is a necessary estimate, not a contradiction.

Lean candidates:
- `h3Critical_scalar_adjacentGapWidth_telescope`
- `h3Critical_scalar_finiteGapOverdraft_forces_actualSpike`
- `h3Critical_scalar_positiveProductSpike_split`
- `h3Critical_noL2Trace_cofinalQuintic_gradientEnergyGapSpike`

The pinned Lean/mathlib build is required; the local checks are structural only.

## Lean correction (fix1, base `9416cc82`)

The final scalar accounting comparison adds the initial energy on the
left of the gap sum. The matching Mathlib congruence is
`add_le_add_right hSum Einitial`, not `add_le_add_left`, which produces
the reversed addition order and fails elaboration. In the independent
positive-product lemma, rename the unused nonnegative coefficient
hypothesis to `_hC` to eliminate its linter warning. No theorem
statements or analytic assumptions change (only the binder name).
