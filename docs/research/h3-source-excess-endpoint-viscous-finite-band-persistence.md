# Cofinal H³ endpoint dissipation spike: finite-band integrated persistence

**Base commit:** `c482134c` — source-peak spectral excursions pay either the physical finite-band PDE clock or actual H³ dissipation at the source anchor / attained spectral maximum.

## Why this is not a full-dissipation continuity assertion

The full actual H³ dissipation `D(s)=velocityH3DissipationAt u s` is an unbounded Fourier gradient multiplier of the genuine weighted H³ spectral state. Norm-continuity of that state does **not** automatically imply norm-continuity of the gradient multiplier. Earlier conditional results that assumed continuity of `D` do not supply it here.

However, existing physically grounded results prove:

- `h3Path_actualHighRadialDissipation_tendsto_zero_fixedTime244`: at each **fixed strict time** `s`, the high-radial H³ dissipation beyond `(N:ℝ)+1` tends to zero as `N→∞`.
- `h3Path_actualRadialDissipation_partition244`: actual low-band dissipation plus actual high-band dissipation equals the **full physical** `D(s)`.
- `h3Path_actualLowRadialDissipation_continuousOn_positiveTime244`: each **finite-cutoff** low-band dissipation is continuous in strict physical time.
- `h3Critical_extendedConstantWindow_eq_heightWidth` and `h3Critical_extendedWindowCost_of_pointwiseFloor`: a real positive floor on a right-hand physical interval pays a genuine full-dissipation extended integral.

## New unconditional local theorem

If an actual strict-time observation has `H<D(s)` (where `H` is any real threshold), then some **finite** cutoff `N+1` captures enough dissipation already at `s`:

    H < D_low(N+1,s).

By continuity of this actual low-frequency physical quantity, some positive right-hand time width `η>0`, with `s+η<T`, satisfies **for every r in [s,s+η]**:

    H < D_low(N+1,r) <= D(r).

Consequently the genuine full viscous ENNReal cost is at least

    ofReal(H) * ofReal(η) <= ∫⁻ r in (s,s+η], ofReal(D(r)) dr.

For the endpoint-viscous spectral-excursion branch from the predecessor, define

    H = R² ε² / 8.

Since `R>0` and `ε>0`, this height is **strictly positive**. The branch `R²ε² < 8D(sState)` now has its own actual finite-band-captured positive persistence interval and full-H³ integrated charge.

## Exact cofinal transfer

The main theorem keeps the same attained maxima, exact physical `A_k/B_k` coefficient identities, calibrated windows and widths, disjointness of those **original short** windows, and their existing summed physical dissipation cost. For every selected k, positive `R,ε` satisfying the accepted spectral-threshold condition, the unchanged alternatives remain:

1. Existing Riccati, compression, cutoff, spectral-anchor or source-anchor/source-excursion, instantaneous dissipation or source-floor branch;
2. Finite-band actual PDE source clock;
3. Full H³ dissipation spike at the original source peak;
4. **New:** an attained-maximum full-H³ spike, now with finite-cutoff dissipation persistence of positive width and its own integrated cost.

The new right-hand intervals at `sState(k)` may cross or overlap original short windows or intervals from other indices. Their costs are **not added** to the original disjoint-window sum without a separate nonoverlap argument. Neither their widths nor Fourier cutoffs are uniform near terminal time.

## Declarations

- `h3Critical_fullViscousSpike_has_finiteRadialCapture`
- `h3Critical_fullViscousSpike_has_finiteBandIntegratedRightWindow`
- `h3Critical_endpointViscousSpike_atMax_has_integratedCost`
- `h3Critical_noL2Trace_cofinalFivefold_endpointMaxIntegratedCostGate`

Registrar adds four `#check` and four `#print axioms`. Lean elaboration requires the pinned local toolchain.
