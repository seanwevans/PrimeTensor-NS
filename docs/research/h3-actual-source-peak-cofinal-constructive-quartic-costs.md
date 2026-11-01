# Cofinal source-peak quartic widths and full physical H³ cost

Base checkpoint: `169fe0e8`, the corrected strict-source-peak automatic quartic persistence theorem.

The previous theorem had physical local source ceiling C and spectral H³ state ceiling E as premises. Both are automatically available on **each** prescribed compact strict-time interval:

- `h3Path_actualProjectedMomentumSource_uniformL2OnStrict244` bounds the physical projected momentum source in the real vector L² Hilbert space.
- `h3Audit_initialActualSpectralVelocity_continuousOn` plus compactness of `[t,t+delta0]` bounds the genuine H³-weighted Fourier spectral state.

Consequently every strict physical peak with barrier excess P>0 yields C,E,R,delta with R≥max(1,sigma), 0<delta≤delta0 and R⁴ delta≤1, and actual high-H³ dissipation `D_>sigma(s)>M` throughout the shorter window. These are not terminal-uniform estimates: C,E,R,delta depend on the strict physical interval.

The existing source-driven cofinal theorem (`TerminalActualSourceDropCofinalGradientEnergyGate`) produces one fixed Fourier coordinate and separated source-peak windows `t(vk)→T`, with strict peak margin and `D_>sigma > M` on each old window. Choosing each original window as the compact strict-time interval and applying the new no-ceiling local persistence theorem gives a *constructive quartic* subwindow of width `delta_k` and radius `R_k`. Because `delta_k ≤ oldWidth(vk)`, the shorter windows remain separated.

The full physical H³ dissipation absorbs the new high-radial floor pointwise. The actual extended Lebesgue integral therefore satisfies for every finite m:

    Σ_{k<m} ENNReal.ofReal(M(vk)) * ENNReal.ofReal(delta_k)
     ≤ Σ_{k<m} ∫⁻_{(t(vk),t(vk)+delta_k]} ENNReal.ofReal(D_full(s)) ds.

This uses no time continuity of the unbounded H³ dissipation multiplier and no measurability assumption on a fictitious proxy. It also makes no claim that the right-hand side is finite on the entire terminal tail, or that the weighted width sum diverges. To obtain a terminal contradiction one must supply an independent lower growth rate for the source margin / upper rates for actual PDE source, H³ state, and physical dissipation, sufficient to make the weighted quartic widths incompatible with the global dissipation budget.

Lean declarations:

- `h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions`
- `h3Critical_noL2Trace_cofinalAutomaticQuarticWidths_and_fullDissipationCosts`
- `h3Critical_quarticCofinalCost_finiteBudget_forces_weightedWidthCap`

No new axioms or sorry placeholders. Requires elaboration in the pinned Lean/mathlib toolchain.

## Lean elaboration correction (fix1 at `169fe0e8`)

Two proof terms for `t(v k) + δ k ≤ t(v k) + w(v k)` incorrectly used
`add_le_add_left` to transport the width inequality. Lean produced the
opposite addition order `δ k + t(v k) ≤ w(v k) + t(v k)`. Replacing
these with `add_le_add_right` at the two occurrences proves the goal
in its required syntactic order. Theorem statements and hypotheses are unchanged.
