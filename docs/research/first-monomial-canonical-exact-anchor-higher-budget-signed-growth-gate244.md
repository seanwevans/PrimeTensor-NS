# Canonical higher-budget spectral escape forces signed H³ growth nonintegrability

Base commit: `a50266d4` — transfer all-orders critical H3 energy cost to actual spectral escape.

The previous all-orders theorem provides, on the exact original disjoint PDE windows, a cofinal sequence `t_k = τ(v k) → T` with `E₃(t_k) → +∞` and spectral Fourier norm escape, conditioned on a real integrable upper envelope for the physical `q^(4+m)` moment, an eventually bounded *attained* projected source, a critical outer cutoff cap, a noncompressed terminal lag, and sufficiently small epsilon.

An integrable positive logarithmic growth rate `max(0, d/dt log E₃)` on the same energy-class interval `(a,T)` would produce uniform terminal H³ control by the existing scalar Gronwall theorem `terminalTailH3Control_of_integrablePositiveLogEnergyGrowthRateOnTail`. The proved finite-coordinate bridge `canonicalH3Tail_of_terminalTailH3Control` would then give a finite uniform scalar `E₃` ceiling on a later tail, contradicting the cofinal energy divergence. Thus the positive logarithmic energy-growth rate is nonintegrable. The exact logarithmic derivative identity transfers this to `max(0,E₃'/E₃)`.

Finally the **exact physical signed energy balance** already proved in `Energy/Balance/Exact.lean`

    E₃'(t) + 2 D₃(t) = - T₃(t)

gives the pointwise identity

    max(0, E₃'(t)/E₃(t)) = max(0,(-T₃(t)-2D₃(t))/E₃(t)).

Therefore the full-dissipation signed transport excess is not integrable on `(a,T)` under the same higher-budget conditional hypotheses. This does **not** assert anything about integrability of the raw unnormalized transport defect, nor does it establish the higher-moment envelope, source bound, cutoff cap or noncompression from Navier–Stokes itself.

New Lean declarations:
- `h3Path_cofinalPhysicalEnergyEscape_excludes_integrablePositiveLog244`
- `h3Path_cofinalPhysicalEnergyEscape_excludes_integrableNormalizedGrowth244`
- `h3Path_cofinalPhysicalEnergyEscape_excludes_integrableFullTransport244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_signedGrowthGate244`

Offline packaging and structural checks only; run the pinned Lake toolchain for full proof verification.
