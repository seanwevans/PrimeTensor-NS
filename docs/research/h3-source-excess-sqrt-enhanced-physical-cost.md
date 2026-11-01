# Enhanced actual H³ dissipation on a square-root-calibrated physical clock

Base commit: `a06f46ce` (`TerminalActualSourceExcessDissipationSurplus`).

Let `κ = 3(3+C_L)>0`, with `C_L` the established physical Fourier-Leray coefficient.
For actual high-radial dissipation threshold `M` and prescribed source excess
`Q>0` define the enhanced physical threshold

    M' = M + Q/κ.

## Exact barrier shift

The kinetic-anchored source barrier has the form

    Barrier(E,σ,M) = max(K [1+6E+3(σ² W₃(σ)E+M)],0),
    K = 3+C_L, κ=3K.

Its affine branch increases by exactly `Q` under `M→M'`, while taking
`max(_,0)` increases it by **at most** `Q` for `Q≥0`:

    Barrier(E,σ,M') ≤ Barrier(E,σ,M) + Q.

Therefore a strict actual source peak above `Barrier(E,σ,M)+2Q` still has
source excess `P'>Q` relative to `Barrier(E,σ,M')`.

## Improved actual physical window

For a strict physical peak at time `t`, compact strict-time source norm
ceiling `C`, spectral-state ceiling `E_state`, and an available positive
interval width `w`, define

    A = 3 + C_L (||U(t)||+E_state)
    B = 12 C² + 2(D_full(t)+M')
    P' = ||HighpassSource(t)|| - Barrier(E_kinetic,σ,M') > Q
    R = max(1,σ)+1+sqrt(A²B)/P'
    δ = min(w,R^-4).

The already certified square-root-calibrated physical PDE persistence theorem
then guarantees

    D_>σ(s) > M'      for all s∈[t,t+δ].

Because `P'>Q` and square-root radius is antitone in the source excess,

    δ ≥ min(w, [max(1,σ)+1+sqrt(A²B)/Q]^-4) > 0.

This *lower* duration bound uses a **prescribed source profile** instead of an
unknown actual peak margin. The PDE costs remain local and index-dependent.

## Cofinal physical consequences

The existing no-physical-L²-terminal-trace source-driven theorem provides one
fixed Fourier coordinate and separated full source windows for arbitrary
source mass floors. Choose the threshold `(Barrier(E,σ,M)+2Q)²` (equivalently
call the enhanced-window theorem with profile `2Q`). At every selected start
point the new physical theorem supplies `P_k,A_k,B_k,R_k,δ_k` and
`δ_k ≤ w_k`, preserving the original disjointness. For all selected times:

    D_>σ_k(s) > M_k+Q_k/κ,
    δ_k ≥ min(w_k,[max(1,σ_k)+1+sqrt(A_k²B_k)/Q_k]^-4).

The full real physical H³ dissipation pays the cofinal extended integral cost

    Σ_{k<m} ofReal(M_k+Q_k/κ) ofReal(δ_k)
      ≤ Σ_{k<m} ∫⁻_{(t_k,t_k+δ_k]} ofReal(D_full(s)) ds.

This is an actual source-amplitude-weighted physical PDE persistence estimate.
It does not claim uniform terminal bounds on `C_k,E_k,B_k`, a lower bound on
`w_k`, convergence or divergence of the weighted time series, or global
Navier–Stokes regularity. The no-terminal-trace branch remains explicit.

Lean declarations:

- `h3CriticalSourceExcessEnhancedFloor`
- `h3Critical_sourceExcess_enhancedBarrier_le_original_add_margin`
- `h3Critical_sourceExcess_doublePeak_survives_enhancedBarrier`
- `h3Critical_squareRootRadius_antitone_in_sourceExcess`
- `h3Critical_squareRootClock_width_lowerBound_from_sourceExcess`
- `h3Critical_strictDoubleSourceExcess_enhancedSquareRootPersistence`
- `h3Critical_noL2Trace_cofinalEnhancedSquareRootWidths_and_fullCosts`

The file must be elaborated under the repository's pinned Lean/Mathlib toolchain.
