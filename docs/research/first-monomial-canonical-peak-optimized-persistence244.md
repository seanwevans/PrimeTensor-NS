# Optimized peak-centered physical dissipation persistence at canonical source maxima

Base: `bec76364` — optimized eighth-power/cubic coercivity at canonical source maxima.

## The local threshold and window

Fix a physical kinetic anchor `b` with `a < b < T`, and let `E = velocityH3Energy0At u b ≥ 0`. At a strict physical spectral peak `s > b` write `A = ‖U₃(s)‖`. Whenever `A ≥ 2` and `A² ≥ 32(E+1)`, the existing strong continuity of the **actual weighted spectral H³ state** supplies a right-hand interval `[s,s+δ]` with `δ > 0`, `s+δ < T`, and `‖U₃(r)-U₃(s)‖ < 1` throughout.

Select the optimized radius **from A/2 at the peak**, not by reselecting a radius at each later time:

    8(E+1) ρ⁶ = (A/2)²,   ρ ≥ 1.

The unit-increment estimate and `A ≥ 2` give `‖U₃(r)‖ ≥ A/2`. The previously proved physical high-frequency dissipation coercivity then gives the fixed positive full-dissipation floor

    H = (ρ²/8) A² ≤ D₃(r)       for s ≤ r ≤ s+δ.

The optimization has the **exact** algebraic normalization

    A⁸ = 16384(E+1) H³,    A²/8 ≤ H.

Compared with the earlier pointwise factor 64, the constant 16384 accounts for reserving half the peak norm during the time interval. It does not depend on time, on k, or on a chosen radius at the observation point r.

## Cofinal disjoint windows and exact finite cost

Any spectrally divergent cofinal sequence after b eventually satisfies the threshold. Discard its finite prefix, select the positive right-hand windows, and apply the already-proved `h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244` to extract disjoint new intervals. The original peak times are retained, except for an increasing subsequence.

If full physical H³ dissipation belongs to `L¹([a,T])`, the generic disjoint nonnegative window lemma charges the **full optimized floor** to the time integral:

    ∀m, Σ_{k<m} d_k H_k ≤ ∫_a^T D₃(r)dr.

Hence `Summable (fun k => d_k*H_k)` and `d_k*H_k → 0`, although `H_k → +∞`. These windows are **new peak-centered windows**, not the original quadratic-sharp annulus windows or the overlapping half-terminal source-maximizer intervals.

## End-to-end conditional source-maximizer theorem

`h3Path_noL2Trace_canonicalWidth_sourcePeakOptimizedPersistence244` packages the preceding construction along the **same canonical physical projected-source maximizing times** as the earlier source-clock theorem. The original noncompression, sixth-order linear-rate, and ninth/eighth annulus-width hypotheses remain explicit. The proof does not assume a uniform H³ time derivative, a terminal source bound, or a positive lower bound on the persistence widths.

The resulting series can converge with arbitrarily small windows. Neither a contradiction with finite terminal dissipation nor Navier–Stokes global regularity is established.

Status: static source checks only; Lean needs local compilation in the user's repository.
