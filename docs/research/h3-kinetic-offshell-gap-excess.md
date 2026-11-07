# Genuine kinetic gap excess forces an adverse off-shell sixth-power H³ flux

**Exact baseline**: `a6dabf895900a82e4cf0068bf21eb9952cb8080f` — native solenoidal sixth-power Fourier global cubic bounds on the existing kinetic annular PDE windows.

## A new three-way margin test, not a global cubic restatement

Let `[t_k,t_k+δ_k]` be the *same* disjoint physical kinetic windows selected by the prior theorem; their genuine viscous charges are `q_k = δ_k M_k/4`. The actual signed physical energy identity and finite-window FTC already prove:

`Q_m = 1 + Σ_{k≤m} q_k ≤ E₃(t₀) + Σ_{k<m} G_k`, unless an original window reaches its genuine Riccati-scale energy state. Here `G_k` is the integral over the **intervening gap** of the actual positive signed full-H³ surplus `max(0, -Transport-2D₃)`.

The new pointwise analytic step invokes the exact PDE and physical low-order transport split, retaining the *signed* third order:

`max(0,-Transport-2D₃) ≤ 24 C_∇ sqrt(E₃) E₃ + max(0,-Transport₃)`.

Instead of assuming that the signed top transport has a global time integral, define the **continuous, compact-gap integrable** lower-order plus η margin:

`L_η(t)=24 C_∇ sqrt(E₃(t)) E₃(t)+η`, with `η>0`.

If the genuine gap integral exceeds `∫ L_η`, the integral-comparison theorem yields a physical time `s` *inside that same gap* with

`η < -Transport₃(s)`.

By the exact minimum-frequency sector partition of the full complex six-orbit solenoidal flux, the same time must have

`η < ((2π)^7/3) 1944 C₁ (E₃(s)+1)^3`.

Therefore, for every finite `m` and every `η>0`, one of three branches holds:

1. A Riccati energy event occurs on an original window `k≤m`;
2. The cumulative viscous charge fits below initial physical energy plus `Σ_{k<m}∫_{gap k} L_η`;
3. Some original gap `k<m` contains an actual adverse top-third sample whose magnitude exceeds `η` and pays the explicit native solenoidal sixth-power energy cost.

This is not a claimed gain in terminal integrability. It keeps the possibly unbounded physical energy and correctly separates the 0–2 transport from the signed third-order commutator.

## Off-shell Fourier localization of branch three

At any such adverse physical sample `s`, the repository's `exists_thirdFullPhysicalSnapshot_offshellTransportPersistence244` supplies ONE real solenoidal Schwartz recovery with the **same actual physical signed third-order transport limit**. For any prescribed sequence of measurable *bounded* common squared-radius annuli with radii `lo_n≤hi_n≤H` and `hi_n-lo_n→0`, their complex sixth-power flux norm tends to zero. Their complementary complex flux converges in signed imaginary part to the full actual physical `Transport₃(s)`.

Thus its complement eventually carries `η < -((2π)^7/3) Im∫_{complement}F₆`. No sign is assigned to every triad; no claim of uniformity over physical times, terminally unbounded shells, or uncontrolled moving outer kinetic cutoff is made. This is an off-shell persistence constraint on the forced adverse branch, **not** an exclusion of that branch.

## Same-window physical conclusion

`thirdFullPhysical_noH3Trace_kineticOffshellGapObstruction244` uses the original no-strong-terminal-H³-trace witness constructor; all the exact kinetic cutoffs, cofinality, positive PDE widths, strict window separation, global extended-dissipation packing, vanishing absolute projected-source L¹ action and uniform moving raw Fourier kinetic mass are retained. The three-way alternative holds for **every** `η>0` on the exact same windows.

The remaining hard analytic problem is to control adverse top-third off-shell transport with a frequency-weighted quantity uniform on the terminal gap family, rather than a fixed-time approximation or the unweighted raw kinetic carrier.

Lean declarations: `thirdFullKineticLowOrderMargin244`, `thirdFullKineticGapSignedSurplus244`, `thirdFullKineticGapLowOrderMargin244`, `thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244`, `thirdFullPhysical_adverseThird_forces_sixthFluxEnergy244`, `thirdFullPhysical_adverseThird_forces_offshellSixthFlux244`, `thirdFull_scalar_gapAggregateOverdraft244`, `thirdFullPhysical_kineticCumulativeMarginOrAdverseThird244`, `thirdFullPhysical_noH3Trace_kineticOffshellGapObstruction244`.

**Verification**: source hygiene, registrar repeatability and package SHA-256 are checked in the supplied script; actual Lean elaboration is not available in the package authoring environment. No `sorry`, `admit` or new axioms were introduced.
