# Minimal first-crossing H³: Riccati clock versus exact physical source rates

**Baseline:** `85a7e3d5` — force intrinsic physical clock or quadratic H³ anchor at minimal Riccati peaks.

## Main new obstruction

The original exact minimal first-crossing selector carries its physical sixth/ninth rate gate:

- either the actual disjoint cubic charges `sum_k δ(vk)*Rk³/2` are unbounded;
- or for each `ε>0`, eventually each index obeys the physical-time compression `Rk³ (T-tk)/4 <= ε`, the twelfth-power linear coefficient barrier, or the ninth-power quadratic coefficient barrier.

On every actual Riccati-heavy window the accepted inverse-root argument proves

`Rk² < 4 (4 K_Ric²+1) E₃(tk) OR 16 < (T-tk) Rk`.

In the second arm, with `Rk>=1`, we have `Rk³ (T-tk)/4 > 4 Rk² >= 4`, so the `ε=1` time-compression cap is impossible. Thus in the bounded-cubic-charge branch, every sufficiently late Riccati-heavy window satisfies one of:

1. **Quadratic anchor**: `Rk² < 4(4K_Ric²+1)E₃(tk)`;
2. **Actual twelfth-power rate**: `Rk¹² <= 512(2304 E₃(tk) Ck² (Nk+2)¹⁰ + 1)`;
3. **Actual ninth-power rate**: `Rk⁹ <= 16(36 Ck² ((Nk+2)⁸ + (Rk+1)⁸) + 1)`.

All terms refer to the *same* physical PDE source maximum `Ck`, minimal outer cutoff `Nk`, and first-crossing time `tk`.

## Improved recurrence premise

The left arm of the existing sixth/ninth rate gate already says the *prefix* cubic sums are unbounded. The new scalar lemma shows that any nonnegative sequence with unbounded finite-prefix sums has unbounded sums on **every finite-shifted tail**. The physical window widths and cubic amplitudes are positive. Hence this rate-gate branch supplies `h3CriticalMinimalShellEveryTailCubicChargeUnbounded` automatically and no longer needs that premise repeated in the signed-gap recurrence theorem.

In this branch, **bounded positive signed-gap replenishment alone** forces recurring Riccati-heavy windows, and therefore recurring quadratic-anchor or inverse-terminal-frequency clocks.

The package is a disjunction between two *physically grounded* regimes. It neither asserts that the positive gap transport is bounded nor concludes unconditional regularity. No globally finite terminal H³ dissipation budget is assumed.

## Theorems

- `h3Critical_scalar_intrinsicClock_excludes_cubicTimeCap`
- `h3Critical_minimalShellRiccatiClock_excludes_compressedRateArm`
- `h3Critical_scalar_unboundedNonnegativePrefix_forces_everyTail`
- `h3Critical_minimalShellPhysicalRates_refine_RiccatiClock`
- `h3Critical_noL2Trace_minimalShell_riccatiClock_sourceRateDichotomy`

The source and audit script require the pinned project Lean/mathlib for final verification; the packaging environment does not contain `lake` or `lean`.

## Lean elaboration correction (base `85a7e3d5`)

The multiplication monotonicity argument for `4 <= 4*R^2` now
uses an explicit `4*1` intermediate term and a typed nonnegative
multiplier `(0 : Real) <= 4`. This avoids an uninstantiated multiplier
metavariable from the previously untyped `by norm_num`. No theorem
statement or mathematical hypothesis changed.
