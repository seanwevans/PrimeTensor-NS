# Actual low-radial Leray source: finite-sum kinetic estimate

Base commit: `7fc30a4e` (`TerminalLowRadialQuadraticKineticBound`).

**Result.** For `hH3 : LoggedPreterminalH3PathAdmissible u T`, an energy
class `PreterminalH3EnergyClass u a T`, any fixed anchor `b∈(a,T)`, any
nonnegative radius `ρ`, strict later time `t∈(b,T)`, output component
`i : Fin 3` and frequency `ξ` with `h3FourierGradientMagnitude ξ < ρ`,

`‖h3RawFinLerayOuterProductDivergence (U t) (U t) i ξ‖ ≤ 18 * (ρ * velocityH3Energy0At u b)`

where `U t = h3AuditActualSpectralVelocityTotal hH3 t` is the ACTUAL
weighted Fourier velocity. The intermediate genuine outer-product divergence
bound has constant 3.

## Exact factors

- Each raw velocity convolution `û_k * û_j` is bounded by `E₀(b)` at every frequency, by the previous proof's exact Hilbert pairing and monotone kinetic energy.
- Every radial Fourier derivative symbol costs at most `ρ` on the actual radial ball.
- Three convolution-derivative terms in one finite divergence sum cost `3ρE₀(b)`.
- Each `h3LerayCoefficient` has norm at most `2`, and each final coordinate sums three such entries: `3 × 2 × 3 = 18`.

## Scope

This is a pointwise Fourier kinetic-Bernstein estimate for the ACTUAL Leray
forcing, not merely an abstract cutoff hypothesis. It does **not** yet
prove spatial Fourier `L²` over the radial ball, physical inverse-Fourier
low-pass `L²`, or terminal time `L¹` of the low-pass projected momentum
source. Those are distinct next steps. Nor does it assume positive terminal
kinetic mass or an H³ endpoint bound.

## Verification

Archive, registrar, index, Lean and full baseline must pass on the repository's
pinned local toolchain before committing. In this patch-building environment,
Lean/Lake is not installed; compilation is unverified.
