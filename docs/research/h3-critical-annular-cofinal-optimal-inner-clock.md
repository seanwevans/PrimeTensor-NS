# Cofinal annular clocks: optimal inner-radius normalization and terminal-tail width

Base commit: `926f5b01ca97de77424323591fd34bfb91d15be7`.

## Exact PDE normalization

The accepted physical self-calibrated annular clock uses

`C(b,rho,H) = max 1 (E_b * (rho^2)^3 * S_b(H))`,

where `E_b = velocityH3Energy0At u b >= 0` and `S_b(H) = thirdFullPhysicalOuterViscousCapSlope244 u b H` is nonnegative for `H >= 0`. Consequently `C(b,rho,H)` is monotone in `rho >= 0` and, for `epsilon>0`, its normalized height `epsilon/C(b,rho,epsilon)` is antitone.

In a family `0 < radiusMin <= rho <= sigma <= R`, the **largest** guaranteed viscous-height floor therefore occurs at `rho=radiusMin` (and `sigma=radiusMin`, which belongs to the assumed family). This is a statement about the actual physical normalization, not a surrogate Fourier quantity.

## Terminal-tail compression

If a genuine physical dissipation density `D>=0` is integrable on `[a,T]`, and its pointwise height on `[x,x+delta]` is at least `H`, then

`delta * H <= integral_[x,T] D`.

For `H=epsilon/C(b,radiusMin,epsilon)>0`, this yields the exact upper bound

`delta <= integral_[x,T] D / H`.

The cofinal extraction theorem is applied with the selected inner and outer radii **both** equal to `radiusMin k`; its extracted windows are still uniform for all annuli in each index's bounded family. On these windows the physical PDE self-calibrated gate proves the optimal floor and hence the terminal-tail estimate. The previous disjoint-clock summability and convergence of actual local dissipation to zero are retained unchanged.

## What is proved and what is not

The new package registers seven theorems:

- `thirdFullPhysical_outerViscousCapSlope_nonneg244`
- `thirdFullPhysical_annularCapClockFactor_mono_inner244`
- `thirdFullPhysical_annularClockHeight_antitone_inner244`
- `thirdFull_scalar_rightWindowHeight_le_terminalTail244`
- `thirdFull_scalar_tailCost_forces_widthCompression244`
- `thirdFullPhysical_actualAnnularDeficit_optimalInnerClockRightWindow244`
- `thirdFullPhysical_cofinalAnnularUniformSnapshots_optimalInnerClocks244`

The cofinal theorem still assumes strict snapshot excess and deficit margins on **every** annulus in the family's interval. It does not infer those margins from spectral escape. Neither the positivity of each selected width nor its terminal-tail upper bound gives a uniform width lower bound. In particular, there is no new contradiction with finite H³ dissipation or unconditional Navier–Stokes continuation.
