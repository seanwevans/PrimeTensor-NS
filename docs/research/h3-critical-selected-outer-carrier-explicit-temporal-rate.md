# Explicit temporal-rate barrier for the actual selected outer carrier

Base: `33c7d43d0d39cfc2a4941d25ce68a2dff69563e1`.

## Mathematical step

The physical outer-carrier proof already forces an instantaneous `sigma^6` H3 viscosity cost under a positive strict excess and nonnegative original annular kinetic deficit. The integrated-compression theorem preserves these signs for some positive interval, but plain continuity supplies no quantitative lower bound on the interval length.

This module states the extra rate information explicitly. Write

`W(t) = ((rho^2 + sigma^2)/2) * actual_sharp_highpass_mass(t,rho)`

`G(t) = actual_annular_kinetic_deficit(b,t,rho,sigma)`.

Assume the actual selected snapshot satisfies `B + margin <= W(x)` and `2 epsilon <= G(x)`, with `margin,epsilon>0`; suppose for `x <= s < T` that

`|W(s)-W(x)| <= LM*(s-x)` and `|G(s)-G(x)| <= LG*(s-x)`, for positive `LM,LG`.

Then the **explicit** interval length

`d = min(margin/(2*LM), epsilon/LG, (T-x)/2) > 0`

preserves half the exact physical margin and a nonnegative deficit, and so

`d * (119 * margin * sigma^6 / 160) <= integral_x^T D_H3(t) dt`.

At arbitrary cofinal selected times `x_k -> T`, finite actual H3 dissipation forces the corresponding **explicit rate cost** to zero:

`min(margin_k/(2LM_k), epsilon_k/LG_k, (T-x_k)/2) * margin_k * sigma_k^6 -> 0`.

The constants are unchanged from the genuine physical Fourier viscous-spike theorem. This result does **not** establish the assumed forward rate bounds; those require new estimates from the projected PDE. It does not show a contradiction or a solution to Navier–Stokes. It isolates a sharp target for a future proof: any candidate bounds on `LM_k` and `LG_k`, plus terminal approach rate, must overcome the sixth-power cost.

## Lean declarations

- `thirdFullPhysical_selectedOuterMargin_explicitTemporalRateWindow244`
- `thirdFullPhysical_cofinalSelectedOuterMargins_explicitTemporalRateCompression244`

Both proofs use the original kinetic observables and actual physical H3 dissipation. No placeholders or new axioms. Compile with the project's pinned Lean/mathlib environment.
