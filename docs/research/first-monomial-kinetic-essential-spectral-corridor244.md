# Essential top-frequency Landau corridor after kinetic-anchor absorption

Checkpoint: `fc75d9e8` — fixed kinetic negative signed H³ cubic essential obstruction.

## New analytic inequality

For a logged preterminal H³ Navier–Stokes path with kinetic anchor `b`, the existing PDE Young absorption bound gives

`E'/E <= K(b) - (T3 + D)/E`, with `K(b) = (3*C1 + 441*C1^2)*E0(b)`.

The actual physical order-three Landau theorem gives `-T3 <= |T3| <= 4398*C1*sqrt(E)*E3`, and physical top dissipation satisfies `D3 <= D`. Therefore

`E'/E <= K(b) + Rtop(t)`, where

`Rtop(t) = (4398*C1*sqrt(E(t))*E3(t) - D3(t))/E(t)`.

The proof uses the established exact spectral identification `T3 = G3 + 3*M3`. No new Fourier regularity, time measurability, or signs are assumed.

## Essential-time conclusion

Since the measurable physical Riccati excess `U=max(0,E'/E-4422)` has *no integrable a.e. majorant* on any terminal subtail under nonextension, the same must be true for `Rtop` after subtracting the fixed anchor cost. Thus under hypothetical nonextension, for every post-anchor subtail `(d,T)`, every finite `M`,

`NOT (a.e. t in (d,T), 4398*C1*sqrt(E)*E3 <= D3 + M*E)`.

This is a genuinely **essential-time** version of the existing pointwise top-frequency corridor, allowing arbitrary signed `M`. No unproved assertion is made about measurability of the spectral channel functions. The result rules out an almost-everywhere dissipative dominance; it does not give a fixed fraction, duration, or concentration rate of bad times.

Conversely, on a single strict post-anchor tail, a.e. top spectral dominance or a time-integrable a.e. envelope on `Rtop` implies smooth continuation.

## Frontier

The remaining PDE question is to control the adverse top-order commutator against actual top-frequency dissipation on an entire terminal tail, modulo an integrable remainder. Existing spatial Schwartz counterexamples preclude an unrestricted fixed-coefficient absorption bound; a successful argument must exploit temporal evolution, directional cancellation, or additional path structure.
