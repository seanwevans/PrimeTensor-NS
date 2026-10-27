# Critical kinetic-shell mass versus relative frequency

Base: `f3ba10bf` — synchronize width averaged physical shell with ninth eighth PDE cutoffs.

The committed physical cofinal witnesses select a shell `m(k)` within the minimal
first-crossing annulus. Write `R_k=v(k)+1`, `J_k=m(k)+3`,
`L_k=N(v(k))-v(k)`, and `μ_k` for the *raw Fourier kinetic mass* in the
actual shell `[m(k)+1,m(k)+2)` at physical time `τ(v(k))`.

The exact width pigeonhole and Fourier multiplier bound give

`3 R_k³/4 < 4 L_k J_k⁸ μ_k`.

For any fixed `A ≥ 0`, comparison `J_k ≤ A R_k` implies

`3 < 16 A⁸ L_k R_k⁵ μ_k`.

Therefore the proven pointwise dichotomy is

`A R_k < J_k` **or** `3 < 16 A⁸ L_k R_k⁵ μ_k`.

This is the *critical quintic normalization* for the selected unit shell.
If the separate, explicit additional hypothesis
`L_k R_k⁵ μ_k → 0` holds, then `J_k/R_k → +∞`; energetic shells
cannot remain in any fixed inner-frequency multiple. The terminal witness
selector is shared with the existing conditional ninth/eighth PDE cutoff
barrier, whose geometric, linear-rate, and source ceilings are not inferred.

This theorem does not claim `L_k R_k⁵ μ_k → 0` from finite H³
dissipation, and makes no inference of unconditional regularity.

Lean remains to be compiled in the target repository.
