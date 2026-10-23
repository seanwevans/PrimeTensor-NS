# Absolute continuity and a.e. weak momentum derivative

Baseline: `a5e9f9ce` — extend physical weak FTC control to L1 temporal momentum errors.

The previous L1 interface retained the premise of an *everywhere* differentiated
scalar weak momentum pairing. A distributional-time construction would naturally
supply only an a.e. derivative. But a.e. derivative alone does not determine a
continuous function (Cantor-type singular paths), so it is mathematically
incorrect to replace the derivative premise without a temporal absolute
continuity hypothesis.

This module makes the missing hypothesis explicit. For each compact solenoidal
`φ`, the actual scalar momentum `fφ(t)=⟨φ,U(t)⟩` is absolutely continuous on
`[a,b]`, with a.e. derivative `⟨φ,R(t)⟩ + eφ(t)`. The individual errors `eφ`
and a shared envelope `g` are L1 on the time interval, with a.e. bound
`|eφ(t)| ≤ g(t)‖φ‖₂`. Applying mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
and `intervalIntegral.integral_congr_ae` yields

    |⟨φ,D(a,r)⟩| ≤ (∫ₐʳ g(t)dt)‖φ‖₂.

The existing density of smooth compact solenoidal tests in the Leray-fixed L2
subspace yields the sharp vector estimate `‖D(a,r)‖₂ ≤ ∫ₐʳ g(t)dt`.
Vanishing cumulative L1 errors imply actual physical weak FTC on every prefix.

**Analytic frontier:** Prove absolute continuity of compactly tested old physical
momentum and its almost-everywhere weak derivative from the preterminal PDE
with the old pressure annihilated distributionally. H3 time continuity or
separate classical regularity alone does not settle that frontier.

The theorem does not assert Navier–Stokes regularity or continuation.
