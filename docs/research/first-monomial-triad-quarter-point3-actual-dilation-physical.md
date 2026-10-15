# Physical Point3 dilation of the real H3 Schwartz velocity

Base commit: `338eea54` (actual H3 energy sums).

The previous checkpoint proves the full order 0–3 derivative masses and all
243 fourth-order dissipation slots scale under positive spatial dilation.
Here we pull the same actual real Schwartz scaling through the existing
`h3SchwartzPoint3Scalar` map rather than introducing a proxy physical carrier.

Let `v_j(x) = f_j(h3Point3ToFourierCLM x)` and `v_j^λ` be the
Point3 realization of `lowNormalSchwartzVelocityDilation λ hλ f`.
The new theorem contracts show:

- `v_j^λ(x) = v_j(λ • x)`;
- `spatial3.d i (v_j^λ) x = λ * spatial3.d i v_j (λ • x)`;
- `∑_j spatial3.d j (v_j^λ) x = λ * ∑_j spatial3.d j v_j (λ • x)`;
- if the actual Point3 divergence of v vanishes identically, that of v^λ also vanishes.

All three coordinates are present and all identities use the existing
positive-depth `Axis Depth.three` representation. These theorems do *not*
assert a Navier–Stokes solution for the velocity snapshot. They do *not* yet
prove the signed 243-slot physical first-monomial scaling, which requires
transporting the three derivative factors (orders 3, 2, 2), integrating their
product against the exact inverse-volume Jacobian, and retaining the factor
two from `spatialEnergyPairing`.

The audit registrar also moves all existing audit imports ahead of `#check`
commands, so the audited module has a valid header.

The code uses neither `sorry` nor `admit` nor a new axiom. It has been
source-checked and packaged, but must be compiled in the user's Lean/mathlib
checkout with `lake env lean`, `lake build`, and the audits.
