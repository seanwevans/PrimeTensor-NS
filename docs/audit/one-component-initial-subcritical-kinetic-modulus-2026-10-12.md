# Quantitative initial physical kinetic-energy convergence

Checkpoint: `ab1cf90c` — derive quantitative initial physical momentum convergence rate.

New module:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialSubcriticalKineticModulus.lean`

## Derived conclusions

The existing physical momentum modulus gives an actual physical L² limit
`L` and the quantitative error

`δ(t) = (3 + C_L) M * t^(1-α) / (1-α)`,

under `0 ≤ α < 1` and `E₃(t) ≤ M*t^(-α)` for `0<t≤b`.

The new module proves the elementary norm-square Lipschitz estimate

`|‖x‖² - ‖y‖²| ≤ ‖x-y‖ (‖x‖+‖y‖)`,

then applies the previously established exact equality

`velocityH3Energy0At u t = ‖old(t)‖²`

at every strictly positive time. It obtains:

- Two-time kinetic modulus:
  `|E₀(t)-E₀(s)| ≤ δ(s,t)*(‖old(t)‖+‖old(s)‖)`;
- Exact right kinetic limit `‖L‖²` and explicit convergence:
  `|E₀(t)-‖L‖²| ≤ δ(t)*(2‖L‖+δ(t))`.

The endpoint trace identification `L = old(0)` is not assumed or
proved by these bounds. If `L=0`, the modulus becomes quadratic in
`δ(t)`.

## Remaining independent fronts

- The subcritical initial H³ energy envelope remains a hypothesis.
- The old-temporal-derivative joint-continuity condition remains a hypothesis.
- Identification with the stipulated physical initial velocity and the
  relative-energy comparison residual are separate obligations.
- The terminal actual-vorticity endpoint is independent.

No sorry, admit, axioms or unsafe code were introduced.

## Validation

Source and ZIP integrity checked. The Lean/mathlib project toolchain is not
available in this artifact environment, so local typechecking and full
`lake build` are required before committing.
