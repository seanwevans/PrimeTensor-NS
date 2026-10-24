# Physical normalized velocity and exact angular source

Baseline: `6aceff13` (`derive conditional physical terminal L2 trace from transverse source variation`).

## Main identity

On strict positive times with `E0(t) = ‖U(t)‖² > 0`, take the established
strong physical Hilbert momentum equation and exact kinetic energy balance:

- `U'(t) = R(t)`;
- `E0'(t) = -2 D0(t)`;
- `R(t) = -(D0(t)/E0(t)) • U(t) + Q(t)`;
- `inner ℝ U(t) Q(t) = 0`.

Set `N(t) = E0(t)^(-1/2) • U(t)`. Applying real scalar inverse/sqrt
differentiation followed by the Hilbert-space scalar product rule gives

`N'(t) = E0(t)^(-1/2) • Q(t)`.

The `D0` coefficient cancels **exactly**; this does not require estimating the
norm of `R(t)`. Moreover `‖N(t)‖ = 1`, `inner ℝ N(t) N'(t) = 0`, and
`‖N'(t)‖ = ‖Q(t)‖/sqrt(E0(t))`.

## Interval geometry

Under a strictly positive canonical terminal kinetic limit `L`, the
normalized direction is C¹ on every strict compact interval and obeys

`‖N(t) - N(s)‖ ≤ ∫_s^t ‖E0(r)^(-1/2) • Q(r)‖ dr`.

Because `E0(r) ≥ L > 0`, the instantaneous angular velocity is bounded by
`‖Q(r)‖/sqrt L`. This identifies the proper finite-variation criterion for
the momentum direction.

The previous conditional L² trace theorem also yields the normalized terminal
direction `V = U_T/sqrt L`, with `‖V‖=1`. No H³ endpoint trace, angular
integrability, or smooth continuation is asserted.

## Audit

The registrar adds the module import to `PrimeTensor.lean` and
`tools/audit/FirstMonomialTriad.lean`, plus `#check` and `#print axioms`
for the new definition and seven theorems. Execute `proof/generate_index.py`
before full build/commit.
