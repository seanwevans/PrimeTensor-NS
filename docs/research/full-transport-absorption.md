# Full transport absorption

Base: `de4c204e`. New source:
[Control/FullTransportAbsorption.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FullTransportAbsorption.lean).

The previous estimate absorbed K E₃ into ε D₃ with remainder K⁴ E₀ / ε³.
The established lower-order energy bound supplies

    E ≤ 1 + 3(E₀ + E₃).

For any existing transport bound |T_H3| ≤ B E with B ≥ 0, apply that
interpolation estimate with K = 3B. Since D₃ ≤ D, the result is

    |T_H3| ≤ ε D + R,
    R = B + (3B + (3B)⁴ / ε³) E₀.

The exact PDE balance E' + 2D = -T_H3 consequently gives

    E' + (2 - ε)D ≤ R.

These inequalities hold for ε > 0; choosing ε < 2 retains a positive
coefficient on the dissipation term. The zeroth-order energy in R is the
actual E₀, not the normalized total E.

## Supplying the transport bound

The final theorem invokes the closed PDE-pairing/commutator theorem directly.
Given a velocity-gradient envelope h on the energy-class tail, it sets
B = 4422(1 + |h(t)|). It does not ask for an additional unproved transport
frontier. The H³ path, energy-class tail, and gradient-envelope premises remain
explicit. Lower-order transport is included through the full transport bound
and the existing energy comparison.

## Temporal limitation

No time-integrability statement is proved here. The new result is a complete
pointwise transport absorption bound with a visible quartic coefficient cost.
To obtain terminal control from it, a bound on the time accumulation of R (or
an appropriate normalized remainder) is still required. Replacing h with a
coarse sqrt(E) envelope does not automatically supply that bound. This patch
does not claim a stronger unconditional continuation theorem.

Existing library declarations are unchanged. The new source is imported by
the root, and the audit prints the remainder and all three theorem contracts
and axiom dependencies. Static coverage/index checks are available locally;
Lean compilation awaits the user's baseline.
