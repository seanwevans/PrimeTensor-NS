# Physical H³ signed transport versus fast energy decay

**Base:** `0c9d9c7a` — derive normalized physical H3 dissipation clock from radial dominance.

## Exact PDE identity and normalized radial witness

Let `E(t) = velocityH3EnergyAt u t`, `D(t) = velocityH3DissipationAt u t`, and
`T_H3(t) = velocityH3TransportDerivativeAt u t`. The exact energy balance was
already formalized as

    deriv E t + 2 * D(t) = - T_H3(t).

Under the explicit assumption that the actual physical kinetic L² velocity
has **no strong terminal trace**, the moving-radial witness from the previous
checkpoint gives `D(t_n)/E(t_n) > n+1` for `n >= 1`, at times `t_n -> T`.
This is a single witness, not a newly selected one at each later step.

The balance implies the exact exhaustive alternative

    deriv E(t_n) < -(n+1) * E(t_n)
    OR
    -T_H3(t_n) > (n+1) * E(t_n).

Indeed, if the first inequality fails, `deriv E >= -(n+1) E` and
`2 D > 2(n+1) E`, whence the adverse signed transport exceeds `(n+1) E`.
No choice of the transport branch is made uniformly across all `n`.

## Endpoint criterion

For any strict anchor `b` and real coefficient `B`, suppose all later times
satisfy both

    deriv E(t) >= - B * E(t)
    -T_H3(t) <= B * E(t).

If the physical kinetic L² terminal trace did not exist, the sequence's
signed alternative would violate one of these bounds arbitrarily close
to `T`. Therefore the actual velocity has a strong physical L² terminal
trace `U`, and its squared norm is exactly the canonical terminal kinetic
mass. The zero-terminal-mass case is covered by the earlier alternative.

This is a **conditional kinetic-trace criterion**, not smooth H³ continuation
and not unconditional 3D Navier--Stokes regularity. The remaining hard PDE
question is whether either signed estimate, or a stronger combination,
can be derived from the physical transport/dissipation structure without
assuming it as an endpoint hypothesis.
