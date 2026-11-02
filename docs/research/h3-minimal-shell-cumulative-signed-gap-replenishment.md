# Minimal-shell cumulative H³ signed transport replenishment

Baseline: `d094be15` (`force signed H3 transport budget on minimal-shell physical PDE windows`).

The canonical minimal first-crossing windows, with inner radius
`R_k = v(k) + 1`, exact quadratic-sharp width `delta_k`, attained projected-source
maximum, positive last-shell mass and width-averaged Fourier kinetic mass,
satisfy the already proved strict physical PDE budget

    E_3'(s) + R_k^3 < -Transport_H3(s)

at every point of their selected compact physical time windows, eventually.
The exact signed H³ energy equation and Riccati bound imply a pointwise
alternative:

    E_3'(s) <= -R_k^3/2
    OR
    R_k^3/2 < K_Ric * sqrt(E_3(s)) * E_3(s).

New: The local compact-interval derivative-FTC lemma converts the uniform
first alternative to a certified **endpoint** physical energy drain

    E_3(t_k + delta_k) + delta_k * R_k^3/2 <= E_3(t_k).

There is no derivative-continuity or terminal H³ dissipation-integrability
assumption: compact strict H³ time intervals already carry the canonical
derivative-integrability theorem. The energy derivative is integrated only
where there is an actual interval.

Choose a finite prefix index `k0` after which the original cofinal selector
has physical strict time and the existing signed-window obligation. Reindex
this **same selector** by `i -> v(i+k0)`. The existing compact-gap theorem
bounds inter-window physical energy gains by the actual Lebesgue integrals
of the positive signed residual

    max(0, -Transport_H3(s) - 2*D_H3(s)).

The preexisting scalar telescoping theorem then gives, for each `q`, either
one Riccati-heavy instant in the first `q+1` selected windows or

    sum_{i=0}^q delta_i R_i^3/2 + 1
       <= E_3(t_0) + sum_{i=0}^{q-1} integral_{end_i}^{t_{i+1}}
                                 max(0,-Transport_H3-2*D_H3).

The final `+1` uses the established lower bound on physical H³ energy.
The original physical sixth/ninth rates, anchor normalized energy–width
obstruction, and width-averaged energetic shell remain true of the witness
sequence, without replacing its minimal cutoff.

**Not proved:** the Riccati exception is absent, the positive signed gap
transport has bounded terminal integral, the cumulative charge is divergent,
or an unconditional H³ regularity result. All those are independent hard
frontiers.
