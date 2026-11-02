# Minimal H³ last-shell overshoot versus relative Fourier escape

Baseline: `b09c94ff` (committed minimal H³ last-shell sixth/ninth PDE rates).

The same cofinal, disjoint **minimal first-crossing** windows now export the
last-shell overshoot and its raw Fourier mass as explicit observables:

- `R_k = v(k)+1`, `Q_k = N(v(k))+1`; the shell is `[m(v(k))+1, N(v(k))+1)` with `N=m+1`.
- `omega_k = D_low(Q_k,t_k)-D_low(R_k,t_k)-3R_k^3/4 > 0`.
- `mu_k = M_raw(last shell,t_k) > 0`.
- `omega_k <= 4 (Q_k+1)^8 mu_k`.

If the selected outer cutoff has `Q_k+1 <= D R_k`, then
`omega_k <= 4 D^8 R_k^8 mu_k`. Therefore, **only under the separate
lower bound** `eta R_k^3 <= omega_k` does a near-inner shell pay
`eta <= 4 D^8 R_k^5 mu_k`.

Consequently, if `R_k^5 mu_k -> 0` and for some `eta > 0` one has
`eta R_k^3 <= omega_k` eventually, the relative outer cutoff must tend
to infinity. This conclusion is conditional on TWO unproved dynamical
properties; first-crossing minimality alone does NOT supply a fixed cubic
overshoot fraction. The actual source maxima, physical anchor energies,
exact quadratic-sharp PDE widths, annular integral costs, and the
charge-divergence/terminal-clock/sixth/ninth physical rate alternative remain
attached to the same selected witnesses.

No endpoint regularity, finite terminal full-H³ dissipation, uniform
source bound, kinetic-mass vanishing, or positive normalized overshoot is
claimed.

## Checks

Run the registrar `--apply`/`--check`, regenerate and check proof index,
compile the new module, build the full project, compile the root and audit,
run the baseline audit, and then commit/push only if each step succeeds.
