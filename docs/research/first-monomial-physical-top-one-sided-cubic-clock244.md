# Physical one-sided logarithmic clock from actual cubic forcing

Base checkpoint: `61d9b5f9` — derive automatic joint physical fifth phase action integrability.

## The hard analytic distinction

At every strict physical time with `D3 > 0`, the exact Fourier PDE identity is

    D3' + M5 + P = M3,   M5 >= 0, P >= 0.

Consequently

    (log D3)' = M3/D3 - (M5+P)/D3 <= M3/D3.

The right side is the real third-radial Leray forcing square mass divided by physical fourth-radial velocity mass. The previous module already proves the cubic rate continuous on compact strict intervals (as part of its automatic integrability argument). This patch exposes its continuous-on-Icc property explicitly, then applies the classical **derivative ceiling / mean-value theorem**, rather than FTC of the potentially unbounded signed logarithmic derivative.

For any `s <= t` in a strict H3 energy class, with `D3>0` throughout, the continuous cubic-to-D3 rate attains a maximum at some actual `r0 in [s,t]`, and

    log(D3(t)) - log(D3(s))
        <= (t-s) * (M3(r0)/D3(r0)).

No signed-log integrability, fifth moment temporal integrability, or phase temporal integrability is needed for this endpoint bound. In particular, rapidly decreasing top mass does not invalidate the one-sided argument.

## Where this helps, and where it does not

This identifies cubic forcing, rather than a fictitious scalar budget, as the only mechanism for large *forward logarithmic growth* of top dissipation. It also gives a concrete, localized obstruction: any physical log-growth secant exceeding `K` requires the actual normalized cubic source to exceed `K` somewhere in the interval.

This **does not** control `-log D3`, the joint fifth/phase expenditure, the repeated downward variation of the top mass, or terminal-uniform behavior. The compact maximum can diverge as the upper time endpoint approaches `T`. Thus the result is not a Navier–Stokes continuation argument. Closing continuation would require a uniform or suitably integrated forcing mechanism (or a dynamical restriction tying the signed concentration channels to this cubic clock).
