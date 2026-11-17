# Finite Z³ Galerkin endpoint-trace bridge — 2026-11-17

Baseline: `6ad05df8a178e4b366efc480226fca8c732d735f`.

## Mathematical result

The actual finite projected complex Leray Navier–Stokes field `F_S` is
C¹ and its local Picard solutions have a cutoff-independent `W_(9/5)`
100-ball and a `W_(3/2)` / finite-state derivative speed ceiling 51000.

For a preterminal strong solution `α` on `[a,b)` satisfying the genuine
ODE and the 51000 vector-field norm ceiling on that interval,
the real mean-value inequality gives

    ‖α(t) − α(s)‖ ≤ 51000 |t−s|,     a ≤ s,t < b.

Therefore, for any Cauchy sequence of preterminal times, the sequence
of finite-state coefficient vectors is Cauchy and has a limit in the
complete finite-dimensional coefficient space. A state-norm ceiling 100
also passes to that limit. The result depends neither on Fourier
cardinality nor on a cutoff-dependent Gronwall constant.

The theorem is deliberately stated on a half-open interval: it does
not assume the existence of a trajectory or derivative at the terminal
time. It gives the missing endpoint trace for maximal continuation.

## Remaining maximal-continuation obligation

Construct a maximal connected solution, use these estimates on every
compact subinterval of its preterminal domain, identify its unique
endpoint trace, restart the C¹ field there, and glue by ODE uniqueness.
Combined with the original strict analytic initial ball and the
cutoff-free persistence theorem, the endpoint cannot occur before
`τ = (log(2)−log(9/5))/100`.

This ZIP **does not** claim the maximal-time or infinite-cutoff theorem.
No new ODE or a priori assumption has been added to the source module.
