# Canonical attained source on arbitrary-height terminal H3 PDE clocks

**Baseline:** `2c65a769fd34e2c93d0c4cd865f3ddf7f790d04b`

## Mathematical change

Prior anchored-profile witnesses selected a real source ceiling `C` satisfying
`‖R(s)‖_{L²} ≤ C` on the short physical PDE interval, but `C > S` alone did
not exhibit a physical source observation. The canonical source envelope

    C(t) = sup_{t ≤ s ≤ (t+T)/2} ‖Δu(s) − Leray(u·∇u)(s)‖_{L²}

is attained on this strictly interior closed interval, since the actual
projected-source Hilbert path is continuous. We choose this exact value when
constructing the anchored polynomial clock, and carry a maximizing source
time through the resulting disjoint subsequence.

For arbitrary positive heights M(n)→∞, failure of a strong terminal H³ trace
and the additional integrability of the full actual H³ dissipation yield
a disjoint terminal subsequence with summable charges δ(v(k))M(v(k))/4.
On every sufficiently late selected index one has:

1. `(T−τ) M < 4` (terminal clock compression), or
2. `M² < 384 K C ((Q+1)^5 + (R+1)^5) + 8` (physical quintic gain), or
3. `M² < 576 C² ((Q+1)^8 + (R+1)^8) + 8` (physical eighth-order gain).

For each fixed source norm threshold `S ≥ 0` the same witnesses additionally
satisfy: compressed terminal clock, an **attained physical observation**
`S < ‖Δu(s) − Leray(u·∇u)(s)‖₂` on `[τ,(τ+T)/2]`, or a large rate
using the exact linear/quadratic cutoff gains evaluated at S.

## Open math

This removes the arbitrary-ceiling efficiency gap. It does **not** bound
the outer Fourier radius Q, the initial H³ amplitude K, or the terminal
clock `(T−τ)M`. The theorem is not an H³ continuation theorem and does
not assert that actual projected-source norms diverge unless the other
rate/clock alternatives are excluded.

## Validation

Registration and static syntax/placeholder checks were performed; the
local environment does not contain `lean` or `lake`. The supplied run
script performs module compilation, whole-project build, index regeneration,
and full baseline audit before any commit.
