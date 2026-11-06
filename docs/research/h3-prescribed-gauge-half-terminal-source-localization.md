# Physical half-terminal source localization on prescribed-gauge H³ windows

Base commit: `55db08c50ef78154ae8c522e6c6d166c9e740a09`.

## Quantitative source trichotomy

The existing no-strong-H³-trace theorem, assuming finite full H³ dissipation,
chooses arbitrary positive profile `M(n)=H(n)^8` with `H(n)>=1` and genuine
minimal crossing windows. Their Fourier outer scale `Q_k=N(v(k))+2` satisfies
`Q_k/H(v(k)) -> infinity`, and their disjoint positive viscous charges satisfy

    sum_{k<m} δ(v(k)) * H(v(k))^8/4 <= integral_a^T D_H3(t) dt.

Let `t_k=τ(v(k))`, `m_k=(t_k+T)/2`, `U` the actual physical terminal
Bochner primitive, `F` the actual physical real-linear raw Fourier map, and
`G(t)` the actual projected Navier–Stokes momentum source. Write

    A_k = || P^+_{v(k)} F U ||,
    E_k = max_{t∈[t_k,m_k]} ||G(t)||,
    L_k = integral_{m_k}^T ||G(t)|| dt.

The source maximum exists by genuine positive-time continuity. The exact
integral split yields

    integral_{t_k}^T ||G|| <= (m_k-t_k)*E_k + L_k.

The previously established strict carrier/source tail alternative then
implies, on all sufficiently late selected windows,

    H(v(k))^4 < 14 Q_k^4 A_k,
       OR
    H(v(k))^4 < 28 Q_k^4 ||F|| (m_k-t_k) E_k,
       OR
    H(v(k))^4 < 28 Q_k^4 ||F|| L_k.

This localizes the source payment into a compact interval with attained
physical source maximum, or a strictly later tail. `E_k` is the *intrinsic*
actual physical source maximum; it need not be identified with the stored
clock ceiling `C_k`, whose named window predicate records only source
attainment on the half-terminal interval and an upper ceiling on the shorter
persistence window. No unjustified global domination by `C_k` is used.

Neither the high-frequency outer radius nor the delayed physical source
tail has an independent upper bound here. Thus this is an unconditional
necessary trichotomy in the no-H³-trace branch, **not a contradiction**.

## Scope and verification

The package adds three Lean theorems and the standard proof index/audit
registrar. No `sorry`, `admit`, or axioms are introduced. The preparation
environment lacks Lean/Lake, so the source must be compiled and audited on
the pinned local repository toolchain before it can be accepted.
