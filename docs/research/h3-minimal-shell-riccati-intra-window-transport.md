# Minimal H³ first-crossing Riccati energy versus actual intra-window signed transport

**Base:** `14293fd9` — force quadratic physical H³ energy on recurrent minimal-shell Riccati windows.

## Quantitative new implication

Let `R_k = v(k) + 1` and `B = 4 K_Ric² + 1`. The existing exact physical
Riccati result states that an exceptional PDE window contains a time
`s ∈ [t_k,t_k+δ_k]` for which `R_k² < B E₃(s)`.

Use the accepted automatic compact-gap signed-transport FTC, applied **inside
that same PDE window**, to obtain

`E₃(s) - E₃(t_k) ≤ ∫_[t_k,s] max(0, -Transport₃ - 2 D₃)`.

The new scalar lemma yields an unconditional *local* dichotomy **given a
Riccati-heavy window**:

- `R_k² < 2 B E₃(t_k)`, i.e. the original physical first-crossing anchor pays;
- or `R_k² < 2 B ∫_[t_k,s] max(0,-Transport₃-2D₃)`, i.e. genuine positive
  signed physical PDE transport replenishes the energy *inside the window*.

The equality case `s=t_k` automatically satisfies the anchor branch. No
artificial lower bound on the duration from `t_k` to `s` is introduced.

The last theorem uses the original every-tail conditional recurrence result,
without reselecting frequency cutoffs, minimal annuli, kinetic shell
witnesses, or sixth/ninth rate gates. Under the two explicit hypotheses
`h3CriticalMinimalShellEveryTailCubicChargeUnbounded` and
`h3CriticalMinimalShellEveryTailGapBudget`, it yields the above local
anchor/transport dichotomy at arbitrarily late selected indices.

**Open:** The hypotheses of divergent cubic charges and bounded positive
inter-window replenishment are *not* derived from Navier–Stokes, and this
new result does not bound the positive within-window transport uniformly.
It is therefore not a proof of regularity or an elimination of the Riccati
alternative. The new information is an exact split of the quadratic energy
amplitude cost into a starting anchor and a measured physical transport
integral over the very same signed-dissipation window.
