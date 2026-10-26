# Intermittent sixth-order rate barrier on exact cubic PDE clocks

Base commit: `d7094a91` — bounded sixth-rate projected-PDE coefficients force cubic terminal-time compression.

## New result

Write `R_k = v(k)+1`, `Z_k = Λ(v(k))+Ξ(v(k))+1`, and
`G_k = R_k^3*(T-τ(v(k)))/4`. The exact width selector and quarter-cubic
annulus gap, combined with summable dissipation costs, imply the *uniform
threshold-by-threshold* barrier:

For every `η>0` and `B>0`, all sufficiently late indices satisfy

`G_k ≥ η  →  Z_k ≥ B*R_k^6`.

This **does not assume** that geometric noncompression holds eventually.
It applies equally to intermittent noncompressed indices interspersed with
rapidly compressed indices. Consequently, for each `η>0` and `B≥0`,
all sufficiently late indices where `Z_k ≤ B*R_k^6` satisfy `G_k<η`.

These are eventual implications, not an unconditional OR between
`G_k→0` and `Z_k/R_k^6→∞`. Oscillating sequences can obey the exact
barrier without either global limit. No global H³ regularity theorem is
asserted, and finite terminal H³ dissipation remains an explicit hypothesis.

## Proof organization

- The abstract intermittent barrier uses the existing finite-scale
  trichotomy with `ε=min(η/2,1/(8B))` and positivity of `Z_k`.
- The bounded-rate-index corollary applies the barrier with threshold
  `B+1`, ruling out `G_k≥η` by positivity of `R_k^6`.
- The physical specialization preserves the exact width, quarter-cubic
  gap, cofinal disjoint intervals, and summable nonnegative dissipation
  costs established at the preceding checkpoints.

This patch adds three theorems with no `sorry`, `admit`, or new axioms.
The new module and project import index must be compiled and checked
with the repository's Lean toolchain.
