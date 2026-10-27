# Canonical first-crossing outer cutoff: ninth/eighth growth and subcutoff exclusion

Base commit: `10194d7f` (least three-quarter-cubic spectral crossing with actual quadratic-sharp PDE clocks).

## Why this step matters

The earlier ninth/eighth outer cutoff result was proved for an existential cutoff, which could in principle be inflated gratuitously. The base commit constructs the least integer `N(n)` with actual annular weighted H3 dissipation above `3*(n+1)^3/4`, then carries that same cutoff through the physical quadratic-sharp clocks and the disjoint cost sum. This module applies the joint sixth/ninth PDE rate barrier and physical eighth-order cutoff gain to those *specific minimal witnesses*.

## Quantitative result

Write `R_k=v(k)+1`, `Q_k=N(v(k))+1`, and let `G_k=R_k^3*(T-tau(v(k)))/4`. Under the no-terminal-strong-L2-trace branch, positive terminal kinetic energy, and the **additional** finite terminal H3 dissipation assumption, the certified first-crossing windows have these implications.

For any `eta>0`, `B>=0`, `M>=0`, and real source test `S`, every sufficiently late selected witness satisfying

- `eta <= G_k` (noncompressed cubic terminal clock),
- `Lambda_k + 1 <= B*R_k^6` (sixth-order linear PDE rate),
- `C_k^2 <= S^2` (projected physical source ceiling),

must satisfy `M*R_k^9 < (Q_k+1)^8`.

If the three branch tests hold eventually, `(Q_k+1)^8 / R_k^9 -> +infinity`. This is now genuine growth of the **least** first-crossing cutoff, not arbitrary spectral-window enlargement.

More strongly, fix any candidate integer cutoff `m>=v(k)` with `(m+2)^8 <= M*R_k^9`. The separation inequality implies `m < N(v(k))`, and first-crossing minimality then forces

`lowDiss(m+1, tau(v(k))) - lowDiss(R_k, tau(v(k))) <= 3*R_k^3/4`.

Thus the weighted spectral dissipation cannot reach the three-quarter-cubic annular threshold below this entire ninth/eighth scale on the conditional branch. The offset `m+2` matches the `(Q+1)^8` bound in the existing physical eighth-order estimate, with `Q=N+1`.

## Scope

These are necessary spectral-distribution alternatives, **not** automatic noncompression, source boundedness, sixth-order linear-rate control, or global Navier-Stokes regularity. The new result does not bound the first-crossing radius from above or remove the explicit full H3 terminal dissipation integrability condition. A subsequent PDE argument must test the canonical cutoff requirement against the kinetic/spectral localization estimates, without presuming a uniform outer-radius ceiling.

## Validation

This patch is packaged with no Lean placeholders and an idempotent registrar. Run its Lean module, module build, index generation/check, the audit, and the full repository build locally. The packaging environment does not provide a Lean toolchain.
