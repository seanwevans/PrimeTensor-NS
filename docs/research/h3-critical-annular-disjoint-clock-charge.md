# Actual annular kinetic deficit: disjoint H³ viscous clock or cap spike

Accepted base: `a369d18e1341300243390c54c140d520ea8f1983`, `derive annular kinetic deficit high-viscous or linear charge alternative`.

## Physical and quantitative bridge

Let `E = velocityH3Energy0At u b` be the actual earlier physical kinetic energy. For any strict physical time `b<t<T`, Plancherel, sharp low/high Pythagoras, the real physical zeroth-order identity, and the actual kinetic antitonicity give

    M(t,rho) := ||(I-P_rho) U(t)||^2 <= E.

This is the **highpass** kinetic mass, unlike the previously established lowpass kinetic anchor. No positive lower bound on `M` is assumed.

Fix `0<=rho<=sigma`, arbitrary `H>=0`, and the exact previously accepted physical kinetic excess and annular Young-gap/width/outer-base deficit `Delta(t,rho,sigma)`. On the sublevel branch `D_3(t)<=H`, the previously accepted linear cap theorem proves

    Delta(t,rho,sigma) <= M(t,rho) * (rho^2)^3 * L(b,H) * D_3(t),

where

    L(b,H) = 12*(3+C_L)^2*(1+6*E) + 18*(3+C_L)^2*H.

Since `L>=0`, define the everywhere positive normalization

    C(b,rho,H) = max(1, E*(rho^2)^3*L(b,H)).

Then an actual positive kinetic deficit floor `epsilon <= Delta(t,rho,sigma)` on the kinetic-excess branch forces the **unsquared** viscous height

    epsilon / C(b,rho,H) <= D_3(t).

The normalizer is at least one even when E=0, rho=0, or the highpass kinetic mass vanishes. No division by `M` occurs.

## Disjoint physical windows

Let `[p_k,p_k+delta_k]` lie inside the strict physical tail `(b,T)` and inside the energy-class interval `(a,T)`, with nonnegative widths and consecutive disjointness. For each k prescribe `0<=rho_k<=sigma_k`, a cap `H_k>=0`, and a **positive** deficit floor `epsilon_k`. The main theorem exposes the following *persistence premises* at **every physical time** on each selected window:

- the existing kinetic-excess condition needed by the annular compensation theorem;
- `epsilon_k <= Delta(t,rho_k,sigma_k)`.

It does NOT assume any viscous cap persistence. Instead it proves exactly one of these alternatives:

1. There exists some window index k and a genuine physical time t in that window with `D_3(t)>H_k`;
2. The **same** disjoint window family is in the cap branch, and its normalized charges

       delta_k * epsilon_k / C(b,rho_k,H_k)

   are summable, tend to zero, and every finite partial sum is bounded by the original actual real physical terminal dissipation integral `∫_a^T D_3(t) dt`.

The proof invokes the existing `h3Path_disjointNonnegativeWindows_finiteHeightCost_le244` and ordinary nonnegative real series summability, without replacing the physical viscous density by an abstract one.

## Remaining hard obstruction

This is a conditional bridge on the **already selected disjoint physical windows**, not a proof that the annular kinetic deficit and kinetic-excess branch actually persist on those windows. The source and physical H³ windows constructed earlier do not automatically preserve this newly defined deficit at every time: that requires a quantitative time modulus for the Fourier nonlinear Young-gap (and its moving annular cutoffs), or a verified alternate selection using the actual PDE. The cap-spike branch likewise supplies no common positive width. Finite terminal H³ dissipation itself is explicitly conditional and, in other parts of the project, implies a physical terminal L² trace.

No additional axiom and no `sorry` or `admit`. Run the registrar, Lean build, source index, and the axiom audit on the user's pinned Lean/mathlib setup. Source screening and registration tests are **not** Lean kernel compilation.
