# Every-tail signed H³ replenishment versus recurring Riccati energy events

Base: `4db150c6` (`charge minimal H3 cubic drains to actual signed gap transport replenishment`).

## Mathematical increment

The previously accepted fixed-prefix cumulative result is logically vacuous after
one early Riccati exception. We remove this defect by proving an EVERY-TAIL
finite-block scalar telescoping identity on the ORIGINAL selected physical
minimal first-crossing windows.

Let `t_k=t(v(k))`, `R_k=v(k)+1`, `w_k=δ(v(k))`,
`c_k=w_k R_k³/2`, `E_k=E₃(t_k)`, and
`G_k=∫_{t_k+w_k}^{t_{k+1}} max(0,-Transport_H³(s)-2D_H³(s)) ds`.
For every shifted block of windows `b,...,b+q` after a fixed initial
physical prefix, we prove that EITHER some `i∈[b,b+q]` has a true physical
Riccati-heavy time inside its window,

    R_i³/2 < K_Ric sqrt(E₃(s)) E₃(s),

OR the entire block satisfies

    1 + ∑_{i=b}^{b+q} c_i ≤ E₃(t_b) + ∑_{i=b}^{b+q-1} G_i.

The lower bound `E₃ >= 1` is already established by the original energy class.
The energy derivative is automatically interval-integrable on each compact
physical window, and the signed gap majorant is automatically integrable
on each compact inter-window gap. No global H³ dissipation assumption.

## Cofinal conditional obstruction

If **(1)** cubic cost partial sums are unbounded on *every* selected tail,
and **(2)** positive signed-gap replenishment partial sums are bounded on
*every* selected tail, then Riccati-heavy events occur beyond every index.
The two premises are independently explicit and are not claimed as PDE
consequences. Unlike fixed-prefix accounting, a single early exception
cannot discharge all later blocks.

## Proof trust / validation

The new module is registered in the root and audit by a repeatable registrar.
Axiom reporting is wired for all three theorems and six definitions, without
`sorry` or new axioms. Pinned Lean compilation and full repository builds must
be run in the user's repository.
