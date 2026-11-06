# Two-sided overlap-safe packing of the prescribed-gauge physical H³ PDE clocks

**Base:** `e579ed7701021870f420feceae4f6758adbae106` — overlap-safe primary-prefix / full-secondary terminal-tail payment.

## Why two-sided trimming matters

The previous theorem selected `s` as an actual maximizing time of the retained primary clock, with `r <= s`, and charged

    min(eta1,s-r) A + eta2 H <= B,

where `H = A/(24 sqrt(R B))`, `A=V/(2P)`, `R=96 C0 (J+2)^5`, and `B=integral_m^T D_H3`. If `s=r`, the primary prefix disappears even though the original primary clock is still certified on `[r,r+eta1]`.

Use complementary, nonoverlapping interval surgery. The right-end overhang of the secondary clock is

    suffix2 := min eta2 (max 0 (s+eta2-(r+eta1))).

This is `eta2` if the clocks are disjoint, `s+eta2-(r+eta1)` for a proper crossing, and zero if the entire secondary clock is contained in the first. The intervals `[r,r+eta1]` and `[s+eta2-suffix2,s+eta2]` are disjoint in their interiors, so

    eta1 A + suffix2 H <= B.

Combine that with the original `eta1 A <= B` and the existing prefix-plus-whole-secondary payment to obtain the *MAX* (not sum) ledger:

    max (eta1 A)
        (max (min eta1 (s-r) A + eta2 H)
             (eta1 A + suffix2 H)) <= B.

This gives meaningful terminal control even when `s=r` and never counts a region of physical space-time twice within a single charge.

## Temporal localization consequence

For any trial time separation `delta <= eta1`, the prefix ledger also yields

    s < r+delta  OR  delta A + eta2 H <= B.

In particular, if `B < delta A + eta2 H`, the attained source/state maximizing time *must* lie strictly before `r+delta`. This does **not** establish that condition automatically. It records exactly which missing size comparison would force physical-time concentration.

## Scope

The main cofinal theorem carries the original minimal prescribed-gauge first-crossing witnesses, terminal Fourier alternative, early source/kinetic alternatives, strict physical primary and secondary clocks, original disjoint viscous charges, and `B_k -> 0`. The maximum lower-bound ledger is conditional on the previously proved two-slice rate branch and kinetic-only gap, exactly as in the predecessor.

No terminal-uniform cutoff, coefficient, positive persistence duration, or Navier–Stokes continuation is claimed. Code is provided without `sorry`/`admit`. The pinned local Lean/mathlib build is required to verify elaboration.
