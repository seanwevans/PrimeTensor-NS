# Exact overlap envelope for retained late physical PDE clocks

**Base:** `8239da2b6973ecc2f2e68e1b20222c47166875aa` — contained secondary physical PDE peak above the primary H3 floor.

## Missing cost in the partial-overlap case

The primary physical clock has interval `[r,r+eta1]` and dissipation floor `A`. The secondary starts at an actual attained source/state time `s>=r`, persists for `eta2`, and has floor `H=h/2`. Both charge the same terminal integral `B=integral_m^T D_H3`.

Set the **outside** length of the secondary interval to

    L := min eta2 (max 0 (s+eta2-(r+eta1)))

and its **intersection** length to `O:=eta2-L`. With positive durations and `r<=s`, the clocks give the exact envelope payment

    eta1*A + L*H + O*max(0,H-A) <= B.

The previously proved three-way maximum ledger plus the contained-three-piece charge imply this single formula:

- **Disjoint:** `L=eta2`, `O=0`, so primary and secondary costs add.
- **Contained:** `L=0`, `O=eta2`, so the entire primary is charged and the contained secondary pays only its positive height excess.
- **Partial crossing:** `L=s+eta2-(r+eta1)`; when `H<=A`, the primary plus exterior secondary charge suffices; when `H>A`, the primary prefix plus whole secondary charge is exactly the envelope.

No overlap is double-counted. This is the optimal estimate from *only these two pointwise constant floors*, before additional PDE structure.

When `H>A`, the overlap length is explicitly bounded by

    O <= (B - eta1*A - L*H)/(H-A).

The physical theorem uses the existing actual Navier--Stokes primary and secondary clock certificates. The cofinal theorem keeps the same first-crossing witnesses, disjoint original viscous sums, spectral escape, and terminal tail convergence. It transports the new exact envelope from the already-accepted contained-peak ledger, choosing no new secondary clock.

## Scope

There is no universal bound forcing `H>A`, no fixed lower bound on `O`, no control of the selected cutoff or the attained source/state growth, and no unconditional regularity/continuation conclusion. The Lean proof uses no placeholders. Compile against the repository's pinned toolchain.
