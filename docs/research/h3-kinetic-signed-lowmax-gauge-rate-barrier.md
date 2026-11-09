# Signed sixth-flux: symmetric kinetic gauge-rate obstruction

**Exact base:** `bb0907a8b7f3502714c07452e1746aa024ed56d5` —
accepted symmetric physical annular rate/clock compression.

## Hard frequency comparison

The previous theorem certifies, for any true gamma-free high-radial physical
signed LowMax carrier, a finite outer natural cutoff `Q >= R` and the actual
in-gap alternative

    gap_length * H <= 16 * D_gap
    or H^2 <= 32 * (L_R(E0) + L_Q(E0) + 1) * D_gap,

where `H` is the *linear* signed flux viscous height and `L_j(E0)` is the
actual kinetic-only PDE dissipation Lipschitz coefficient at natural radius
`j`, with the original kinetic anchor `E0 = velocityH3Energy0At(u,b)`.

One cannot simply assume `L_j` increases with `j`. Instead, because every
`L_j(E0) >= 0`, for *any* prescribed gauge `G` and any `R <= Q <= G`, the
finite sum `S_G = sum_(j=0)^G L_j(E0)` satisfies

    L_R(E0) + L_Q(E0) <= 2 * S_G.

This avoids a hidden monotonicity hypothesis and retains the exact cutoff
rate. Therefore a non-compressed gap clock together with an insufficient
finite-gauge rate budget forces **G < Q**:

    16*D_gap < gap_length*H
    32*(2*S_G+1)*D_gap < H^2
    --------------------------------
                   G < Q.

The result is conditional: it does not assert either of the strict
inequalities on every gap.

## Uniform cofinal form

The accepted original cofinal gap-dissipation theorem says `D_gap -> 0` on
the *same separated physical kinetic gaps*. For any fixed `eta>0` and
`epsilon>0`, there is a single late index after which **for all** natural
`G,R` and **all** actual high-tail adverse observations `t` in each gap,
there exists `Q >= R` such that

    gap_length*H < 16*epsilon
    OR G < Q
    OR H^2 < 32*(2*S_G+1)*epsilon.

The threshold does not depend on `G,R,t`: the smallness input is only the
entire physical gap dissipation. The final theorem eliminates the first and
third alternatives under explicit opposite inequalities and derives `G<Q`.

The physical hypotheses are not changed: the Navier--Stokes path satisfies
the accepted positive-time `H3` admissibility, energy class, finite interval
H3 dissipation, and original cofinal natural-annular kinetic witnesses.

## Mathematical boundary

This is a frequency escape *necessity*, not a regularity proof. Gap lengths
can shrink, the signed physical height can shrink if the adverse-time H3
energy grows, and the actual outer cutoff `Q` is not fixed. No lower bound on
the gap clock or height has been proved. The distinct cubic signed baseline
and source/radius/energy arms remain open. The result shows precisely which
additional physical rate estimates would make an outer cutoff escape
unavoidable on the high-tail branch.

## Verification

Regenerate `proof/generate_index.py`, run the registrar and target Lean/Lake
builds, the full build, and the proof fragment audit on the pinned revision.
The ZIP's static checks do not establish Lean kernel verification.
