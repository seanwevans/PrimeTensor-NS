# Nonintegrable minimal H3 first crossings: energetic shell alongside last-shell overshoot

Base: `b939798b` (verified commit). The previous theorem synchronized the minimal last shell, its small positive overshoot, physical H3 energy, exact quadratic sharp projected source PDE clocks, disjoint annular charges and sixth/ninth rate alternative.

The *last* shell only pays its possibly tiny overshoot. The older finite telescoping pigeonhole theorem `h3Path_physicalFirstCrossing_exists_widthAveragedKineticShell244` instead finds some shell `j` inside that same minimal annulus (not necessarily the last shell) paying the full first-crossing cost divided by the actual shell count `L=N-v`:

    3 R^3/4 < L * [D_low(j+2,t)-D_low(j+1,t)]
             <= L * 4 (j+3)^8 mu_j.

This patch transports that physical result onto the same no-L2-terminal-trace, disjoint quadratic-PDE windows selected by `h3Critical_noL2Trace_disjointMinimalShell_energySourceOuterRateBarrier`. The old window and original sixth/ninth rate alternatives remain literally unchanged; no independent cutoff is selected. The selected physical snapshots are eventually in `(a,T)` by cofinal convergence and the positivity of the already certified exact PDE widths.

For any D>=0, eventually:

    D R < j+3 OR 3 < 16 D^8 L R^5 mu_j.

If additionally `L R^5 mu_j -> 0`, then `(j+3)/R -> +infinity`. This latter assertion does **not** need an unproved lower bound on the normalized last-shell overshoot, but the critical width-weighted mass vanishing remains an explicit hypothesis. No full terminal H3 dissipation integrability, uniform H3 energy bound, upper width bound, or regularity conclusion is asserted.

The original last-shell witness `m` remains in `h3CriticalMinimalShellEnergyWindow`; the energetic pigeonhole shell `j` may differ from `m`.

Audits: two new Lean theorems plus #check and #print axioms. Execute `lake env lean` and full `lake build` locally before committing.
