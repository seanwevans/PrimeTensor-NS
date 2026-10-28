# Canonical H³ critical-width failure: quantitative cofinal alternatives

Base commit: `81d7dd33` — conditional continuation from compressed canonical H³ peaks and the intrinsic Riccati lower terminal clock.

The continuation theorem from that commit is conditional on **all three** eventual tests for the canonical quadratic-sharp disjoint witnesses:

1. `η ≤ G_k := (v_k+1)^3 * ((T-τ(v_k))/4)` for some fixed `η>0` (geometric noncompression).
2. `F_k := h3PathCubicAnnulusActualLinearRate244 N K C (v_k)+1 ≤ U*(v_k+1)^6` for a fixed finite nonnegative `U`.
3. `W_k := (((N(v_k)-v_k : ℕ):ℝ)+1)^8 ≤ V*(v_k+1)^9` for a fixed finite nonnegative `V`.

Under the previous *explicit* H³ path, energy class, positive terminal kinetic mass, no-strong-terminal-trace and finite viscous-budget hypotheses, add hypothetical **no smooth continuation**. The previous conditional extension implication proves that these three tests **cannot hold eventually together** for any `η>0`, `U,V≥0`.

The new module makes the quantifiers exact on the **same canonical source-maximizing sequence and same minimal annuli**:

For every `η>0`, `U,V≥0` and every integer `n`, some `k≥n` satisfies

    G_k < η   OR   U*(v_k+1)^6 < F_k   OR   V*(v_k+1)^9 < W_k.

This is cofinal failure; it does *not* say a particular arm fails eventually or that one particular arm is always responsible. It is not a contradiction with no-extension.

Under the *additional explicit* assumption that `G_k≥η` and `F_k≤U*(v_k+1)^6` hold eventually, the normalized eighth-power annulus width `W_k/(v_k+1)^9` exceeds **every finite nonnegative** `V` on arbitrarily late indices. Under geometric noncompression plus an eventual width cap, the normalized linear rate `F_k/(v_k+1)^6` likewise exceeds every finite nonnegative `U` cofinally. The theorem states the division-free versions so it does not introduce denominator normalizations or cutoff indexing changes.

This is a precise obstruction classification and identifies exactly which missing PDE estimates would settle the critical-width regime. It does not supply those estimates, does not eliminate the geometric-compression branch, and does not prove unconditional 3D Navier–Stokes regularity.

Lean elaboration is not available in the packaging environment. Validate with the repository's pinned toolchain and full baseline, with `proof/generate_index.py` run before checks/builds.
