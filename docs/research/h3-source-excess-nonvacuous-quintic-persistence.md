# Nonvacuous quintic PDE persistence: remove the finite-dissipation hypothesis

Base commit: `35253cc8`.

## Existing formal fact: the finite-H³ branch is impossible under no-L²-trace

`FiniteDissipationTerminalTrace.lean` already proves `h3Critical_noL2Trace_incompatible_with_finite_dissipation`. `TerminalDissipationObstruction.lean` proves `h3Critical_noL2Trace_forces_full_dissipation_nonintegrable_on_every_tail`. Accordingly the last several theorems assuming *both* no physical terminal L² trace and an integrable terminal full H³ dissipation have incompatible premises. Their conclusions hold vacuously and cannot be used as necessary asymptotic balances for a hypothetical singular branch. This is not a flaw in Lean; it is a proof-design issue.

## Constructive, unconditioned-on-finite-dissipation result

On exactly the synchronized fivefold source windows, the already certified physical annular persistence theorem provides a width

    θ_k = min(d_k/2, H_k/[8 (Λ_k+1)]) > 0

for each active spike over twice the low-band kinetic ceiling. Here H_k=R_k² ε_k² / 8, d_k=t(v_k)+w(v_k)-p_k, and Λ_k is the genuine projected-PDE annular variation coefficient on the selected source and spectral maxima.

The proved fifth-order polynomial ceiling gives

    Λ_k ≤ P_k = 24 K_k C_k [(N_k+2)^5+(L_k+2)^5],

so the **same** certified width satisfies

    θ_k ≥ min(d_k/2, H_k/[8 (P_k+1)]).

On the entire interval [p_k,p_k+θ_k], actual physical Fourier-annular dissipation exceeds H_k/4 and is no greater than full physical H³ dissipation. Its annular integral is at least θ_k H_k/4. The four-way PDE/spectral alternatives survive. This module assumes no finite integral of D₃ on (a,T).

## Next hard-math direction

Study the nonintegrable physical H³ dissipation branch. Do not invoke finite terminal dissipation to obtain cofinal summability on that branch. Investigate whether the physical source/kinetic structure produces a compensating estimate on actual Fourier-annular charge without adding a hypothesis already known to force an L² trace.

Lean compilation must run in the user's configured mathlib toolchain before this patch is accepted.
