# Higher-budget signed logarithmic transport-rate barrier

Base commit: `74f4ba7b` — derive all-orders critical logarithmic radius cost from signed H3 transport.

All four lemmas are conditional on the committed all-orders exact-anchor radial transport logarithmic budget, and the final theorem preserves each original higher moment, projected source, critical cutoff and noncompressed clock hypothesis without replacing or silently discharging it.

Fix m, fixed b∈(a,T), fixed S,D,epsilon satisfying the existing conditions, R_k=v(k)+1, p=16m+3, and C_b=((512epsilon²)^4 D^5)(2304 E3(b) S²+1)^4. The previous theorem has at all late k an actual physical s∈(b,t_k) where

    p log R_k ≤ log C_b + 4(T-b) g(s).

Since v is strictly increasing, log R_k→+∞. For late k, log C_b≤(p/2)log R_k, so the selected physical s also satisfies

    p log R_k ≤ 8(T-b)g(s).

An independent sharp scalar contradiction excludes an eventual *upper envelope* of the form

    ∀ s∈(b,t_k), g(s)≤c log R_k,

provided 4(T-b)c<p. The scalar contradiction uses the exact budget before halving, so it retains the sharp coefficient 4 instead of 8.

The quantity g is the exact positive normalized full-dissipation physical transport excess. The theorem does not prove any physical upper bound, does not establish the antecedent canonical higher-budget hypotheses, and is not a Navier–Stokes regularity proof. The upper-envelope exclusion is a necessary consequence of the conditional canonical escape, not a PDE estimate.

Declarations: `h3Path_strictMono_canonicalLogRadius_escape244`, `h3Path_scalar_logBudget_forces_halfSharpRate244`, `h3Path_scalar_logBudget_excludes_subcriticalRateEnvelope244`, and `h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRateBarrier244`.

Offline static checks only. Complete Lean verification requires repository's pinned Lake toolchain.
