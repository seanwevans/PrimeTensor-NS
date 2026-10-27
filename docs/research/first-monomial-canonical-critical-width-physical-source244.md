# Canonical projected physical source escape under a bounded critical width

Base commit: `cba412ce` — canonical attained source maxima carried through disjoint quadratic-sharp PDE clocks.

The original chosen-ceiling width/source theorem cannot be transferred wholesale to its newly canonicalized witnesses: existential witnesses may be distinct. This module constructs the ninth/eighth quadratic source-gain estimate directly on the **same** canonical cofinal/disjoint clock sequence from `h3Path_noL2Trace_finiteDissipation_canonicalSourceDisjointThreeScale244`.

For `R_k=v(k)+1`, `Q_k=N(v(k))+1`, `W_k=N(v(k))-v(k)` and the canonical source maximum `C_k`, the exact three-cap barrier plus the physical eighth-order polynomial gain establishes a conditional inequality for every fixed `M ≥ 0` and each proposed source ceiling `S`: with noncompression and controlled sixth-order linear rate, `C_k² ≤ S²` implies

`M R_k^9 < 36 S² ((Q_k+1)^8 + (R_k+1)^8) + 1`

eventually. Positive annular dissipation and the monotone low-radial Fourier integral recover `v(k) ≤ N(v(k))`; this ensures the exact geometry `R_k + W_k + 1 = Q_k + 1` without adding a new cutoff-order hypothesis.

If `(W_k+1)^8 ≤ D R_k^9` eventually, the previously proved outer-bound lemma yields `(Q_k+1)^8 ≤ 256(D+1) R_k^9`. The inner term satisfies `(R_k+1)^8 ≤ 256 R_k^9`. Thus the eighth-gain estimate is incompatible with a bounded `C_k²` when its multiplier `M` is chosen arbitrarily large. Formally, `C_k² → +∞`.

Here `C_k` is **by construction** the attained physical `L²` norm maximum of `Δu - Leray(u·∇u)` on `[τ(v(k)), (τ(v(k))+T)/2]`; therefore actual projected-source norms exceed every fixed threshold at some time in each sufficiently late such shrinking window. No assertion at the left endpoint is made.

This remains a **conditional** PDE consequence under finite full H³ dissipation, absence of strong terminal physical L² trace, eventual geometric noncompression, sixth-order linear-rate control, and a uniform critical ninth/eighth annular-width cap. It is not an unconditional continuation or regularity result.
