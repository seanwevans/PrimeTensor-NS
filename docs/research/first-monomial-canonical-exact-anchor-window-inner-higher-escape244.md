# Canonical full-window top-order higher-radial escape

Base commit: `03f3df5d` — derive unconditional canonical inner-cutoff top higher radial escape.

**New mathematical improvement.** On the exact same disjoint source-aware PDE windows, the cofinal canonical constructor has already established for all times `s` between `t_k` and `t_k+δ_k` the genuine low-frequency difference

    R_k³/2 < L_(Q_k)(s) - L_(R_k)(s),  R_k=v(k)+1, Q_k=N(v(k))+1.

The physical low/high radial partition and nonnegative outer high tail give

    R_k³/2 <= H_(R_k)(s).

The committed high-frequency physical comparison and established top-order coercivity lemma then imply for *every* natural order `m` and every `s` in the **entire original window**,

    ENNReal.ofReal((R_k²)^m * R_k³/8) <= M_top,4+m(s).

This is an actual physical `q^(4+m)` extended moment, not the separate weighted-full-dissipation moment. No higher-moment finite real integral is assumed.

Since strict monotonicity of the original cofinal selection yields `R_k³ -> +∞` and `(R_k²)^m>=1`, one obtains a **uniform full-window escape**: for every *fixed* m and every real threshold B, eventually **all s** in the k-th original interval satisfy

    ENNReal.ofReal B <= M_top,4+m(s).

The result is stronger than single-anchor escape and requires no H³-derived continuity of the higher moments, no additional source ceiling, no charge persistence hypothesis. It remains conditional on `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, positive canonical terminal kinetic mass, absence of terminal physical L² trace, and integrable full H³ dissipation. It is not a proof of global regularity or a contradiction: these windows shrink.

## Formal declarations

- `h3Path_physicalHalfAnnulus_forces_windowTopHigherMoment244`
- `h3Path_scalar_cubicWindowMoment_eventually_above244`
- `h3Path_noL2Trace_exactAnchor_uniformWindowTopHigherEscape244`

ZIP structure and audit registrar are checked offline. Full Lean/Mathlib compilation is unavailable in the packaging environment and must be checked in the repository's pinned Lake build.

## Local Lean correction (fix1)

The selected cofinal package states `hAll k` at the time `tau (v k)`; using `hAll (v k)` double-applies the selection and incorrectly requires a window around `tau (v (v k))`. The interval-persistence proof now obtains the annular inequality from `hAll k`, retaining the same `k` and `s`. The theorem statements and premises are unchanged.
