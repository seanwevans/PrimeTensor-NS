# Critical logarithmic radius against the genuine physical H³ PDE Riccati ceiling

Base: `d92fc4db` — exclude subcritical logarithmic signed H3 transport rates at canonical anchors.

The prior exact canonical witness gives an eventual positive full-dissipation normalized transport rate satisfying `(16m+3) log R_k <= 8 (T-b) g(s)` at an intermediate physical `s` in `(b,t_k)`, and excludes any cap `g(s) <= c log R_k` with `4(T-b)c < 16m+3` on all those intervals.

This module uses two **already proved physical PDE bounds**:

1. The autonomous energy inequality `E₃' <= K_* sqrt(E₃) E₃`, where `K_* = h3PathSqrtEnergyRiccatiCoefficient`. By the project's exact equality `g = max(0,E₃'/E₃)` and minimal-positive-rate lemma, `g <= K_* sqrt(E₃)`.
2. The complete Landau-analytic H³ transport commutator `|T₃| <= 4422 (1+|h|) E₃`, with `h=h3PathCanonicalSqrtEnergyGradientEnvelope`, and physical `D₃>=0` give `g <= 4422 (1+|h|)`.

Thus, on **the same canonical disjoint exact-anchor witnesses**, at a genuine interior physical time `s=s_k`:

    (16m+3) log R_k <= 8 (T-b) K_* sqrt(E₃(s_k)),
    (16m+3) log R_k <= 8 (T-b) 4422 (1+|h(s_k)|).

A sharp proposed *interval-wise* square-root H³ energy ceiling `sqrt(E₃(s)) <= c log R_k` for every `s in (b,t_k)` is impossible whenever `4(T-b) (K_* c) < 16m+3`. This uses the parent unhalved rate obstruction, not the weaker half-sharp pointwise form.

The gradient envelope h is a proved **upper bound** for pointwise gradients; its forced growth does not itself imply a converse lower bound on the true gradient supremum. These are necessary conditions under the original higher radial moment majorant F, source envelope S, critical cutoff D, noncompressed clock eta and small epsilon, not unconditional Navier–Stokes regularity conclusions.

Lean declarations:
- `h3Path_fullSignedExcess_le_physicalRiccatiSqrtEnergy244`
- `h3Path_fullSignedExcess_le_physicalGradientEnvelope244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_physicalRiccatiLogBarrier244`

Full Lean compilation must be performed using the repository Lake toolchain; structural validation alone is not a proof check.
