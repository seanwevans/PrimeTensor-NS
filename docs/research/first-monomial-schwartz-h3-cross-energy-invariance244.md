# Signed Schwartz H³ completion is invariant under E₂/E₃ equivalence

Starting from `9c752c0d`, the already formalized completed signed Schwartz
first monomial is known to be invariant under vanishing cross-sequence
81+27 mixed L²/L⁴ derivative discrepancy.

This patch upgrades the invariant criterion to the *ordinary quadratic*
second- and third-order Schwartz energy differences: if, at matching indices,
`E₂(f_n-g_n) → 0` and `E₃(f_n-g_n) → 0`, then all 81 third-jet real L² roots
and all 27 second-jet real L⁴ roots vanish in the limit. The former follows
by the proven root-square ≤ E₃ estimate; the latter from the established
fourth-power Gagliardo–Nirenberg inequality in eighth-power root form.
The finite sums converge, so the prior cross-graph invariance theorem gives
equality of the completed signed values.

This is a precise approximation independence statement for the E₂/E₃
Schwartz completion. It neither constructs Schwartz density in a specified
physical H³ Hilbert space nor identifies the completed scalar with an
existing physical transport pairing. Those are separate obligations.
