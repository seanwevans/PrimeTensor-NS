# Six-integral source coverage: normalize the product swaps

The original six-orbit identity used a global `simp` with the three AC
addition rewrites, exhausting the simplifier's heartbeat budget.  The first
repair removed those rewrites, but `ac_rfl` left `MeasurableEquiv.prodComm`
applications intact.  This patch explicitly rewrites the measurable product
commutor to a swapped pair, then applies the four previously proved
frequency identities `h1` through `h4` via `simp only` before `ac_rfl`.

This patch changes only the proof tactic in the still-local
`FirstMonomialTriadSixIntegral.lean`.  It introduces no new axiom or
assumption and does not alter the six-permutation identity.  Compile the
module on the user's Lean toolchain before registering it in the root
source inventory; do not claim its proof checked before that compilation.

The registration helper then makes this formerly uncovered module root
reachable.  Regenerate the proof index, run the full source coverage audit,
then commit all source and index changes together.
