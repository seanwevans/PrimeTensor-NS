# SixIntegral finite permutation orbit fix

The former `simp only` proof expanded `Fin.sum_univ_succ` but did not reduce
indexed entries of the six-element permutation vector, producing an enormous
goal containing `Matrix.vecCons` and proof-field expansions of measurable
equivalences. The earlier unrestricted `simp` with AC rewrite rules exceeded
Lean's 200,000-heartbeat budget.

Use ordinary `simp` on the six fixed permutations, explicitly expand
`MeasurableEquiv.prodComm` so swaps reduce to pair projections, and leave
AC **out of the simplifier**. Any remaining equality of six coefficients is
resolved by `ac_rfl`. The four local momentum identities are retained.

No theorem statements, assumptions or normalization factors are changed.
This patch is source-tested but not Lean-compiled in the packaging runtime.
The required local gate is `lake env lean` on `FirstMonomialTriadSixIntegral`
before registering it in `PrimeTensor.lean`. Then regenerate `proof/order.txt`,
check source coverage, compile and run `baseline.sh --reuse-build`.
