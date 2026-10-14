# Six-integral orbit identity: bounded simplification repair

The root-coverage audit found a locally present but uncompiled
`FirstMonomialTriadSixIntegral.lean`. The first failed theorem was
`h3SchwartzTriadSixKernel_eq_orbit` at line 101. Its `simp` call
unfolded a six-term orbit while treating `add_comm`, `add_left_comm`, and
`add_assoc` as simp rewrites. Lean's AC-ordering comparison (`acLt`)
reached its default 200,000-heartbeat limit.

`tools/audit/fix_first_monomial_six_integral_orbit.py` is an idempotent,
fail-closed local patcher for that exact tactic. It removes the three
unrestricted AC simp arguments and uses `ac_rfl` *after* unfolding the
specific six permutations and the four already proved vector identities.
The theorem statement and the six-order signed integral are unchanged.

The patch operates against the local module, which was not committed at
the reference checkpoint. It does not assume its contents are present in
the published GitHub tree. The source must first typecheck with the
pinned Lean toolchain, then its Lake module target must compile, before
it can be imported into the root or claimed as covered by the baseline.

`python3 proof/generate_index.py` and its `--check` run after source
registration, and `proof/order.txt` is committed. No custom axioms,
`sorry`, or `admit` are introduced by this repair.
