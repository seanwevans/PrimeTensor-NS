# Quantitative physical solenoidal scalar momentum residual

Base commit: `ca19a74e`.

## Mathematical result

Given a Leray-fixed physical Hilbert vector `D`, the bound
`‖⟪φ,D⟫‖ ≤ η ‖φ‖` for **all compact smooth divergence-free tests** implies
`‖D‖ ≤ η`. This uses the exact established density identity of their closed
span with the Leray-fixed physical `L²` submodule. The sharp constant 1 is
preserved. This lemma is independent of any pressure-gradient `L²` state.

Apply the lemma to the actual physical projected FTC defect
`D(a,r) = U(r)-U(a)-∫ₐʳ R(s) ds`. The old physical velocity and projected
source are already in physical `L²`, so its Hilbert pairings coincide with
the scalar compact-test residual. Uniform scalar test-dual error at most `η`
on every prefix yields `‖D(a,r)‖ ≤ η`; arbitrarily small errors imply genuine
Hilbert FTC and full compact solenoidal weak evolution. Failure of FTC forces
an error floor for these scalar test-dual bounds.

This changes the remaining analytic premise from **constructing a strong
Hilbert residual** to proving **quantitatively small scalar residuals against
divergence-free tests**. Old/classical pressure gradients never need a
physical `L²` representative. The actual scalar temporal integration by parts
and vanishing residual estimate still require proof from the preterminal PDE;
no unconditional regularity/continuation is asserted.

## Audit

Run `python3 tools/audit/register_first_monomial_physical_top_quant_solenoidal_residual244.py`,
`python3 proof/generate_index.py`, and Lean build/audit. The new declarations
are audited with `#check` and `#print axioms`.
