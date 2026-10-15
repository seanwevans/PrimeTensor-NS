# Necessary half-energy exponent on the real Schwartz witness

Based on commit `d5790b99`, the positive complete 243-slot first-monomial
witness `f` satisfies `M(a f) = a³ M(f)`, `E(a f) = a² E(f)`, and
`D(a f) = a² D(f)`, with `M(f) > 0` and `a > 0`.

For all fixed `C ≥ 0` and `0 ≤ θ < 1/2`, there is an explicit positive
amplitude `a` for which

    C (1 + |E(a f)|)^θ |D(a f)| < M(a f).

This sharpness statement is deliberately stronger than one with the signed
quadratic energy and dissipation: absolute values prevent relying on a hidden
nonnegativity argument. For `a ≥ 1`, the elementary bound
`1 + a² |E| ≤ a² (1 + |E|)` reduces the issue to the divergence of
`a^(1 - 2θ)`. In the Lean proof that divergence is certified by
`Real.tendsto_rpow_atTop`.

This theorem gives a *necessary* energy exponent in a global, fixed-constant
absorption estimate. It does not establish sufficiency at `θ = 1/2`, PDE
integrability, global continuation, or Navier--Stokes blowup.

## Verification

After adding the new module's root import and audit checks, regenerate
`proof/order.txt` with `python3 proof/generate_index.py`, then run `--check`,
`python3 proof/check_fragment.py --all`, `lake env lean` on the new source,
`lake build PrimeTensor`, the audit files, `lake build`, and
`bash tools/audit/baseline.sh --reuse-build` before committing.

Lean compilation is not available in the artifact preparation environment.
