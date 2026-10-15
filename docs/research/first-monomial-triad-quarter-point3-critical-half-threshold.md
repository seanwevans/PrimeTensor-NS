# Exact half-energy coefficient threshold on a positive real Schwartz ray

**Base commit:** `de52f6a5`.

The previous checkpoint excludes every energy exponent `0 ≤ θ < 1/2`
for a uniform fixed coefficient along amplitudes of one explicit real
divergence-free Schwartz velocity.

Here the critical `θ=1/2` is characterized exactly at the **scalar-ray**
level. For `M>0, E≥0, B≥0`, the estimate

    a³ M ≤ B sqrt(1 + a² E) a²       for every a>0

holds if and only if

    M² ≤ B² E.

Unlike an asymptotic argument, the Lean proof directly derives the
necessary inequality from one explicitly selected large amplitude,
and proves sufficiency by squaring the nonnegative sides.

For a real Schwartz field with positive complete 243-slot first monomial,
apply the scalar statement to `M = firstMonomial f`,
`E = |fullH3EnergyQuadratic f|`, and
`B = C * |topH3Dissipation f|`. The application is necessary for any
coefficient `C≥0` that works along the entire amplitude ray. The final
theorem selects the previously formalized positive divergence-free
quarter-packet witness.

**Limitation:** this does not establish a single `C` for all Schwartz
fields, nor positivity of every PDE energy form, nor a PDE continuation
estimate. Scaling alone cannot establish critical-endpoint sufficiency.

## Verification

Import the new file into `PrimeTensor.lean` and
`tools/audit/FirstMonomialTriad.lean`, register theorem contracts,
generate `proof/order.txt` before compilation, run the standalone Lean
file and project builds, then `bash tools/audit/baseline.sh --reuse-build`.
No `sorry` or `admit` is used. Lean compilation is unverified in the
artifact-creation environment.
