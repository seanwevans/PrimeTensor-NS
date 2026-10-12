# Initial projected RHS from an integrable H³-energy envelope

Base checkpoint: `5cdc2711` (`derive initial projected RHS from diffusion and Leray transport`).

New module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialH3EnergyMajorizedProjectedRHS.lean`.

## Actual mathematical increment

The prior `H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData` explicitly assumes both `IntervalIntegrable D volume 0 b` and `IntervalIntegrable N volume 0 b`. The new data contract replaces those source-integrability assumptions by:

- `IntervalIntegrable (velocityH3EnergyAt u) volume 0 b`;
- `AEStronglyMeasurable` of `D` and `N` under the measure restricted to `(0,b]`;
- concrete estimates `‖D(t)‖ ≤ cD * velocityH3EnergyAt u t` and `‖N(t)‖ ≤ cN * velocityH3EnergyAt u t` on `[0,b]`, with `cD,cN ≥ 0`.

The generic physical-Hilbert domination theorem applies `Integrable.mono'` under the restricted measure. In particular both physical source paths become Bochner interval-integrable. The quantitative bound is

`∫₀ᵇ ‖D(s)-N(s)‖ ds ≤ (cD+cN) * ∫₀ᵇ velocityH3EnergyAt u s ds`.

The old projected-RHS weak FTC then follows from the previous positive-time scalar derivative criterion. The new theorem `h3Audit_initialH3EnergyMajorized_implies_diffusionLerayData` feeds the old source contract with derived integrability and preserves the epsilon-vanishing residual. Subsequent results retain initial compact weak-test uniqueness, physical initial `L²` and upper `H³` traces, and the conditional full-time transverse estimates.

## Explicit remaining PDE obligations

1. Initial integrability of the **actual** `velocityH3EnergyAt u` is not implied by merely having `LoggedPreterminalH3PathAdmissible u T` on positive times.
2. The source functions are meant to represent the literal physical diffusion and Leray transport, but their identification and the pointwise source-energy estimates remain hypotheses.
3. Positive-time scalar momentum derivatives for every Schwartz probe remain hypotheses (not an automatic consequence of this new integrability result).
4. The epsilon-vanishing old/selected relative-energy comparison is independent.
5. The terminal actual-vorticity strong-`H³` endpoint is independent. No unconditional global regularity or blowup exclusion is claimed.

## Verification

No `sorry`, `admit`, or new axioms introduced by the source patch. ZIP integrity can be checked in the container; only the user's local Lean/mathlib project environment can confirm elaboration and full `lake build`.
