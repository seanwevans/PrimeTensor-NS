# The actual projected-source L¹ action vanishes on critical-eighth cofinal windows

Base commit: `ff12ca3c082dae0f5b1a48378c8f28d9fea17a45`.

## The mathematical obstacle

The constructive critical-eighth source-clock theorem gives disjoint, minimal
first-crossing windows with `δ(vk) (vk+1)^8 -> 0`. Their attained physical
source maximum `C(vk)` can exceed every fixed multiple of `(vk+1)^8`, and
`C(vk) δ(vk)` need not be small merely from this clock condition.

It is essential not to confuse a pointwise source peak with the *actual
integrated momentum source*. The repository already proves
`h3Critical_projected_source_integrable_of_finite_dissipation`:

    finite ∫_a^T velocityH3DissipationAt(u,t) dt
      -> projected physical momentum source belongs to L¹(b,T;L²_x)

for any strict `a < b < T`.

## New hard transfer

The theorem `thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244`
uses the continuous scalar primitive of the nonnegative integrable function
`‖G(t)‖` to establish:

    τ_k -> T, σ_k -> T, b ≤ τ_k ≤ σ_k ≤ T eventually
      -> ∫_{τ_k}^{σ_k} ‖G(t)‖ dt -> 0.

The key is continuity at T of `P(t)=∫_b^t ‖G(s)‖ ds` and the exact identity
`∫_{τ_k}^{σ_k} ‖G‖ = P(σ_k)-P(τ_k)` for the actual interval endpoints.
This controls **absolute source action**, not merely the signed Bochner
momentum increment.

Next, `thirdFullPhysical_criticalEighth_minimalWindows_sourceL1_tendsto_zero244`
instantiates this for the selected physical windows. Their right endpoints
converge to T because the positive widths satisfy
`0 ≤ δ(vk) ≤ T-τ(vk) -> 0`; no separate clock-rate estimate is needed.

Finally, `thirdFullPhysical_noH3Trace_criticalEighth_sourceL1Tail244` carries
the stronger L¹ action conclusion on the exact witnesses from the prior
source-clock theorem, together with summable eighth-order window clocks,
vanishing raw annular kinetic mass, the actual minimal-carrier outer escape,
and the attained source-peak alternative.

## Why this changes the research direction

An arbitrarily large attained source peak may have arbitrarily little L¹
mass; the existing peak alternative alone cannot force a contradiction.
The next hard analytic obligation is a *lower* bound for integrated source
activity or an H³ energy/gronwall argument from the actual signed PDE
transport. Existing absolute L¹ terminal integrability rules out treating
peak height alone as an obstruction.

## Verification

Source-only patch. Registrar checks theorem declarations and rejects proof
placeholders. Regenerate the index, compile this module with the pinned
Lean/mathlib toolchain, build the full root and audit before committing.
No Lean toolchain is installed in the packaging environment, so compiler
verification is a required user-side gate.
