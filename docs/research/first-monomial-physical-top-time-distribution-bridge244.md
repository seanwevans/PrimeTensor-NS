# Strict-time distributional momentum bridge (checkpoint `b7bea8bd`)

**Goal:** Formulate the actual physical H³ velocity and projected source as
regular distributions on `(a,b)` and reduce the distributional weak momentum
identity to an explicit compact-time-test formula. This is groundwork for
proving weak FTC directly from the classical preterminal PDE without assuming
pointwise differentiation of spatial integrals.

## What is established

For `0 < a < b < T` and any compact smooth physical test vector `φ`, the actual
L² velocity and Leray-projected source have scalar pairings

`mφ(t) = ⟨φ,U(t)⟩` and `rφ(t) = ⟨φ,R(t)⟩`.

Existing strong L² continuity proves that both scalar functions are **locally
integrable on `(a,b)`**, so the locally defined `h3PathRegularTimeDistribution244` represents their genuine
regular distributions (rather than yielding zero for nonintegrable inputs).

The new exact equivalence is

`∂ₜ T_{mφ} = T_{rφ}` in distributions on `(a,b)`

if and only if, for every smooth compactly supported time test `θ`,

`-∫ θ'(t)mφ(t) dt = ∫ θ(t)rφ(t) dt`.

The derivative is represented by mathlib's `TestFunction.lineDerivCLM` in the
unit real-time direction. A further theorem removes an arbitrary pressure
functional `P(φ,θ)` from the tested equation when it vanishes on compact
solenoidal spatial tests. In addition, a snapshotwise-vanishing pressure pairing
`P(φ,t)` integrates to zero against every compact smooth temporal test,
so no independent space-time norm bound of the pressure is needed for that
final cancellation (the derivation of the tested PDE remains a separate issue).

## What remains open

1. Derive the joint spacetime-tested equation from the separately classical
   physical preterminal NSE, including a justified space/time integration
   exchange or distributional weak formulation. Snapshotwise pressure
   cancellation is not by itself this theorem.
2. Prove the distributional temporal primitive uniqueness upgrade for a
   **continuous** scalar momentum path and a continuous projected source,
   thereby obtaining physical weak FTC without postulating absolute
   continuity. In a continuous one-dimensional setting this is standard
   mathematically, but it has not been formalized in this patch.

No assertion of unconditional NSE regularity or H³ continuation is made.

## Pinned mathlib compatibility (proof fix)

At the repository's mathlib revision `a021f70d9761`, the name
`Distribution.ofFun` is not yet defined. The equivalent regular-distribution
constructor here is `TestFunction.integralAgainstBilinCLM` specialized to real
scalar multiplication. Its evaluation on locally integrable scalar time
functions is proved through `TestFunction.integralAgainstBilinCLM_eq_integral`.
This changes no mathematical premises.

### Compact-convergence type-copy repair (October 23)

The pinned `Distribution Ω ℝ ⊤` is an alias of the compact-convergence
`UniformConvergenceCLM` type, not directly the `ContinuousLinearMap`
produced by `TestFunction.integralAgainstBilinCLM`.  The repair inserts
`UniformConvergenceCLM.ofFun` explicitly and unfolds its identity
underlying map with `change` in the evaluation lemma.  Neither
the source distribution nor the physical momentum assumptions change.
