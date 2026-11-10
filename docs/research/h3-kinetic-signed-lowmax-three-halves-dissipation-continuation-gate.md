# Three-halves weighted full-H3 dissipation continuation criterion

Base commit: `2c27c3b5d522c055efb9932955c4ad8f3dca810d`.

## Physical rate and improvement

The accepted nonextension theorem supplies the pointwise cubic rate on a
sufficiently late strict tail, with fixed kinetic anchor `b`:

`1 <= B (T-t)^8 (D_3(t))^3`, where `B = 81 K^8 E_0(b)`.

Choose a further strict terminal tail on which `B^2 (T-t) <= 1`.
This is possible because `B` is a fixed finite real constant. Squaring
the cubic inequality and factoring gives

`1 <= B^2 (T-t)^16 D_3(t)^6 <= ((T-t)^5 D_3(t)^2)^3`, so
`1 <= (T-t)^5 D_3(t)^2`. Positivity and the real square root then yield

`1/(T-t) <= (T-t) sqrt(T-t) D_3(t) <= (T-t) sqrt(T-t) D_full(t)`.

Since the harmonic profile is nonintegrable on any strict terminal tail,
hypothetical nonextension implies nonintegrability of the full physical
`(T-t) sqrt(T-t)` weighted dissipation on *every* strict terminal subtail.
The contrapositive establishes smooth continuation if that weighted
dissipation is integrable on **one** strict terminal subtail. The energy-tail
version follows by measure restriction.

Unlike the previous linearly weighted condition, this is the exponent
`3/2`, a faster-vanishing terminal weight. It remains below the critical
`5/3` exponent indicated by the exact cubic balance; a sharp cube-root
statement and its endpoint integrability threshold are future work.

**Research limitation:** This is a conditional continuation criterion, not a
proof that arbitrary Navier--Stokes trajectories satisfy the weighted
integrability assumption. It introduces no new axioms or arbitrary viscous
persistence widths and does not reuse the vacuous signed-flux residual.

## Declarations

- `thirdFullKinetic_scalar_cubicRate_forces_quinticSquare244`
- `thirdFullKinetic_scalar_quinticSquare_harmonicSqrtWeight244`
- `thirdFullPhysical_noExtension_harmonicThreeHalvesDissipation244`
- `thirdFullPhysical_noExtension_threeHalvesDissipation_nonintegrable244`
- `thirdFullPhysical_threeHalvesDissipation_strictTail_forcesContinuation244`
- `thirdFullPhysical_threeHalvesDissipation_energyTail_forcesContinuation244`

All six proofs are Lean tactic proofs; no `sorry` or `admit`. Source-level
checks are not the Lean kernel; run the targeted and full Lake checks.
