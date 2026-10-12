# Initial actual physical-source reconstruction and automatic measurability

Parent commit: `91b86744` (derive initial actual spectral Laplacian and Leray source bounds).

## Correctness correction to the parent module

The original definitions of `h3AuditSpectralPhysicalLaplacian` and
`h3AuditSpectralPhysicalLerayForcing` applied `h3RealPartFourierL2` and
`h3FromFourierRealL2` directly to **raw Fourier frequency** states. The latter
is a measure-preserving carrier identification and *not* the Fourier inversion
operator. Without inversion, these objects are not the claimed physical-space
Laplacian and nonlinear forcing.

This patch corrects both definitions to the map

```
raw Fourier L²
  → (Lp.fourierTransformₗᵢ ...).symm
  → h3RealPartFourierL2
  → h3FromFourierRealL2
  → WithLp.toLp 2 (three coordinates)
```

It adds the inverse Plancherel isometry to each of the two parent norm proofs.
The numerical constants `3` and `3 * 576 * π * C₃` are unchanged. No theorem
statement changes; the meanings of the two source definitions are corrected.

## New continuity/measurability theorems

`OneComponentInitialActualPhysicalSourceMeasurability.lean` proves:

- `continuous_h3AuditSpectralPhysicalLaplacian`
- `continuous_h3AuditSpectralPhysicalLerayForcing`
- `h3Audit_initialActualSpectralVelocity_continuousAt`
- `h3Audit_initialActualSpectralVelocity_continuousOn`
- `h3Audit_initialActualSpectralSources_aestronglyMeasurable`
- `h3Audit_initialActualSpectralSources_integrable_of_H3Energy`
- `h3Audit_initialActualSpectralSources_implies_diffusionLerayData`
- Conditional compact weak comparison and physical initial trace consequences.

These use the repository's local canonical restart window and spectral state
continuity, joint quadratic Leray forcing continuity, and the finite `PiLp`
wrapper. There is no continuity assumption at `t = 0`.

The new initial data predicate `H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData`
retains **only** initial H³-energy integrability, strict-time weak momentum
pairing derivative for these specific reconstructed sources, and the vanishing
old/selected comparison residual, in addition to the existing initial datum
and restart scale. Source measurability, source-specific Bochner integrability,
and source-to-energy bounds are derived, not assumed.

## Remaining mathematical obligations

- Identify these reconstructed physical `L²` source classes with the actual
  spatial Laplacian and Leray-projected nonlinear transport of the physical PDE
  at all strictly positive times. The repository has positive-restart
  coordinatewise identification theorems; these must be transferred to the
  global actual-time construction.
- Prove the strict-time scalar momentum derivative for all Schwartz tests;
  this module keeps it explicit.
- Establish initial `L¹(0,b)` control of the actual normalized H³ energy;
  positive-time admissibility alone does not supply this.
- Discharge the epsilon-vanishing old/selected relative-energy residual.
- Independently discharge the terminal actual-vorticity strong-H³ endpoint
  for any unconditional full-time continuation claim.

## Verification

The ZIP was checked for internal path/CRC integrity and no `sorry` or `admit`
occurrences. **Lean / Lake are not installed in the packaging environment.**
Compile the patched parent file first and then the new module, followed by
`lake build` and the repository baseline audit. Do not push if any check fails.

## Compiler repair: Fourier-carrier finite-axis instance

The Lean `Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ` construction depends on
`NormedAddCommGroup H3FourierPoint3`. Here `H3FourierPoint3` is a finite
Euclidean product over `PrimeTensor.Axis Depth.three`. Other modules declare
the axis `Fintype` as a **local** instance, and those instances are not
exported across imports. Both modified/new audit modules now declare their own
local `Fintype` instance before constructing the inverse transform.

This addresses the two reported `synthInstanceFailed` diagnostics. The
subsequent `isDefEq`/`whnf` timeouts and unknown downstream norm lemma are
consistent with elaboration cascading from the missing instance, but remain
subject to a local recompilation. A targeted heartbeat increase is included
for elaboration of the nested Fourier/Hilbert expressions. No theorem
statement or PDE assumption was changed by this repair.
