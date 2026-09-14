import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity

/-!
# Zeroth-order endpoint continuity: old snapshot diffusion identification

The nonlinear half of one old canonical snapshot has now been identified with
physical advection.  This file closes the corresponding quotient-safe diffusion
bookkeeping.

For one elapsed slice `q`, the old-solution Fourier `L²` Laplacian is already
defined as the sum of the three diagonal second-jet slots.  Independently, the
generic spectral Laplacian of the canonical weighted H³ state is defined by the
contractive multiplier

    -|2πξ|² / W₃(ξ).

Both have almost-everywhere representative

    -|2πξ|² û_j(ξ).

The only bridge needed is the encoder/deweighting round trip for the same old
canonical H³ snapshot.  Consequently the two genuine `L²` classes are equal.

No endpoint continuity, selected restart, mild equation, pressure, or temporal
regularity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldDiffusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact H³ deweighting of one old canonical snapshot coordinate is the old
solution's zeroth-order Plancherel state at the same physical time. -/
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_rawFourierL2_eq_baseFourierAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) j)
      =
    velocityH3BaseFourierAt
      u
      (t + (q : ℝ))
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      j := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed
  unfold velocityH3SpectralStateAt

  exact
    h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)
      j

/-- The old quotient-safe Fourier `L²` Laplacian is exactly the generic
spectral Laplacian of the same endpoint-independent canonical H³ snapshot. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_snapshotLaplacian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q j
      =
    h3SpectralScalarLaplacianRawFourierL2
      ((h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) j) := by
  apply MeasureTheory.Lp.ext

  have hOld :=
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae
      hNS ht hEnd hTail q j

  have hIdentify :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed_rawFourierL2_eq_baseFourierAt
      hNS ht hEnd hTail q j

  rw [← hIdentify] at hOld

  have hNew :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      ((h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) j)

  filter_upwards [hOld, hNew] with xi hOldXi hNewXi

  rw [hOldXi, hNewXi]

end

end Euclidean
end Bridge
end PrimeTensor
