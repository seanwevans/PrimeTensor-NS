import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldJetFourierSchwartzWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Weak.Compact.Zero

/-!
# Pressure-free closure of the weak H³ spectral frontier

`OldJetFourierSchwartzWeak` proves pressure-free real-part weak continuity of
every old Fourier H³ jet coordinate against every complex Schwartz frequency
test.

`WeakCompactZero` already contains the exact weighted-spectral pairing identity
for a smooth compact weighted test `g`:

    ⟪W₃ ûⱼ, g⟫
      =
    ⟪ûⱼ, W₃ g⟫,

and packages `W₃ g` as a complex Schwartz function.

Therefore its previous strong-zero / pressure input is no longer required.
The new Fourier weak theorem supplies continuity of the right-hand side
directly.  The existing smooth-compact density theorem then lifts this to
arbitrary weighted spectral `L²` tests.

Consequently the complete third-order weak-plus-norm frontier now depends only
on coordinate-norm continuity.  No pressure estimate, temporal derivative, or
zeroth-order strong continuity is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdWeakPressureFree
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Smooth-compact weighted spectral weak continuity follows directly from the
pressure-free Fourier-Schwartz weak theorem. -/
theorem h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j F hFcompact

  rcases hFcompact with
    ⟨g, hF, hcompact, hsmooth⟩

  let Ψ : 𝓢(H3FourierPoint3, ℂ) :=
    h3SmoothCompactReweightedSchwartz
      g hcompact hsmooth

  have hFourier :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (inner ℂ
            (h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q)
            (Ψ.toLp
              2 (volume : Measure H3FourierPoint3))).re) :=
    continuous_re_inner_h3PreterminalCanonicalFourierJetOnElapsed_schwartz
      hNS ht hEnd hE hTail Ψ (h3JetSlot0 j)

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j)
          F).re)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q)
          (Ψ.toLp
            2 (volume : Measure H3FourierPoint3))).re) := by
    funext q

    rw [
      inner_h3PreterminalTailCanonicalSpectralStateOnElapsed_smoothCompact_eq_zeroFourier_reweighted
        hNS ht hEnd hTail q j F g hF hcompact hsmooth
    ]

  rw [hEq]

  exact hFourier

/-- Arbitrary weighted spectral weak continuity is now pressure-free. -/
theorem h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_smoothCompact
      hNS ht hEnd hE hTail
      (h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_pressureFree
        hNS ht hEnd hE hTail)

/-- Locally, coordinate-norm continuity is now the only additional input needed
for weak-plus-norm continuity. -/
theorem h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_coordinateNorm_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hNorm :
      H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    ⟨
      h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_pressureFree
        hNS ht hEnd hE hTail,
      hNorm
    ⟩

/-- Restart-radius coordinate-norm continuity closes the full restart-radius
weak-plus-norm frontier without any pressure hypothesis. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_coordinateNorm_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hNorm :
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_coordinateNorm_pressureFree
      hNS ht hEnd hE hTail
      (hNorm q hqPos hEnd)

/-- Globally, the third-order weak-plus-norm frontier reduces to coordinate
norm continuity alone. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_coordinateNorm_pressureFree
    (hNorm :
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_coordinateNorm_pressureFree
      hNS ht hE hTail
      (hNorm E hE u T t hNS ht hTail)

/-- Coordinate-norm continuity alone now closes the existing ordered-third
physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_coordinateNorm_pressureFree
    (hNorm :
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_weakNorm
      (h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_coordinateNorm_pressureFree
        hNorm)

end

end Euclidean
end Bridge
end PrimeTensor
