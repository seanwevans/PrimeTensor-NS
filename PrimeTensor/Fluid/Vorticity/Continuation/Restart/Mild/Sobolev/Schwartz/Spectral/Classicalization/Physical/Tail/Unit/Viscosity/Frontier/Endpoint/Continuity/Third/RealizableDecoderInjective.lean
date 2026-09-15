import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.WeakStrongDenseOverlap
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.VariationOfConstants.State

/-!
# Injectivity of the real decoder on realizable H³ spectral states

The canonical real decoder is not injective on arbitrary complex spectral
states: taking a real part can discard information.

It is injective on the physically realizable subspace.  For a realizable state,
the full complex decoder is exactly the complexification of the real decoder,
and exact H³ deweighting is already injective.

This file also records that the selected mild restart launched from genuine
encoded real H³ data is realizable at every physical time in the canonical
restart radius.  These are precisely the two facts needed to turn local
physical endpoint agreement into exact weighted-H³ spectral equality.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal Interval Topology ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3RealizableDecoderInjective
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact complex spectral decoder is injective.

Its Fourier transform is the exact deweighted raw Fourier `L²` state, and that
deweighting map is already known to be injective. -/
theorem h3SpectralScalarDecodeComplexL2_injective :
    Function.Injective h3SpectralScalarDecodeComplexL2 := by
  intro F G hDecode

  apply h3SpectralScalarRawFourierL2_injective

  have hFourier :=
    congrArg
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      hDecode

  simpa only [
    h3Fourier_h3SpectralScalarDecodeComplexL2
  ] using hFourier

/-- On realizable scalar states the real decoder loses no information, hence it
is injective. -/
theorem h3SpectralScalarDecodeRealL2_eq_imp_eq_of_realizable
    {F G : H3SpectralScalarState}
    (hF : H3SpectralScalarRealizable F)
    (hG : H3SpectralScalarRealizable G)
    (hDecode :
      h3SpectralScalarDecodeRealL2 F
        =
      h3SpectralScalarDecodeRealL2 G) :
    F = G := by
  apply h3SpectralScalarDecodeComplexL2_injective

  calc
    h3SpectralScalarDecodeComplexL2 F
        =
      h3ComplexifyFourierL2
        (h3SpectralScalarDecodeRealL2 F) := hF
    _ =
      h3ComplexifyFourierL2
        (h3SpectralScalarDecodeRealL2 G) := by
          rw [hDecode]
    _ =
      h3SpectralScalarDecodeComplexL2 G := hG.symm

/-- Velocity-state version: equality of all real decoded velocity components
identifies two realizable weighted H³ spectral states exactly. -/
theorem h3SpectralVelocityDecodeRealL2_eq_imp_eq_of_realizable
    {U V : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U)
    (hV : H3SpectralVelocityRealizable V)
    (hDecode :
      h3SpectralVelocityDecodeRealL2 U
        =
      h3SpectralVelocityDecodeRealL2 V) :
    U = V := by
  funext j

  apply
    h3SpectralScalarDecodeRealL2_eq_imp_eq_of_realizable
      (hU j)
      (hV j)

  exact congrFun hDecode j

/-- Every canonical-radius physical-time selected slice launched from a genuine
encoded real H³ snapshot is realizable. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_encoded_realizable
    {ν A : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas)
    (hA : 0 < A)
    (hU₀ :
      ‖velocityH3SpectralStateAt
          u t hInt hMeas hFourier‖
        ≤ A)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A)) :
    H3SpectralVelocityRealizable
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
        hA
        hU₀
        (q : ℝ)) := by
  have hSelected :=
    h3SpectralFinHeatLerayPhysicalMildSolution_encoded_realizable
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      hFourier
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      q

  simpa only [
    h3SpectralFinHeatLerayPhysicalMildSolution_apply,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  ] using hSelected

end

end Euclidean
end Bridge
end PrimeTensor
