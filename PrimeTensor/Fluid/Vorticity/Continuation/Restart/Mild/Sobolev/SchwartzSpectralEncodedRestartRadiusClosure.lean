import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralMildPhysicalRestartRadiusClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityBridge

/-!
# Encoded real H³ data at the canonical restart radius

The canonical-radius closure theorem above starts from an arbitrary weighted
spectral H³ state.  A classical restart slice enters the spectral theory
through `velocityH3SpectralStateAt`, once the concrete H³ integrability,
measurability, and Fourier-compatibility hypotheses have been supplied.

This file joins those interfaces without claiming the still-missing classical
field/gluing theorem.  For a genuine encoded real H³ snapshot it records three
facts at the canonical positive restart radius:

* the initial real decoder is exactly the transported physical velocity slice;
* every selected physical-time slice is genuinely real, not merely projected
  to its real part;
* the complete canonical-radius step has the exact physical heat-plus-remainder
  decomposition, with the nonlinear remainder in the Schwartz heat--Leray
  physical-realization set.

Thus the remaining continuation frontier is no longer spectral realization.
It is the passage from this decoded real `L²` mild path to the classical real
`C³` Navier--Stokes continuation/gluing interface.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- At the encoded restart slice, the canonical real decoder recovers the
transported zeroth-order physical velocity component exactly. -/
theorem h3SpectralEncodedRestartRadius_initial_decodeRealL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    h3SpectralVelocityDecodeRealL2
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j
      =
    h3ToFourierRealL2
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)) := by
  exact
    h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
      hFourier j

/-- Every physical-time slice of the canonical-radius mild solution started
from encoded real data is exactly the complexification of its real decoder. -/
theorem h3SpectralEncodedRestartRadius_allSlices_real
    {ν A : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀bound :
      ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ A)
    (q : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (j : Fin 3) :
    h3SpectralFinHeatLerayPhysicalDecodedComplexL2
        hν
        (h3FinHeatLerayRestartRadius_pos ν hA).le
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound
        (h3FinHeatLerayRestartRadius_smallness ν hA.le)
        q j
      =
    h3ComplexifyFourierL2
      (h3SpectralFinHeatLerayPhysicalDecodedRealL2
        hν
        (h3FinHeatLerayRestartRadius_pos ν hA).le
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound
        (h3FinHeatLerayRestartRadius_smallness ν hA.le)
        q j) := by
  exact
    h3SpectralFinHeatLerayPhysicalDecoded_encoded_eq_complexify_real
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      hFourier
      hA
      hU₀bound
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      q j

/-- The full canonical-radius restart step for an encoded real H³ snapshot has
both exact initial decoding and a physically realized nonlinear remainder. -/
theorem h3SpectralEncodedRestartRadius_fullStep_realized
    {ν A : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀bound :
      ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ A) :
    let U₀ : H3SpectralVelocityState :=
      velocityH3SpectralStateAt u t hInt hMeas hFourier
    let T : NNReal := h3FinHeatLerayRestartRadiusNN ν A hA
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀bound
    let R : H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν 0 hν W W T
    (∀ j : Fin 3,
      h3SpectralVelocityDecodeRealL2 U₀ j
        = h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))
      ∧
    (
      h3SpectralFinVectorDecodeComplexL2 (W (T : ℝ))
          = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W 0)
            + h3SpectralFinVectorDecodeComplexL2 R
        ∧
      h3SpectralFinVectorDecodeComplexL2 R
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (T : ℝ) hν
    ) := by
  dsimp only
  constructor
  · intro j
    exact
      h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
        hFourier j
  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_fullStep_realized
        hν
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA
        hU₀bound

end

end Euclidean
end Bridge
end PrimeTensor
