import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Mild.NineQuarter.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarter.Forcing.Envelope

/-!
# Quantitative selected five-quarter forcing mass

`MildNineQuarterMass` now gives an explicit pointwise `9/4` raw Fourier mass
envelope for every coordinate of the selected positive-time mild state:

    m₉/₄(W(t)_k)
      ≤
    h3SelectedMildNineQuarterMomentEnvelope ν A t.

`ThirdVariationZeroEnvelope` already supplies the uniform unweighted mass

    m₀(W(t)_k)
      ≤
    h3SelectedRestartRawFourierL1Envelope A.

The generic forcing algebra in `FiveQuarterForcingEnvelope` therefore applies
directly to the diagonal Navier--Stokes forcing.  This file packages the
resulting selected pointwise `5/4` forcing envelope:

    m₅/₄(N(W(t),W(t))_i)
      ≤
    B₅(
      h3SelectedRestartRawFourierL1Envelope A,
      h3SelectedMildNineQuarterMomentEnvelope ν A t).

No convolution, derivative, divergence, or Leray estimate is reopened here.
The only remaining step for the full-third variation criterion is to
uniformize the scalar `9/4` state envelope over a positive interval `[a,t]`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedForcingFiveQuarterMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit pointwise `5/4` forcing envelope for one coordinate of the
selected nonlinear forcing. -/
noncomputable def h3SelectedForcingFiveQuarterMassEnvelope
    (ν A t : ℝ) : ℝ :=
  h3FiveQuarterForcingDiagonalEnvelope
    (h3SelectedRestartRawFourierL1Envelope A)
    (h3SelectedMildNineQuarterMomentEnvelope ν A t)

/-- Every selected positive-time forcing coordinate has an explicit `5/4`
raw Fourier mass bound obtained by substituting the already-closed `m₀` and
`m₉/₄` state envelopes into the generic diagonal forcing estimate. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMass_le_selectedEnvelope
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass
        (W t) (W t) i
      ≤
    h3SelectedForcingFiveQuarterMassEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (W t k)
          ≤
        h3SelectedRestartRawFourierL1Envelope A := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ t k

  have hW9 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (W t k)
          ≤
        h3SelectedMildNineQuarterMomentEnvelope ν A t := by
    intro k
    dsimp only [W]
    simpa only [h3SpectralScalarRawFourierNineQuarterMass] using
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le
        hν U₀ hA hU₀ ht htR k)

  have hWq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR k

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  let k0 : Fin 3 := 0

  have hMass0 :
      0 ≤ h3SpectralScalarRawFourierNineQuarterMass (W t k0) :=
    h3SpectralScalarRawFourierNineQuarterMass_nonneg (W t k0)

  have hM9nonneg :
      0 ≤ h3SelectedMildNineQuarterMomentEnvelope ν A t :=
    le_trans hMass0 (hW9 k0)

  have hBase :=
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_diagonalEnvelope
      (W t) i
      hM0nonneg
      hM9nonneg
      hW0
      hW9
      hWq

  unfold h3SelectedForcingFiveQuarterMassEnvelope
  exact hBase

end
end Euclidean
end Bridge
end PrimeTensor
