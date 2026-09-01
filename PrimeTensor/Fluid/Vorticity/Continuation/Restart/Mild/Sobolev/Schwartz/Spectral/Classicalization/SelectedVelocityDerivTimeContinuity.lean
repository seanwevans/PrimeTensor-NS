import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityDerivativeCandidateTimeContinuity

/-!
# Classicalization: continuity of the actual selected complex time derivative

`SelectedVelocityOrdinaryTimeDerivative` identifies the ordinary derivative of
the selected complex C1 representative at every strict positive interior
restart time with an explicit candidate.

`SelectedVelocityDerivativeCandidateTimeContinuity` proves that this candidate
is continuous at every such time.

This file transfers that continuity to the actual one-dimensional `deriv`.
The transfer is local: on the open restart interval `(0,R)`, the derivative
formula holds pointwise, hence `deriv` is eventually equal near any strict
interior base time to the continuous candidate.

No new estimate and no new frontier proposition are introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityDerivTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The actual ordinary time derivative of the selected complex C1
representative is continuous at every strict positive interior restart time. -/
theorem deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (deriv
        (fun r : ℝ =>
          h3SpectralScalarC1Representative (W r i) x))
      s := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarC1Representative (W r i) x

  let G : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatTimeGeneratorRepresentative
          ν r (U₀ i) x
        -
      ((ν : ℂ) *
          (∑ j : Fin 3,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
              ν r W W i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j)))
        +
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W r) (W r) i x)

  have hCandidate :
      ContinuousAt G s := by
    dsimp only [G, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_timeDerivativeCandidate_continuousAt
        hν U₀ hA hU₀ hs hsR i x

  have hAt :
      deriv f s = G s := by
    dsimp only [f, G, W]
    exact
      deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative
        hν U₀ hA hU₀ hs hsR i x

  have hWindow :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 s := by
    apply Ioo_mem_nhds
    · exact hs
    · simpa only [R] using hsR

  have hEventuallyEq :
      G =ᶠ[𝓝 s] deriv f := by
    filter_upwards [hWindow] with r hr

    have hEq :=
      deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2)
        i x

    dsimp only [f, G, W]
    exact hEq.symm

  change
    Tendsto
      (deriv f)
      (𝓝 s)
      (𝓝 (deriv f s))

  rw [hAt]

  exact hCandidate.congr' hEventuallyEq

end

end Euclidean
end Bridge
end PrimeTensor
