import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelHessianTraceMild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedHessianTraceTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.GeneratorContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.HessianTraceRepresentative

/-!
# Classicalization: time continuity of the viscosity-scaled selected Duhamel Hessian trace

The selected Duhamel right derivative contains

    ν * trace(D² Duhamel(t)).

The preceding classicalization increments now provide exactly the two pieces
needed to prove continuity of this term without differentiating the retarded
integral again.

First, the twice-spatially-differentiated selected mild equation gives

    trace(D² Duhamel)
      =
    trace(D² Heat) - trace(D² Selected).

Second, the scalar positive-time heat equation identifies

    ν * trace(D² Heat)
      =
    heatTimeGenerator.

Therefore, throughout the strict positive interior restart interval,

    ν * trace(D² Duhamel)
      =
    heatTimeGenerator - ν * trace(D² Selected).

The heat generator is continuous at every positive time, and the selected
Hessian trace is continuous at every strict interior restart time.  This file
packages the resulting continuity of the exact first summand appearing in the
selected Duhamel right-derivative candidate.

No new Fourier, endpoint, or source-time estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelHessianTraceTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- At every strict positive interior restart time, the viscosity-scaled
diagonal trace of the selected Duhamel Hessian is continuous in time.  This is
the exact Hessian term occurring in the selected classical Duhamel right
derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_viscosity_mul_diagonalTrace_continuousAt
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
      (fun r : ℝ =>
        (ν : ℂ) *
          (∑ j : Fin 3,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
              ν r W W i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j))))
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν r W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j)))

  let H : ℝ → ℂ :=
    fun r =>
      h3SpectralScalarHeatTimeGeneratorRepresentative
        ν r (U₀ i) x

  let S : ℝ → ℂ :=
    fun r =>
      ∑ j : Fin 3,
        iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative (W r i))
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 j))

  have hHeatContinuous :
      ContinuousAt H s := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatTimeGeneratorRepresentative_continuousAt_time
        hν hs (U₀ i) x

  have hSelectedContinuous :
      ContinuousAt S s := by
    dsimp only [S, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_secondFrechet_diagonalTrace_continuousAt
        hν U₀ hA hU₀ hs hsR i x

  have hScaledSelectedContinuous :
      ContinuousAt
        (fun r : ℝ => (ν : ℂ) * S r)
        s := by
    exact
      continuousAt_const.mul hSelectedContinuous

  have hRhsContinuous :
      ContinuousAt
        (fun r : ℝ =>
          H r - (ν : ℂ) * S r)
        s := by
    exact
      hHeatContinuous.sub hScaledSelectedContinuous

  have hRewrite
      (r : ℝ)
      (hr : 0 < r)
      (hrR : r ≤ h3FinHeatLerayRestartRadius ν A) :
      D r
        =
      H r - (ν : ℂ) * S r := by
    have hMild :
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν r W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j)))
          =
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarHeatC3Representative
              ν r (U₀ i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j)))
          -
        (∑ j : Fin 3,
          iteratedFDeriv ℝ 2
            (h3SpectralScalarC1Representative
              (W r i))
            x
            (fun _ : Fin 2 =>
              h3FourierAxisDirection (h3AxisOfFin3 j))) := by
      simpa only [W] using
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_diagonalTrace_eq_heat_sub_selected
          hν U₀ hA hU₀ hr hrR i x

    have hHeat :
        h3SpectralScalarHeatTimeGeneratorRepresentative
            ν r (U₀ i) x
          =
        (ν : ℂ) *
          (∑ j : Fin 3,
            iteratedFDeriv ℝ 2
              (h3SpectralScalarHeatC3Representative
                ν r (U₀ i))
              x
              (fun _ : Fin 2 =>
                h3FourierAxisDirection (h3AxisOfFin3 j))) := by
      exact
        h3SpectralScalarHeatTimeGeneratorRepresentative_eq_viscosity_mul_hessianTrace
          hν hr (U₀ i) x

    dsimp only [D, H, S]

    rw [hMild]
    rw [hHeat]
    ring

  have hAt :
      D s
        =
      H s - (ν : ℂ) * S s :=
    hRewrite s hs hsR.le

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        H r - (ν : ℂ) * S r
          =
        D r := by
    filter_upwards [hInterior] with r hr
    exact
      (hRewrite r hr.1 hr.2.le).symm

  change
    Tendsto
      D
      (𝓝 s)
      (𝓝 (D s))

  rw [hAt]

  exact
    hRhsContinuous.congr' hEventuallyEq

end

end Euclidean
end Bridge
end PrimeTensor
