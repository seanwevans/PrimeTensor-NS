import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPointwiseMild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Derivative

/-!
# Selected velocity time derivative: heat-side reduction

`SelectedPointwiseMild` gives the exact pointwise identity

    u_i(t,x) = H_t U₀_i(x) - D_i(t,x)

throughout the positive canonical restart window.

The positive-time heat term already has a genuine ordinary time derivative,
identified by `Heat.Time.Derivative` with the inverse Fourier reconstruction of
the heat-generator amplitude.

This file combines those two facts without pretending that the remaining
Duhamel diagonal derivative is already closed.  If the classical Duhamel
coordinate has derivative `dD` at one interior time, then the selected complex
velocity coordinate has derivative

    heatGenerator - dD

there.  The corresponding `deriv` equality is recorded as well.

Thus the selected temporal derivative frontier is reduced to exactly one
nonlinear pointwise statement: the time derivative of the literal classical
Duhamel integral.  No `L²` point evaluation is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityTimeDerivativeHeatReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/- Keep complex-valued paths differentiated over real time on the same
restriction-of-scalars instance used by the heat time-derivative theorem. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- At an interior positive restart time, any pointwise time-derivative formula
for the classical Duhamel term immediately yields the corresponding derivative
of the selected complex velocity coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time_of_Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (dD : ℂ)
    (hD :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      HasDerivAt
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν s W W i x)
        dD
        t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x)
      (h3SpectralScalarHeatTimeGeneratorRepresentative
          ν t (U₀ i) x
        - dD)
      t := by
  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHeat :
      HasDerivAt
        (fun s : ℝ =>
          h3SpectralScalarHeatC3Representative
            ν s (U₀ i) x)
        (h3SpectralScalarHeatTimeGeneratorRepresentative
          ν t (U₀ i) x)
        t :=
    h3SpectralScalarHeatC3Representative_hasDerivAt_time
      hν ht (U₀ i) x

  have hD' :
      HasDerivAt
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν s W W i x)
        dD
        t := by
    simpa only [W] using hD

  have hRhs :
      HasDerivAt
        (fun s : ℝ =>
          h3SpectralScalarHeatC3Representative
              ν s (U₀ i) x
            -
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν s W W i x)
        (h3SpectralScalarHeatTimeGeneratorRepresentative
            ν t (U₀ i) x
          - dD)
        t :=
    hHeat.sub hD'

  have hWindow : Set.Ioo (0 : ℝ) R ∈ 𝓝 t := by
    exact Ioo_mem_nhds ht htR

  have hEq :
      (fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x)
        =ᶠ[𝓝 t]
      (fun s : ℝ =>
        h3SpectralScalarHeatC3Representative
            ν s (U₀ i) x
          -
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν s W W i x) := by
    filter_upwards [hWindow] with s hs
    have hMild :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ hs.1 hs.2.le i
    exact congrFun hMild x

  exact hRhs.congr_of_eventuallyEq hEq

/-- Equality form of the preceding reduction.  Once the classical Duhamel
derivative is known, the ordinary derivative of the selected complex velocity
coordinate is literally heat-generator minus Duhamel derivative. -/
theorem deriv_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_of_Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (dD : ℂ)
    (hD :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      HasDerivAt
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν s W W i x)
        dD
        t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    deriv
      (fun s : ℝ =>
        h3SpectralScalarC1Representative (W s i) x)
      t
      =
    h3SpectralScalarHeatTimeGeneratorRepresentative
        ν t (U₀ i) x
      - dD := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have h :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_hasDerivAt_time_of_Duhamel
      hν U₀ hA hU₀ ht htR i x dD hD

  simpa only [W] using h.deriv

end

end Euclidean
end Bridge
end PrimeTensor
