import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityHessianTraceGradientTimeContinuity

/-!
# Classicalization: selected mixed-derivative candidate time continuity

The two analytic pieces of the spatial derivative of the selected velocity PDE
are now separately time-continuous:

* the viscosity-weighted gradient of the selected Hessian trace;
* the spatial partial of the instantaneous nonlinear forcing.

Therefore their difference,

    ν * ∂ₐ tr(D² uᵢ) - ∂ₐ Nᵢ(u,u),

is time-continuous at every strict positive interior restart time.

This is exactly the PDE-predicted value of `∂ₐ ∂ₜ uᵢ`.  No new estimate,
regularity theorem, or derivative commutation is introduced here.  The next
layer only has to identify this continuous candidate with the actual spatial
partial of the already-proved temporal derivative field.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityMixedDerivativeCandidateTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar-coordinate form: the PDE-predicted mixed spatial/time derivative is
time-continuous. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_mixedDerivativeCandidate_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        ν *
            (∑ k : Fin 3,
              spatial3.d a
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W r i))))
                x)
          -
        spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r) i y).re)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLinear :
      ContinuousAt
        (fun r : ℝ =>
          ν *
            (∑ k : Fin 3,
              spatial3.d a
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W r i))))
                x))
        s := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_viscosityHessianTraceGradient_continuousAt
        hν U₀ hA hU₀ hs hsR i x a

  have hForcing :
      ContinuousAt
        (fun r : ℝ =>
          spatial3.d
            a
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W r) (W r) i y).re)
            x)
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_continuousAt_time
        hν U₀ hA hU₀ hs hsR i x a

  exact hLinear.sub hForcing

/-- Velocity-component form of the same continuous mixed-derivative
candidate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_mixedDerivativeCandidate_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        ν *
            (∑ k : Fin 3,
              spatial3.d a
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        hν U₀ hA hU₀ r y).component j)))
                x)
          -
        spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W r) (W r)
              (h3ClassicalizationFinOfAxis j) y).re)
          x)
      s := by
  dsimp only

  change
    ContinuousAt
      (fun r : ℝ =>
        ν *
            (∑ k : Fin 3,
              spatial3.d a
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                        hν U₀ hA hU₀ r
                        (h3ClassicalizationFinOfAxis j)))))
                x)
          -
        spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ r)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ r)
              (h3ClassicalizationFinOfAxis j) y).re)
          x)
      s

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_mixedDerivativeCandidate_continuousAt
      hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)
      x a

end

end Euclidean
end Bridge
end PrimeTensor
