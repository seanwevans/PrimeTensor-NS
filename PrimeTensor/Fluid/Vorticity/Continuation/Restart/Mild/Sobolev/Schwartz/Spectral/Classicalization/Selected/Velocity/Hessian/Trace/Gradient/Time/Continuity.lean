import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Third.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Spatial.Partial.Time.Continuity

/-!
# Classicalization: selected Hessian-trace gradient time continuity

The nonlinear forcing spatial partial is now time-continuous in exactly the
`spatial3.d` language used by the mixed-regularity frontier.

This file closes the matching linear term.  The selected real velocity already
has a time-continuous ordered third spatial jet.  Therefore, for any fixed
outer axis `a`, every diagonal third partial

    ∂ₐ ∂ⱼ ∂ⱼ uᵢ

is time-continuous.  Finite summation over the three spatial axes, followed by
multiplication by the fixed viscosity, preserves continuity.

No new estimate and no derivative-commutation theorem are used: the order is
kept exactly as `a, j, j`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityHessianTraceGradientTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For one selected scalar spectral coordinate, the spatial derivative of the
real Hessian trace is time-continuous at every strict positive interior restart
time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_hessianTraceGradient_continuousAt
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
    ContinuousAt
      (fun r : ℝ =>
        ∑ j : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ r i))))
            x)
      s := by
  have hTerm :
      ∀ j : Fin 3,
        ContinuousAt
          (fun r : ℝ =>
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ r i))))
              x)
          s := by
    intro j
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdPartial_continuousAt
        hν U₀ hA hU₀ hs hsR i x
        a
        (h3AxisOfFin3 j)
        (h3AxisOfFin3 j)

  change
    Tendsto
      (fun r : ℝ =>
        ∑ j : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ r i))))
            x)
      (𝓝 s)
      (𝓝
        (∑ j : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s i))))
            x))

  exact
    tendsto_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j _hj => hTerm j)

/-- Multiplication by the fixed viscosity preserves the preceding
Hessian-trace-gradient time continuity. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_viscosityHessianTraceGradient_continuousAt
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
    ContinuousAt
      (fun r : ℝ =>
        ν *
          (∑ j : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ r i))))
              x))
      s := by
  have hTrace :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_hessianTraceGradient_continuousAt
      hν U₀ hA hU₀ hs hsR i x a

  exact
    continuousAt_const.mul hTrace

/-- Velocity-component form of the viscosity-weighted Hessian-trace-gradient
continuity. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_viscosityHessianTraceGradient_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
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
              x))
      s := by
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
              x))
      s

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_viscosityHessianTraceGradient_continuousAt
      hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)
      x a

end

end Euclidean
end Bridge
end PrimeTensor
