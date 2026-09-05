import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Temporal.Derivative.PDE.Form

/-!
# Classicalization: time continuity of the selected spatial-temporal derivative

The preceding increment identifies, at every strict positive interior restart
time, the actual spatial partial of the actual temporal derivative with the
PDE mixed-derivative candidate

    ν * Σₖ ∂ₐ∂ₖ∂ₖ uᵢ - ∂ₐ Re Nᵢ(u,u).

That candidate was already proved time-continuous.

Because the pointwise identification is available only on the open restart
interval, this file performs the transfer locally: `Ioo 0 R` is a
neighborhood of every strict positive interior time `s`, so the actual mixed
field and the candidate are eventually equal in `𝓝 s`.  Continuity then
transports through `ContinuousAt.congr_of_eventuallyEq`.

No new estimate, regularity hypothesis, or derivative commutation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocitySpatialTemporalDerivativeTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar-coordinate form: the actual spatial derivative of the actual
temporal derivative is time-continuous at every strict positive interior
restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_temporal_d_continuousAt
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
        spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W q i) y)
              r)
          x)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let actual : ℝ → ℝ :=
    fun r : ℝ =>
      spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) y)
            r)
        x

  let candidate : ℝ → ℝ :=
    fun r : ℝ =>
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
        x

  have hCandidate :
      ContinuousAt candidate s := by
    dsimp only [candidate, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_mixedDerivativeCandidate_continuousAt
        hν U₀ hA hU₀ hs hsR i x a

  have hInterior :
      Set.Ioo
          0
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    IsOpen.mem_nhds isOpen_Ioo ⟨hs, hsR⟩

  have hEq :
      actual =ᶠ[𝓝 s] candidate := by
    filter_upwards [hInterior] with r hr
    dsimp only [actual, candidate, W]
    exact
      spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
        hν U₀ hA hU₀ hr.1 hr.2 i x a

  change ContinuousAt actual s
  exact hCandidate.congr_of_eventuallyEq hEq

/-- Velocity-component form of the same time continuity statement. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatial_d_temporal_d_continuousAt
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
        spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ q y).component j)
              r)
          x)
      s := by
  change
    ContinuousAt
      (fun r : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ q
                    (h3ClassicalizationFinOfAxis j))
                  y)
              r)
          x)
      s

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_temporal_d_continuousAt
      hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)
      x a

end

end Euclidean
end Bridge
end PrimeTensor
