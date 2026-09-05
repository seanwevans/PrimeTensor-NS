import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Frontier

/-!
# Classicalization: selected real velocity third-jet continuity

`CubicThirdJetContinuity` closes the analytic part of the time-regularity
problem one scalar spectral coordinate at a time.  This file packages those
three scalar coordinates into an honest PrimeTensor real velocity field.

There are two small representation steps.

* The spectral solver uses `Fin 3`.
* PrimeTensor vectors use `Axis Depth.three`.

We define the inverse coordinate map explicitly and prove that it is a left
inverse to the already-established `h3AxisOfFin3` map.  The selected real
velocity is then the tensor whose `j`th component is the real inverse-Fourier
representative of spectral coordinate `h3ClassicalizationFinOfAxis j`.

The scalar `ContinuousAt` theorem consequently becomes
`RealVelocityThirdJetContinuousAt` componentwise, and quantifying over the
open restart interval gives `RealVelocityThirdJetContinuousOn`.

This checkpoint is restart-relative.  It also proves decoder matching at
restart origin `t = 0`.  A later gluing layer can translate the field by the
old terminal time and combine it with the preterminal classical solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedVelocityThirdJetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Convert one intrinsic three-dimensional project axis back to the
corresponding spectral `Fin 3` coordinate. -/
def h3ClassicalizationFinOfAxis :
    PrimeTensor.Axis Depth.three → Fin 3
  | .first => 0
  | .next .first => 1
  | .next (.next .first) => 2

/-- The explicit axis-to-`Fin 3` map is inverse to the project-wide
`h3AxisOfFin3` decoder on the three spectral coordinates. -/
@[simp]
theorem h3ClassicalizationFinOfAxis_h3AxisOfFin3
    (i : Fin 3) :
    h3ClassicalizationFinOfAxis (h3AxisOfFin3 i) = i := by
  fin_cases i <;>
    rfl

/-- Package an arbitrary three-coordinate spectral path as a real
PrimeTensor spacetime velocity field. -/
noncomputable def h3SpectralRealVelocityOfPath
    (W : ℝ → H3SpectralFinVectorState) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  fun s x =>
    ⟨fun j =>
      h3SpectralVelocityRealC1RepresentativeOnPoint3
        (W s)
        (h3ClassicalizationFinOfAxis j)
        x⟩

@[simp]
theorem h3SpectralRealVelocityOfPath_component
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    (h3SpectralRealVelocityOfPath W s x).component j
      =
    h3SpectralVelocityRealC1RepresentativeOnPoint3
      (W s)
      (h3ClassicalizationFinOfAxis j)
      x := by
  rfl

/-- The packaged velocity decodes the original `Fin 3` spectral coordinate
when its component is requested through `h3AxisOfFin3`. -/
@[simp]
theorem h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (x : Point3)
    (i : Fin 3) :
    (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i)
      =
    h3SpectralVelocityRealC1RepresentativeOnPoint3
      (W s)
      i
      x := by
  rw [
    h3SpectralRealVelocityOfPath_component,
    h3ClassicalizationFinOfAxis_h3AxisOfFin3
  ]

/-- The selected restart-radius spectral path, reconstructed as an ordinary
real velocity field in restart-relative time. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  h3SpectralRealVelocityOfPath
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀)

/-- At every strict positive interior restart time, the selected reconstructed
velocity has a time-continuous ordered third spatial jet at every point. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_thirdJetContinuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (x : Point3) :
    RealVelocityThirdJetContinuousAt
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hA hU₀)
      s
      x := by
  intro a b c j

  change
    ContinuousAt
      (fun r : ℝ =>
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r
                  (h3ClassicalizationFinOfAxis j)))))
          x)
      s

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdPartial_continuousAt
      hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)
      x a b c

/-- The restart-relative selected real velocity has a continuous ordered third
spatial jet throughout the whole open restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_thirdJetContinuousOn
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    RealVelocityThirdJetContinuousOn
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hA hU₀)
      (h3FinHeatLerayRestartRadius ν A) := by
  intro s hs x

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_thirdJetContinuousAt
      hν U₀ hA hU₀
      hs.1 hs.2
      x

/-- At restart origin zero, the packaged real velocity is exactly the decoder
required by the classicalization frontier on the whole selected restart
interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_decoderMatches_zero
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    H3SpectralRestartDecoderMatches
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hA hU₀)
      0
      (h3FinHeatLerayRestartRadius ν A) := by
  intro s i

  have hAE :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (s := (s : ℝ))
      hν U₀ hA hU₀ i

  filter_upwards [hAE] with x hx

  change
    h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          i)
        x
      =
    (h3SpectralRealVelocityOfPath
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        (0 + (s : ℝ))
        x).component
      (h3AxisOfFin3 i)

  rw [
    zero_add,
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
  ]

  exact hx.symm

end
end Euclidean
end Bridge
end PrimeTensor
