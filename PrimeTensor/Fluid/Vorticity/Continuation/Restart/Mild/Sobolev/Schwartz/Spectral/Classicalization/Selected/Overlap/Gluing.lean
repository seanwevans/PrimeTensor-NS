import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder

/-!
# Classicalization: selected overlap gluing

The selected restart is launched at an interior preterminal time `t < T`.
Therefore the canonical restart window generally overlaps the already-existing
classical solution on `[t,T)`.

Two requirements from the classicalization frontier are simultaneously active
on that overlap.

* `RealRestartAgreesBeforeT` requires the eventual total real field to equal
  the old logged velocity at every absolute time below `T`.
* `H3SpectralRestartDecoderMatches` requires the same field, at absolute time
  `t + q`, to realize the canonical real decoder of the selected spectral
  restart state `W q`.

Thus a piecewise definition by itself cannot avoid uniqueness: on the overlap
the old solution and the selected restart must represent the same state.

This file isolates that remaining uniqueness obligation as one exact a.e.
decoder predicate and removes all gluing bookkeeping around it.

The glued field is

    old logged velocity,       s < T
    selected restart velocity, T ≤ s,

with selected time measured from the restart anchor `t`.

Assuming decoder agreement only on the genuine overlap, the glued field:

1. automatically satisfies `RealRestartAgreesBeforeT`;
2. automatically matches the selected spectral decoder on the *entire*
   canonical restart interval.

Outside the overlap the second statement uses the already-compiled exact
decoder theorem for the selected real velocity.  The next analytic increment
can therefore focus exclusively on proving the overlap predicate from
Navier--Stokes uniqueness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedOverlapGluing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The exact remaining overlap statement.

At every selected restart time `q` whose absolute time `t + q` is still before
the old terminal time `T`, the canonical real `L²` decoder of the selected
spectral state agrees almost everywhere with the old logged velocity.

This is intentionally stated in the same a.e. representation language as
`H3SpectralRestartDecoderMatches`; no unnecessary pointwise upgrade is built
into the uniqueness target. -/
def H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
    (W : ℝ → H3SpectralVelocityState)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t T R : ℝ) : Prop :=
  ∀ (q : Set.Icc (0 : ℝ) R) (j : Fin 3),
    t + (q : ℝ) < T →
      ∀ᵐ x : Point3 ∂volume,
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2
              (W (q : ℝ)) j)
            x
          =
        (PrimeTensor.Bridge.logSpaceTimeVectorField
            u
            (t + (q : ℝ))
            x).component
          (h3AxisOfFin3 j)

/-- Glue the old logged preterminal velocity to the selected real restart.

The branch point is the old terminal time `T`, while the selected branch is
evaluated at elapsed restart time `s - t`. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
    {ν A t T : ℝ}
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  fun s x =>
    if hs : s < T then
      PrimeTensor.Bridge.logSpaceTimeVectorField u s x
    else
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hA hU₀
        (s - t)
        x

/-- The overlap glue agrees exactly with the original logged preterminal
velocity at every time in `(0,T)`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedOverlapGlue_agreesBeforeT
    {ν A t T : ℝ}
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    RealRestartAgreesBeforeT
      u
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
        (t := t) (T := T)
        hν u U₀ hA hU₀)
      T := by
  intro s hs

  funext x

  simp only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue,
    dif_pos hs.2
  ]

/-- Assuming uniqueness only on the true overlap, the glued real field matches
the selected spectral decoder throughout the full canonical restart window.

Before `T` this is exactly the overlap hypothesis.  At and after `T`, the
field is definitionally the selected real restart shifted from relative time
`q` to absolute time `t + q`, and the selected decoder theorem closes the
branch. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedOverlapGlue_decoderMatches
    {ν A t T : ℝ}
    (hν : 0 < ν)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hOverlap :
      H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        u
        t
        T
        (h3FinHeatLerayRestartRadius ν A)) :
    H3SpectralRestartDecoderMatches
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
        (t := t) (T := T)
        hν u U₀ hA hU₀)
      t
      (h3FinHeatLerayRestartRadius ν A) := by
  intro q j

  by_cases hBefore : t + (q : ℝ) < T

  · have hAE :=
      hOverlap q j hBefore

    filter_upwards [hAE] with x hx

    change
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (q : ℝ))
            j)
          x
        =
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
        (t := t) (T := T)
        hν u U₀ hA hU₀
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 j)

    rw [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue,
      dif_pos hBefore
    ]

    exact hx

  · have hSelected :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_decoderMatches_zero
        hν U₀ hA hU₀
        q j

    have hShift :
        t + (q : ℝ) - t = (q : ℝ) := by
      ring

    filter_upwards [hSelected] with x hx

    change
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (q : ℝ))
            j)
          x
        =
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
        (t := t) (T := T)
        hν u U₀ hA hU₀
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 j)

    rw [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue,
      dif_neg hBefore,
      hShift
    ]

    simpa using hx

end
end Euclidean
end Bridge
end PrimeTensor
