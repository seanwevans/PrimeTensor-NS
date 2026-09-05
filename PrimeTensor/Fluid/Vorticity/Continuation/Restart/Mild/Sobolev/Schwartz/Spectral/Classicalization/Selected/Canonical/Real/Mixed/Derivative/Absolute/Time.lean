import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.Temporal.Derivative.Regularity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Classicalization: canonical real mixed derivative in absolute time

The canonical restart-radius velocity is naturally parameterized by elapsed time
`r ∈ (0,R)`, while the continuation and gluing frontier is written in absolute
time through

    τ ↦ h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity (τ - t₀).

The restart-relative canonical mixed derivative is already proved, and the
canonical real temporal-derivative regularity package is now available.  This
file transports the relative mixed derivative through the affine translation
`τ ↦ τ - t₀`.

There are only two chain-rule steps:

* compose the relative mixed `HasDerivAt` theorem with the translation, whose
  derivative is one;
* identify the temporal derivative of the translated real component with the
  same restart-relative derivative at `s - t₀`.

No new estimate, PDE identity, or mixed-partial argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealMixedDerivativeAbsoluteTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Absolute-time form of the canonical selected real mixed derivative theorem.

If `s` lies in the translated restart interval `(t₀,t₀+R)`, then the path
`τ ↦ ∂ₐ u(τ-t₀,x)` has derivative equal to the concrete spatial partial of its
absolute-time temporal derivative. -/
theorem h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime
    {nu A t0 s : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A)
    (hs :
      s ∈ Set.Ioo
        t0
        (t0 + h3FinHeatLerayRestartRadius nu A))
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun tau : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              (tau - t0)
              y).component j)
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun tau : ℝ =>
              (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                hnu U0 hA hU0
                (tau - t0)
                y).component j)
            s)
        x)
      s := by
  let R : ℝ :=
    h3FinHeatLerayRestartRadius nu A

  let q : ℝ :=
    s - t0

  have hq0 : 0 < q := by
    dsimp only [q]
    exact sub_pos.mpr hs.1

  have hqR : q < R := by
    dsimp only [q, R]
    linarith [hs.2]

  have hRelative :=
    h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_time
      hnu U0 hA hU0
      hq0 hqR
      x a j

  have hShift :
      HasDerivAt
        (fun tau : ℝ => tau - t0)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t0

  have hAbsoluteRaw :
      HasDerivAt
        (fun tau : ℝ =>
          spatial3.d
            a
            (fun y : Point3 =>
              (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                hnu U0 hA hU0
                (tau - t0)
                y).component j)
            x)
        (spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                  hnu U0 hA hU0
                  r
                  y).component j)
              q)
          x)
        s := by
    have hComp :=
      hRelative.comp s hShift

    simpa only [
      Function.comp_def,
      mul_one,
      q
    ] using hComp

  have hTemporalFieldEq :
      (fun y : Point3 =>
        temporal.d
          (fun tau : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              (tau - t0)
              y).component j)
          s)
        =
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              r
              y).component j)
          q) := by
    funext y

    have hRegularity :=
      h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        hnu U0 hA hU0 y j

    dsimp only at hRegularity

    have hqMem :
        q ∈ Set.Ioo
          0
          (h3FinHeatLerayRestartRadius nu A) := by
      exact ⟨hq0, by simpa only [R] using hqR⟩

    have hfDiff :
        DifferentiableAt ℝ
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              r
              y).component j)
          q := by
      exact
        (hRegularity.1 q hqMem).differentiableAt
          (isOpen_Ioo.mem_nhds hqMem)

    have hf :
        HasDerivAt
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              r
              y).component j)
          (deriv
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                hnu U0 hA hU0
                r
                y).component j)
            q)
          q :=
      hfDiff.hasDerivAt

    have hComp :=
      hf.comp s hShift

    change
      deriv
          (fun tau : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              (tau - t0)
              y).component j)
          s
        =
      deriv
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              r
              y).component j)
          q

    simpa only [
      Function.comp_def,
      mul_one,
      q
    ] using hComp.deriv

  have hCoefficientEq :
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun tau : ℝ =>
                (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                  hnu U0 hA hU0
                  (tau - t0)
                  y).component j)
              s)
          x
        =
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                  hnu U0 hA hU0
                  r
                  y).component j)
              q)
          x :=
    congrArg
      (fun f : ScalarField3 => spatial3.d a f x)
      hTemporalFieldEq

  exact
    hAbsoluteRaw.congr_deriv hCoefficientEq.symm

end

end Euclidean
end Bridge
end PrimeTensor
