import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealMixedDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealTemporalDerivativeRegularity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Classicalization: selected real mixed derivative in absolute time

The selected restart is naturally parameterized by elapsed time `r ∈ (0,R)`,
whereas the continuation/gluing frontier uses absolute time

    τ ↦ selectedVelocity (τ - t₀).

The restart-relative mixed derivative theorem is already closed.  This file
transports it through the affine time translation `τ ↦ τ - t₀`.

There are two chain-rule uses.

* The relative mixed `HasDerivAt` is composed with the translation, whose
  derivative is one.
* For each fixed spatial point, temporal differentiability of the selected real
  component identifies the absolute-time `temporal.d` with the same
  restart-relative derivative at `s - t₀`.

Thus the resulting coefficient is exactly the absolute-time mixed field
required by the continuation reduction.  No new estimate, PDE identity, or
mixed-partial argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealMixedDerivativeAbsoluteTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Absolute-time form of the selected real mixed derivative theorem.

If `s` lies in the translated restart interval `(t₀,t₀+R)`, then the path
`τ ↦ ∂ₐ u(τ-t₀,x)` has derivative equal to the concrete spatial partial of its
absolute-time temporal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime
    {ν A t₀ s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs :
      s ∈ Set.Ioo
        t₀
        (t₀ + h3FinHeatLerayRestartRadius ν A))
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun τ : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              (τ - t₀)
              y).component j)
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun τ : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hν U₀ hA hU₀
                (τ - t₀)
                y).component j)
            s)
        x)
      s := by
  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let q : ℝ :=
    s - t₀

  have hq0 : 0 < q := by
    dsimp only [q]
    exact sub_pos.mpr hs.1

  have hqR : q < R := by
    dsimp only [q, R]
    linarith [hs.2]

  have hRelative :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_time
      hν U₀ hA hU₀
      hq0 hqR
      x a j

  have hShift :
      HasDerivAt
        (fun τ : ℝ => τ - t₀)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t₀

  have hAbsoluteRaw :
      HasDerivAt
        (fun τ : ℝ =>
          spatial3.d
            a
            (fun y : Point3 =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hν U₀ hA hU₀
                (τ - t₀)
                y).component j)
            x)
        (spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀
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
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s)
        =
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              r
              y).component j)
          q) := by
    funext y

    have hRegularity :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        hν U₀ hA hU₀ y j

    dsimp only at hRegularity

    have hqMem :
        q ∈ Set.Ioo
          0
          (h3FinHeatLerayRestartRadius ν A) := by
      exact ⟨hq0, by simpa only [R] using hqR⟩

    have hfDiff :
        DifferentiableAt ℝ
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              r
              y).component j)
          q := by
      exact
        (hRegularity.1 q hqMem).differentiableAt
          (isOpen_Ioo.mem_nhds hqMem)

    have hf :
        HasDerivAt
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              r
              y).component j)
          (deriv
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hν U₀ hA hU₀
                r
                y).component j)
            q)
          q :=
      hfDiff.hasDerivAt

    have hComp :=
      hf.comp s hShift

    change
      deriv
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s
        =
      deriv
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀
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
              (fun τ : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀
                  (τ - t₀)
                  y).component j)
              s)
          x
        =
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀
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
