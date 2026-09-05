import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pressure.Absolute.Time
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Temporal.Derivative.Regularity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Selected H³ pressure momentum in absolute continuation time

`SelectedPressureMomentum` proves the physical momentum equation in the restart
clock `r ∈ (0,R)`.  The continuation glue is written in absolute time `s`, with

    r = s - t.

This file translates the complete momentum identity through that affine time
change.  Every spatial term is pointwise and therefore changes only by
substitution.  The single nontrivial bookkeeping step is the temporal
derivative:

    d/ds u(s-t) = d/dr u(r) |_{r=s-t},

because the shift `s ↦ s-t` has derivative one.

The resulting theorem is stated for the shifted spectral path itself.  This is
the exact selected-side identity needed before transporting momentum through the
old/selected overlap glue.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureMomentumAbsoluteTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical selected spectral restart written in absolute time. -/
noncomputable def h3PreterminalTailCanonicalSelectedRestartAbsolute
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ℝ → H3SpectralFinVectorState :=
  fun s =>
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      (s - t)

/-- The selected physical momentum identity in the absolute continuation clock,
still written in the exact finite-coordinate Laplacian form of the relative
selected theorem. -/
theorem h3PreterminalTailCanonicalSelectedRestartAbsolute_pressure_momentum_fin
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    temporal.d
        (fun τ : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W (τ - t) i) x)
        s
      +
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      (s - t) x).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalSelectedPressureAbsolute
          hNS ht hE hTail)
        s x
        (h3AxisOfFin3 i)
      +
    (∑ j : Fin 3,
      spatial3.d
        (h3AxisOfFin3 j)
        (spatial3.d
          (h3AxisOfFin3 j)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W (s - t) i)))
        x) := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let r : ℝ := s - t

  have hr0 : 0 < r := by
    dsimp only [r]
    exact sub_pos.mpr hs.1

  have hrR :
      r < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [r]
    exact
      (sub_lt_iff_lt_add).2
        (by simpa only [add_comm] using hs.2)

  have hrMem :
      r ∈ Set.Ioo
        0
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨hr0, hrR⟩

  let f : ℝ → ℝ :=
    fun q : ℝ =>
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W q i) x

  have hRegularity :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      x
      (h3AxisOfFin3 i)

  have hDiffNamed :
      DifferentiableAt ℝ
        (fun q : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
            q x).component
              (h3AxisOfFin3 i))
        r := by
    exact
      (hRegularity.1 r hrMem).differentiableAt
        (isOpen_Ioo.mem_nhds hrMem)

  have hDiff :
      DifferentiableAt ℝ f r := by
    dsimp only [f, W, U₀]
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3PreterminalTailCanonicalSelectedRestart,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3
    ] using hDiffNamed

  have hf :
      HasDerivAt f (deriv f r) r :=
    hDiff.hasDerivAt

  have hShift :
      HasDerivAt
        (fun τ : ℝ => τ - t)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t

  have hComp :=
    hf.comp s hShift

  have hTemporal :
      temporal.d
          (fun τ : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W (τ - t) i) x)
          s
        =
      temporal.d f r := by
    change
      deriv
          (fun τ : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W (τ - t) i) x)
          s
        =
      deriv f r

    have hDeriv := hComp.deriv

    simpa only [
      Function.comp_def,
      f,
      r,
      mul_one
    ] using hDeriv

  have hRelative :=
    h3PreterminalTailCanonicalSelectedRestart_pressure_momentum_fin
      (ν := (1 : ℝ))
      (E := E)
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hr0 hrR i x

  rw [hTemporal]

  simpa only [
    f,
    W,
    r,
    h3PreterminalTailCanonicalSelectedPressureAbsolute,
    PrimeTensor.Bridge.RealFluid.pressureForceComponent,
    one_mul
  ] using hRelative

end

end Euclidean
end Bridge
end PrimeTensor
