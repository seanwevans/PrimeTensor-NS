import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Temporal.PDE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Temporal.Derivative.Regularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Strict-positive FTC for the canonical selected restart

The selected restart now has two independent ingredients already proved by the
classicalization stack:

* global continuity of each reconstructed real velocity coordinate;
* ordinary temporal `C¹` regularity on the strict relative restart interval
  `(0,R)`.

This file combines them into the scalar FTC on every compact subinterval

    0 < a ≤ b < R.

For one coordinate and physical point,

    ∫ₐᵇ ∂ₜ S_i(s,x) ds
      =
    S_i(b,x) - S_i(a,x).

The lower endpoint is deliberately kept strictly positive.  This avoids
manufacturing pointwise second-derivative control at restart time zero.  The
weak/Hilbert layer can later pass `a ↓ 0`, where both the selected velocity and
the projected physical `L²` RHS are already canonically defined.

No old-branch temporal regularity or endpoint continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology
  InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedPointwiseFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar FTC for one canonical selected real velocity coordinate on a strict
positive compact subinterval of the restart radius. -/
theorem h3PreterminalSelectedUnitRealVelocity_intervalIntegral_temporalDerivative_between
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ha0 : 0 < a)
    (hab : a ≤ b)
    (hbR :
      b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∫ s in a..b,
      temporal.d
        (fun r : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i) x)
        s)
      =
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (W b i) x
      -
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (W a i) x := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let f : ℝ → ℝ :=
    fun s : ℝ =>
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W s i) x

  let G : ℝ → ℝ :=
    fun s : ℝ =>
      temporal.d f s

  have hRegularity0 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      x
      (h3AxisOfFin3 i)

  have hRegularity :
      DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) R)
        ∧
      ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) R) := by
    simpa only [
      f,
      W,
      R,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3PreterminalTailCanonicalSelectedRestart,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3
    ] using hRegularity0

  have hSub :
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) R := by
    intro s hs
    constructor
    · exact lt_of_lt_of_le ha0 hs.1
    · exact lt_of_le_of_lt hs.2 hbR

  have hFContinuous :
      ContinuousOn f (Set.Icc a b) := by
    exact
      hRegularity.1.continuousOn.mono hSub

  have hGContinuous :
      ContinuousOn G (Set.Icc a b) := by
    change
      ContinuousOn
        (deriv f)
        (Set.Icc a b)
    exact hRegularity.2.mono hSub

  have hGIntegrable :
      IntervalIntegrable G volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hGContinuous

  have hFDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo a b →
        HasDerivAt f (G s) s := by
    intro s hs

    have hsClosed :
        s ∈ Set.Icc a b :=
      ⟨hs.1.le, hs.2.le⟩

    have hsOpen :
        s ∈ Set.Ioo (0 : ℝ) R :=
      hSub hsClosed

    have hDiffWithin :
        DifferentiableWithinAt
          ℝ f (Set.Ioo (0 : ℝ) R) s :=
      hRegularity.1 s hsOpen

    have hDiff :
        DifferentiableAt ℝ f s :=
      hDiffWithin.differentiableAt
        (isOpen_Ioo.mem_nhds hsOpen)

    change
      HasDerivAt f (deriv f s) s

    exact hDiff.hasDerivAt

  have hFTC :
      (∫ s in a..b, G s)
        =
      f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab
      hFContinuous
      hFDeriv
      hGIntegrable

  simpa only [G, f, W] using hFTC

end

end Euclidean
end Bridge
end PrimeTensor
