import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Raw.Forcing.Physical.L2.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force

/-!
# Zero-order physical L² selected pressure force

The two terms in the exact selected pressure-force identity are now both in
physical `L²`:

    -∂ᵢp = rawᵢ - lerayᵢ.

The raw term is supplied by `H3PathSelectedRawForcingPhysicalL2Zero`; the
projected term was already reconstructed in
`H3PathSelectedForcingPhysicalL2Zero`.  Hence the selected pressure force is
`L²` by subtraction, and the actual first pressure derivative is `L²` by
negation.

No new estimate is used here.  This is only the exact pressure identity plus
closure of `MemLp` under subtraction and negation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPressurePhysicalL2Zero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedPressurePhysicalL2Zero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For any spectral path, each canonical pressure-force coordinate is in
physical `L²` whenever evaluated through the existing raw/Leray reconstruction.
At order zero those two inputs are already available for arbitrary H³ states. -/
theorem h3RawFinPressureRealC1OfPath_pressureForceComponent_memLp2
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (i : Fin 3) :
    MemLp
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x
          (h3AxisOfFin3 i))
      2
      (volume : Measure Point3) := by

  have hRaw :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              (W s) (W s) i)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re)
        2
        (volume : Measure Point3) :=
    h3RawFinOuterProductDivergence_fourierInvOnPoint3_real_memLp2
      (W s) (W s) i

  have hLeray :
      MemLp
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W s) (W s) i x).re)
        2
        (volume : Measure Point3) :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_real_memLp2
      (W s) (W s) i

  have hSubAlg :
      MemLp
        ((fun x : Point3 =>
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              (W s) (W s) i)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re)
          -
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W s) (W s) i x).re))
        2
        (volume : Measure Point3) :=
    hRaw.sub hLeray

  have hSubAE :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W s) (W s) i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re
          -
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i x).re)
        =ᵐ[(volume : Measure Point3)]
      ((fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W s) (W s) i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re)
        -
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i x).re)) := by
    filter_upwards with x
    rfl

  have hSub :
      MemLp
        (fun x : Point3 =>
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence
              (W s) (W s) i)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)).re
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W s) (W s) i x).re)
        2
        (volume : Measure Point3) := by
    exact (memLp_congr_ae hSubAE).2 hSubAlg

  have hEq :
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x
          (h3AxisOfFin3 i))
        =
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W s) (W s) i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re
          -
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i x).re) := by
    funext x
    exact
      h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
        W s i x

  rw [hEq]
  exact hSub

/-- Axis-indexed form of the zero-order selected pressure-force `L²` theorem. -/
theorem h3RawFinPressureRealC1OfPath_pressureForceComponent_axis_memLp2
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    MemLp
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x j)
      2
      (volume : Measure Point3) := by

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have h :=
    h3RawFinPressureRealC1OfPath_pressureForceComponent_memLp2
      W s i

  simpa only [
    i,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis
  ] using h

/-- The actual first pressure derivative, rather than its negative force form,
is in physical `L²`. -/
theorem h3RawFinPressureRealC1OfPath_spatialDerivative_memLp2
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d
        j
        ((h3RawFinPressureRealC1OfPath W) s))
      2
      (volume : Measure Point3) := by

  have hForce :=
    h3RawFinPressureRealC1OfPath_pressureForceComponent_axis_memLp2
      W s j

  have hNegAlg :
      MemLp
        (-(fun x : Point3 =>
          PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath W)
            s x j))
        2
        (volume : Measure Point3) :=
    hForce.neg

  have hNegAE :
      (fun x : Point3 =>
        - PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath W)
            s x j)
        =ᵐ[(volume : Measure Point3)]
      (-(fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x j)) := by
    filter_upwards with x
    rfl

  have hNeg :
      MemLp
        (fun x : Point3 =>
          - PrimeTensor.Bridge.RealFluid.pressureForceComponent
              spatial3
              (h3RawFinPressureRealC1OfPath W)
              s x j)
        2
        (volume : Measure Point3) := by
    exact (memLp_congr_ae hNegAE).2 hNegAlg

  have hEq :
      spatial3.d
          j
          ((h3RawFinPressureRealC1OfPath W) s)
        =
      (fun x : Point3 =>
        - PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath W)
            s x j) := by
    funext x
    unfold PrimeTensor.Bridge.RealFluid.pressureForceComponent
    ring

  rw [hEq]
  exact hNeg

/-- Selected-restart specialization of the zero-order pressure-force `L²`
closure. -/
theorem h3SelectedRestartPressureForce_memLp2
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          (h3RawFinPressureRealC1OfPath W)
          s x j)
      2
      (volume : Measure Point3) := by
  dsimp only
  exact
    h3RawFinPressureRealC1OfPath_pressureForceComponent_axis_memLp2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      s j

/-- Selected-restart specialization in the exact pressure-derivative form used
by the H³ energy split. -/
theorem h3SelectedRestartPressureSpatialDerivative_memLp2
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d
        j
        ((h3RawFinPressureRealC1OfPath W) s))
      2
      (volume : Measure Point3) := by
  dsimp only
  exact
    h3RawFinPressureRealC1OfPath_spatialDerivative_memLp2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      s j

end

end Euclidean
end Bridge
end PrimeTensor
