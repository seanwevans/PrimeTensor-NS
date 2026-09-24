import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge

/-!
# Zero-order physical L² reconstruction for the raw selected forcing

The projected Leray forcing is already available in physical `L²`.  The
unprojected raw outer-product divergence enjoys the same Fourier `L²`
property before projection, for arbitrary H³ spectral states.

This file transports that raw Fourier field through the unitary inverse
Fourier transform and the volume-preserving `Point3` identification, then
takes real parts.  No positive-time smoothing or new moment estimate is
required at derivative order zero.

Together with `H3PathSelectedForcingPhysicalL2Jet`, this supplies both terms
in the pressure-force identity

    -∇p = raw advection - Leray-projected advection

at zero spatial derivative order.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingPhysicalL2Zero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedRawForcingPhysicalL2Zero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Ordinary inverse Fourier reconstruction of an integrable Fourier `L²`
field remains `L²` after pulling back to `Point3`. -/
private theorem memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawForcingZero
    {f : H3FourierPoint3 → ℂ}
    (hf1 :
      Integrable
        f
        (volume : Measure H3FourierPoint3))
    (hf2 :
      MemLp
        f
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by

  let f2 : H3FourierComplexL2 :=
    hf2.toLp f

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let p2 :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three))
      u2

  have hCompat :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hf1 hf2

  have hComp :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hFrom :
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    dsimp only [p2]
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        u2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ) :=
    hComp.trans hFrom.symm

  have hp2 :
      MemLp
        ((p2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp p2

  exact
    (memLp_congr_ae hAE).2 hp2

/-- Taking real parts preserves physical `L²`. -/
private theorem memLp_re_of_memLp_complex_h3SelectedRawForcingZero
    {f : Point3 → ℂ}
    (hf :
      MemLp
        f
        2
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => (f x).re)
      2
      (volume : Measure Point3) := by

  let F :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    hf.toLp f

  let R :
      MeasureTheory.Lp
        ℝ
        2
        (volume : Measure Point3) :=
    Complex.reCLM.compLp F

  have hF :
      ((F :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      f := by
    dsimp only [F]
    exact MeasureTheory.MemLp.coeFn_toLp hf

  have hR :
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re) := by
    dsimp only [R]
    exact Complex.reCLM.coeFn_compLp F

  have hAE :
      (fun x : Point3 => (f x).re)
        =ᵐ[(volume : Measure Point3)]
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ) := by
    filter_upwards [hF, hR] with x hxF hxR
    calc
      (f x).re
          =
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re :=
        congrArg Complex.re hxF.symm
      _ =
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ) x :=
        hxR.symm

  have hRMem :
      MemLp
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp R

  exact (memLp_congr_ae hAE).2 hRMem

/-- Every raw finite outer-product divergence coordinate has an ordinary
inverse-Fourier reconstruction in physical complex `L²` on `Point3`. -/
theorem h3RawFinOuterProductDivergence_fourierInvOnPoint3_memLp2
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    MemLp
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence U V i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by
  exact
    memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedRawForcingZero
      (h3RawFinOuterProductDivergence_integrable U V i)
      (h3RawFinOuterProductDivergence_memLp2 U V i)

/-- Real physical raw forcing is `L²` as well. -/
theorem h3RawFinOuterProductDivergence_fourierInvOnPoint3_real_memLp2
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    MemLp
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence U V i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re)
      2
      (volume : Measure Point3) := by
  exact
    memLp_re_of_memLp_complex_h3SelectedRawForcingZero
      (h3RawFinOuterProductDivergence_fourierInvOnPoint3_memLp2
        U V i)

/-- Selected-restart specialization of the real raw forcing `L²` statement.
Unlike the differentiated versions, the zero-order claim requires no positive
restart time. -/
theorem h3SelectedRestartRealRawForcing_memLp2
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W s) (W s) i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re)
      2
      (volume : Measure Point3) := by
  dsimp only
  exact
    h3RawFinOuterProductDivergence_fourierInvOnPoint3_real_memLp2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      i

end

end Euclidean
end Bridge
end PrimeTensor
