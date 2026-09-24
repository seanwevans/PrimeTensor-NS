import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge

/-!
# Zero-order physical L² reconstruction for selected Leray forcing

The pressure branch will use the exact selected identity

    -∇p = advection - Leray(advection).

The transport term is now closed in physical `L²`.  On the projected side the
repository already packages the raw Leray forcing as Fourier `L²` and proves
that its ordinary continuous inverse-Fourier representative agrees almost
everywhere with the canonical unitary `L²` reconstruction.

This file transports that reconstruction through the `WithLp` identification
onto `Point3` and then takes real parts.  It is the zero-order base case for the
next differentiated-forcing `L²` bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingPhysicalL2Zero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedForcingPhysicalL2Zero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pulling an arbitrary Fourier-carrier complex `L²` class back to `Point3`
through the canonical volume-preserving `WithLp.toLp` map preserves `L²`.
-/
private theorem memLp_point3_pullback_h3FourierComplexL2
    (F : H3FourierComplexL2) :
    MemLp
      (fun x : Point3 =>
        ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by

  let P :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three))
      F

  have hP :
      ((P :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    dsimp only [P]
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        F
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hPMem :
      MemLp
        ((P :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp P

  exact
    (memLp_congr_ae hP.symm).2 hPMem

/-- Real projection preserves physical `L²` on `Point3`. -/
private theorem memLp_re_of_memLp_complex_h3SelectedForcingZero
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

/-- The ordinary continuous physical reconstruction of every raw finite Leray
forcing coordinate belongs to complex physical `L²` on `Point3`. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_memLp2
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    MemLp
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U V i)
      2
      (volume : Measure Point3) := by

  let F : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergencePhysicalL2 U V i

  have hPull :
      MemLp
        (fun x : Point3 =>
          ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        2
        (volume : Measure Point3) :=
    memLp_point3_pullback_h3FourierComplexL2 F

  have hAE :
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3 U V i
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_ae_eq_physicalL2
        U V i

  exact (memLp_congr_ae hAE).2 hPull

/-- The real selected physical Leray forcing coordinate is therefore in
physical `L²` at zero spatial derivative order. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_real_memLp2
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    MemLp
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U V i x).re)
      2
      (volume : Measure Point3) := by
  exact
    memLp_re_of_memLp_complex_h3SelectedForcingZero
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_memLp2
        U V i)

/-- Positive-time selected-restart specialization of the zero-order physical
Leray forcing `L²` statement. -/
theorem h3SelectedRestartRealLerayForcing_memLp2
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
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W s) (W s) i x).re)
      2
      (volume : Measure Point3) := by
  dsimp only
  exact
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_real_memLp2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      i

end

end Euclidean
end Bridge
end PrimeTensor
