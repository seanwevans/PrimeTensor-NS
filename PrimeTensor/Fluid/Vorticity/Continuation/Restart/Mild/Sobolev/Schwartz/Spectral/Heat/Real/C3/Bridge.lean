import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.Compatibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Positive-time real C³ heat reconstruction on the project carrier

The classical/L² compatibility theorem identifies the complex ordinary
inverse-Fourier reconstruction of a positive-time heat-smoothed H³ spectral
state with the existing complex L² decoder almost everywhere.

This file takes the real part of that representative, transports it from the
Euclidean Fourier carrier back to the project's `Point3` carrier, and lifts the
result coordinatewise to three-component velocity data.

Thus positive heat time now supplies an actual real spatial `C³`
representative on `Point3` whose a.e. class is exactly the real decoder already
used by the restart stack.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatRealC3Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzHeatRealC3Bridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Real C³ representative on the Euclidean carrier -/

/-- Real part of the positive-time classical inverse-Fourier representative. -/
noncomputable def h3SpectralScalarHeatRealC3Representative
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    H3FourierPoint3 → ℝ :=
  fun x => (h3SpectralScalarHeatC3Representative ν t G x).re

/-- The real positive-time representative is spatially `C³`. -/
theorem h3SpectralScalarHeatRealC3Representative_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 3
      (h3SpectralScalarHeatRealC3Representative ν t G) := by
  unfold h3SpectralScalarHeatRealC3Representative
  simpa [Function.comp_def] using
    (h3SpectralScalarHeatC3Representative_contDiff_three hν ht G).continuousLinearMap_comp
      Complex.reCLM

/-- The real `C³` representative agrees almost everywhere with the existing
real `L²` decoder of the same heat-evolved spectral state. -/
theorem h3SpectralScalarHeatRealC3Representative_ae_eq_decodeRealL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatRealC3Representative ν t G
      =ᵐ[volume]
    ((h3SpectralScalarDecodeRealL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) G) :
      H3RealPhysicalScalarL2) : H3FourierPoint3 → ℝ) := by
  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN ν hν.le (NNReal.mk t ht.le) G

  have hComplex :
      h3SpectralScalarHeatC3Representative ν t G
        =ᵐ[volume]
      ((h3SpectralScalarDecodeComplexL2 H : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp [H]
    exact
      h3SpectralScalarHeatC3Representative_ae_eq_decodeComplexL2
        hν ht G

  have hRealPart :
      ((h3SpectralScalarDecodeRealL2 H : H3RealPhysicalScalarL2) :
          H3FourierPoint3 → ℝ)
        =ᵐ[volume]
      (fun x : H3FourierPoint3 =>
        ((h3SpectralScalarDecodeComplexL2 H : H3ComplexPhysicalScalarL2) x).re) := by
    unfold h3SpectralScalarDecodeRealL2 h3RealPartFourierL2
    exact
      Complex.reCLM.coeFn_compLp
        (h3SpectralScalarDecodeComplexL2 H)

  unfold h3SpectralScalarHeatRealC3Representative
  change
    (fun x : H3FourierPoint3 =>
      (h3SpectralScalarHeatC3Representative ν t G x).re)
      =ᵐ[volume]
    ((h3SpectralScalarDecodeRealL2 H : H3RealPhysicalScalarL2) :
      H3FourierPoint3 → ℝ)

  filter_upwards [hComplex, hRealPart] with x hx hRe
  rw [hRe]
  simpa using congrArg Complex.re hx

/-! ## Calculus transport back to `Point3` -/

/-- Real positive-time `C³` representative on the project's spatial carrier.

The carrier change is the canonical `WithLp.toLp` coordinate identity.  Using
this map directly is important: it is exactly the same volume-preserving map
used by `h3FromFourierRealL2`, while Mathlib separately proves that it is
smooth between the two equivalent finite-dimensional normed-space structures.
-/
noncomputable def h3SpectralScalarHeatRealC3RepresentativeOnPoint3
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    Point3 → ℝ :=
  fun x =>
    h3SpectralScalarHeatRealC3Representative ν t G
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- Transport to `Point3` preserves spatial `C³` regularity. -/
theorem h3SpectralScalarHeatRealC3RepresentativeOnPoint3_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ContDiff ℝ 3
      (h3SpectralScalarHeatRealC3RepresentativeOnPoint3 ν t G) := by
  have hToLp :
      ContDiff ℝ 3
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp
  unfold h3SpectralScalarHeatRealC3RepresentativeOnPoint3
  exact
    (h3SpectralScalarHeatRealC3Representative_contDiff_three hν ht G).comp
      hToLp

/-- On `Point3`, the real `C³` representative is exactly the a.e.
representative of the existing transported real decoder. -/
theorem h3SpectralScalarHeatRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3 ν t G
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) G)) : H3ScalarL2) :
      Point3 → ℝ) := by
  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN ν hν.le (NNReal.mk t ht.le) G
  let R : H3FourierRealL2 :=
    h3SpectralScalarDecodeRealL2 H

  have hFourier :
      h3SpectralScalarHeatRealC3Representative ν t G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((R : H3FourierRealL2) : H3FourierPoint3 → ℝ) := by
    dsimp [R, H]
    exact
      h3SpectralScalarHeatRealC3Representative_ae_eq_decodeRealL2
        hν ht G

  have hComp :
      (fun x : Point3 =>
        h3SpectralScalarHeatRealC3Representative ν t G
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (R : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hFourier

  have hFrom :
      ((h3FromFourierRealL2 R : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (R : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        R
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hFinal := hComp.trans hFrom.symm
  change
    (fun x : Point3 =>
      h3SpectralScalarHeatRealC3Representative ν t G
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2 R : H3ScalarL2) : Point3 → ℝ)
  exact hFinal

/-! ## Three-component velocity lift -/

/-- Coordinatewise real `C³` heat reconstruction of a spectral velocity
state, on the project carrier. -/
noncomputable def h3SpectralVelocityHeatRealC3RepresentativeOnPoint3
    (ν t : ℝ)
    (U : H3SpectralVelocityState) :
    Fin 3 → Point3 → ℝ :=
  fun j =>
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3 ν t (U j)

/-- Every velocity coordinate of the positive-time heat reconstruction is
spatially `C³`. -/
theorem h3SpectralVelocityHeatRealC3RepresentativeOnPoint3_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    ContDiff ℝ 3
      (h3SpectralVelocityHeatRealC3RepresentativeOnPoint3 ν t U j) := by
  exact
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3_contDiff_three
      hν ht (U j)

/-- Every velocity coordinate agrees a.e. with the exact real decoder of the
coordinatewise spectral heat evolution. -/
theorem h3SpectralVelocityHeatRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityHeatRealC3RepresentativeOnPoint3 ν t U j
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) U) j) : H3ScalarL2) :
      Point3 → ℝ) := by
  change
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3 ν t (U j)
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (U j))) : H3ScalarL2) :
      Point3 → ℝ)
  exact
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
      hν ht (U j)

end

end Euclidean
end Bridge
end PrimeTensor
