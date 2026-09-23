import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedForcingFirstCoordinatePhysicalL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingPhysicalL2Jet

/-!
# Identify the selected first forcing coordinate physical L² package

The preceding checkpoint transported the strongly continuous first-coordinate
Leray-forcing multiplier from Fourier `L²` into physical real `L²` on every
positive terminal slab.

This file identifies that canonical physical package with the literal first
spatial derivative of the selected real Leray forcing.  The proof uses the
same two representation bridges already established elsewhere in the project:

* inverse Plancherel agrees a.e. with the ordinary inverse Fourier integral for
  an integrable Fourier `L²` amplitude;
* the selected forcing endpoint theorem identifies the ordinary inverse
  Fourier first-coordinate multiplier pointwise with the literal
  `spatial3.d` field.

We then package the literal derivative itself as an `H3ScalarL2` state and
prove its slab path is strongly continuous by equality with the transported
package.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedForcingFirstCoordinatePhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedForcingFirstCoordinatePhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On a positive terminal slab, the transported physical package has the
ordinary inverse Fourier first-coordinate amplitude as an a.e.
representative. -/
theorem h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    (((h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR i a s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            h3RawFinLerayOuterProductDivergence
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ (s : ℝ))
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ (s : ℝ))
              i ξ)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        h3RawFinLerayOuterProductDivergence
          (W (s : ℝ)) (W (s : ℝ)) i ξ

  let f2 : H3FourierComplexL2 :=
    h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i
      (h3ClassicalizationFinOfAxis a) s

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let r2 : H3FourierRealL2 :=
    h3RealPartFourierL2 u2

  have hsPos : 0 < (s : ℝ) := by
    have hHalf : 0 < q / 2 := by positivity
    exact lt_of_lt_of_le hHalf s.property.1

  have hsR :
      (s : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    s.property.2.trans hqR

  have hRawInt :
      Integrable raw
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3SelectedRestartForcingFirstCoordinate_memLp2
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)

  have hCompat :
      FourierTransformInv.fourierInv raw
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    unfold h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
    unfold h3SelectedRestartForcingFirstCoordinateFourierL2
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hRawInt hRaw2

  have hCompatPoint :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hRe :
      ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ).re) := by
    dsimp only [r2]
    unfold h3RealPartFourierL2
    exact Complex.reCLM.coeFn_compLp u2

  have hRePoint :
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hRe

  have hFrom :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        r2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by
    filter_upwards [hFrom, hRePoint, hCompatPoint] with x hxFrom hxRe hxCompat
    calc
      ((h3FromFourierRealL2 r2 : H3ScalarL2) : Point3 → ℝ) x
          =
        ((r2 : H3FourierRealL2) : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) := hxFrom
      _ =
        (((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := hxRe
      _ =
        (FourierTransformInv.fourierInv raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
        congrArg Complex.re hxCompat.symm

  simpa only [
    h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab,
    r2, u2, f2, raw, W
  ] using hAE

/-- On a slab strictly inside the restart radius, the ordinary inverse Fourier
first-coordinate amplitude is pointwise the literal first spatial derivative
of the selected real Leray forcing. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_eq_fourierInvFirstOnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (s : ℝ)) (W (s : ℝ)) i x).re)
      =
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            h3RawFinLerayOuterProductDivergence
              (W (s : ℝ)) (W (s : ℝ)) i ξ)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        h3RawFinLerayOuterProductDivergence
          (W (s : ℝ)) (W (s : ℝ)) i ξ

  have hsPos : 0 < (s : ℝ) := by
    have hHalf : 0 < q / 2 := by positivity
    exact lt_of_lt_of_le hHalf s.property.1

  have hsR :
      (s : ℝ) < h3FinHeatLerayRestartRadius ν A :=
    lt_of_le_of_lt s.property.2 hqR

  funext x

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
      hν U₀ hA hU₀ hsPos hsR.le i af
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hPhysical :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_eq_re_fderiv
      hν U₀ hA hU₀ hsPos hsR i x a

  have hInvEq :
      FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        =
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W (s : ℝ)) (W (s : ℝ)) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        (h3FourierAxisDirection a) := by
    dsimp only at hEndpoint
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative at hEndpoint
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W (s : ℝ)) (W (s : ℝ)) i
    ] at hEndpoint
    simpa only [
      raw, af, W,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hEndpoint

  calc
    spatial3.d a
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (s : ℝ)) (W (s : ℝ)) i y).re)
        x
        =
      ((fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W (s : ℝ)) (W (s : ℝ)) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        (h3FourierAxisDirection a)).re := hPhysical
    _ =
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      congrArg Complex.re hInvEq.symm

/-- The transported physical package is a.e. the literal selected real Leray
forcing first derivative on every slab strictly inside the restart radius. -/
theorem h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab_ae_eq_spatial_d
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (s : ℝ)) (W (s : ℝ)) i x).re)) := by
  dsimp only

  have hInv :=
    h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
      hν U₀ hA hU₀ hq hqR.le i a s

  have hPoint :=
    h3SelectedRestartRealLerayForcing_spatial_d_eq_fourierInvFirstOnSlab
      hν U₀ hA hU₀ hq hqR i a s

  filter_upwards [hInv] with x hx
  rw [hx]
  exact congrFun hPoint x |>.symm

/-- Literal first spatial derivative of the selected real Leray forcing,
packaged as physical `H3ScalarL2` on a slab strictly inside the restart
radius. -/
noncomputable def h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartRealLerayForcing_spatial_d_memLp2
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (lt_of_le_of_lt s.property.2 hqR)
      i a).toLp
    (spatial3.d a
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (s : ℝ)) (W (s : ℝ)) i x).re))

/-- The literal forcing-derivative `L²` state equals the transported physical
package. -/
theorem h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab_eq_physicalL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a s
      =
    h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a s := by
  apply MeasureTheory.Lp.ext

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLiteral :
      (((h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a s : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (s : ℝ)) (W (s : ℝ)) i x).re)) := by
    dsimp only [
      h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab,
      W
    ]
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (h3SelectedRestartRealLerayForcing_spatial_d_memLp2
          hν U₀ hA hU₀
          (by
            have hHalf : 0 < q / 2 := by positivity
            exact lt_of_lt_of_le hHalf s.property.1)
          (lt_of_le_of_lt s.property.2 hqR)
          i a)

  have hPackage :=
    h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab_ae_eq_spatial_d
      hν U₀ hA hU₀ hq hqR i a s

  filter_upwards [hLiteral, hPackage] with x hxLiteral hxPackage
  exact hxLiteral.trans hxPackage.symm

/-- The literal selected Leray-forcing first derivative is strongly continuous
in physical `L²` on every positive slab strictly inside the restart radius. -/
theorem continuous_h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a) := by
  have hPhysical :
      Continuous
        (h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a) :=
    continuous_h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a

  have hEq :
      h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a
        =
      h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
        hν U₀ hA hU₀ hq hqR.le i a := by
    funext s
    exact
      h3SelectedRestartRealLerayForcingFirstCoordinateL2OnSlab_eq_physicalL2
        hν U₀ hA hU₀ hq hqR i a s

  rw [hEq]
  exact hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
