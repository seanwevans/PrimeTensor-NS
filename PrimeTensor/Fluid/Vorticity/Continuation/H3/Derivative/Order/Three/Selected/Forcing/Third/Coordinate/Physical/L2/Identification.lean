import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Forcing.Third.Coordinate.Physical.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet

/-!
# Identify the selected forcing third-derivative physical L² package

The preceding checkpoint transported every ordered third-coordinate selected
Leray-forcing multiplier from Fourier `L²` into physical real `L²` on a
positive terminal slab.

This file identifies that transported package with the literal physical third
spatial derivative

    spatial3.d a (spatial3.d b (spatial3.d c N_j)).

The proof is the direct order-three analogue of the already-closed Hessian
bridge:

* inverse Plancherel agrees a.e. with the ordinary inverse Fourier integral for
  the integrable Fourier `L²` amplitude;
* the selected forcing third-Frechet endpoint identifies that inverse Fourier
  integral pointwise with the literal third spatial derivative.

The literal third derivative is then packaged directly as `H3ScalarL2`, shown
equal to the transported physical package, and hence inherits strong `L²`
continuity on every positive terminal slab strictly inside the restart radius.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedForcingThirdCoordinatePhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedForcingThirdCoordinatePhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On a positive terminal slab, the transported physical third-coordinate
package has the ordinary inverse Fourier third-coordinate amplitude as an a.e.
representative. -/
theorem h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    (((h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b c s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                h3RawFinLerayOuterProductDivergence
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ (s : ℝ))
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ (s : ℝ))
                  i ξ)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re)) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol
          (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol
            (h3ClassicalizationFinOfAxis b) ξ *
          (h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis c) ξ *
            h3RawFinLerayOuterProductDivergence
              (W (s : ℝ)) (W (s : ℝ)) i ξ))

  let f2 : H3FourierComplexL2 :=
    h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
      (h3ClassicalizationFinOfAxis c)
      s

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
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3SelectedRestartForcingThirdCoordinate_memLp2
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)

  have hCompat :
      FourierTransformInv.fourierInv raw
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    unfold h3SelectedRestartForcingThirdCoordinateFourierL2OnSlab
    unfold h3SelectedRestartForcingThirdCoordinateFourierL2
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
    h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab,
    r2, u2, f2, raw, W
  ] using hAE

/-- On a slab strictly inside the restart radius, the ordinary inverse Fourier
third-coordinate amplitude is pointwise the literal third spatial derivative
of the selected real Leray forcing. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_three_eq_fourierInvThirdOnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (s : ℝ)) (W (s : ℝ)) i x).re)))
      =
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              (h3FourierDerivativeSymbol
                  (h3ClassicalizationFinOfAxis c) ξ *
                h3RawFinLerayOuterProductDivergence
                  (W (s : ℝ)) (W (s : ℝ)) i ξ)))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 :=
    h3ClassicalizationFinOfAxis a
  let bf : Fin 3 :=
    h3ClassicalizationFinOfAxis b
  let cf : Fin 3 :=
    h3ClassicalizationFinOfAxis c

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ *
          (h3FourierDerivativeSymbol cf ξ *
            h3RawFinLerayOuterProductDivergence
              (W (s : ℝ)) (W (s : ℝ)) i ξ))

  have hsPos : 0 < (s : ℝ) := by
    have hHalf : 0 < q / 2 := by positivity
    exact lt_of_lt_of_le hHalf s.property.1

  have hsR :
      (s : ℝ) < h3FinHeatLerayRestartRadius ν A :=
    lt_of_le_of_lt s.property.2 hqR

  funext x

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
      hν U₀ hA hU₀ hsPos hsR.le i af bf cf
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hPhysical :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_three_eq_re_thirdFrechet
      hν U₀ hA hU₀ hsPos hsR i x a b c

  have hInvEq :
      FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        =
      iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W (s : ℝ)) (W (s : ℝ)) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b,
          h3FourierAxisDirection c
        ] := by
    dsimp only at hEndpoint
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative at hEndpoint
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude at hEndpoint
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W (s : ℝ)) (W (s : ℝ)) i
    ] at hEndpoint
    simpa only [
      raw, af, bf, cf, W,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hEndpoint

  calc
    spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (s : ℝ)) (W (s : ℝ)) i y).re)))
        x
        =
      (iteratedFDeriv ℝ 3
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W (s : ℝ)) (W (s : ℝ)) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b,
          h3FourierAxisDirection c
        ]).re := hPhysical
    _ =
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      congrArg Complex.re hInvEq.symm

/-- The transported physical package is a.e. the literal selected real Leray
forcing third derivative on every slab strictly inside the restart radius. -/
theorem h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab_ae_eq_spatial_d_three
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a b c s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (s : ℝ)) (W (s : ℝ)) i x).re)))) := by
  dsimp only

  have hInv :=
    h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
      hν U₀ hA hU₀ hq hqR.le i a b c s

  have hPoint :=
    h3SelectedRestartRealLerayForcing_spatial_d_three_eq_fourierInvThirdOnSlab
      hν U₀ hA hU₀ hq hqR i a b c s

  filter_upwards [hInv] with x hx
  rw [hx]
  exact congrFun hPoint x |>.symm

/-- Literal third spatial derivative of the selected real Leray forcing,
packaged as physical `H3ScalarL2` on a slab strictly inside the restart
radius. -/
noncomputable def h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (lt_of_le_of_lt s.property.2 hqR)
      i a b c).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (s : ℝ)) (W (s : ℝ)) i x).re))))

/-- The literal forcing third-derivative `L²` state equals the transported
physical package. -/
theorem h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab_eq_physicalL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c s
      =
    h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a b c s := by
  apply MeasureTheory.Lp.ext

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLiteral :
      (((h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b c s : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (s : ℝ)) (W (s : ℝ)) i x).re)))) := by
    dsimp only [
      h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab,
      W
    ]
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
          hν U₀ hA hU₀
          (by
            have hHalf : 0 < q / 2 := by positivity
            exact lt_of_lt_of_le hHalf s.property.1)
          (lt_of_le_of_lt s.property.2 hqR)
          i a b c)

  have hPackage :=
    h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab_ae_eq_spatial_d_three
      hν U₀ hA hU₀ hq hqR i a b c s

  filter_upwards [hLiteral, hPackage] with x hxLiteral hxPackage
  exact hxLiteral.trans hxPackage.symm

/-- The literal selected Leray-forcing third derivative is strongly continuous
in physical `L²` on every positive slab strictly inside the restart radius. -/
theorem continuous_h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b c) := by

  have hPhysical :
      Continuous
        (h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a b c) :=
    continuous_h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a b c

  have hEq :
      h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b c
        =
      h3SelectedRestartForcingThirdCoordinatePhysicalL2OnSlab
        hν U₀ hA hU₀ hq hqR.le i a b c := by
    funext s
    exact
      h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab_eq_physicalL2
        hν U₀ hA hU₀ hq hqR i a b c s

  rw [hEq]
  exact hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
