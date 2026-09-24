import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Forcing.Second.Coordinate.Physical.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet

/-!
# Identify the selected forcing Hessian physical L² package

The preceding checkpoint transported each ordered second-coordinate selected
Leray-forcing multiplier from Fourier `L²` into physical real `L²` on every
positive terminal slab.

This file identifies that transported package with the literal physical Hessian

    spatial3.d a (spatial3.d b N_j).

The proof is the order-two analogue of the already-closed order-one bridge:

* inverse Plancherel agrees a.e. with the ordinary inverse Fourier integral for
  the integrable Fourier `L²` amplitude;
* the selected forcing second-Frechet endpoint theorem identifies that ordinary
  inverse Fourier integral pointwise with the literal second spatial
  derivative.

The literal Hessian is then packaged directly as `H3ScalarL2`, shown equal to
the transported package, and therefore strongly continuous on each positive
terminal slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedForcingSecondCoordinatePhysicalL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedForcingSecondCoordinatePhysicalL2Identification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On a positive terminal slab, the transported physical second-coordinate
package has the ordinary inverse Fourier Hessian amplitude as an a.e.
representative. -/
theorem h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    (((h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              h3RawFinLerayOuterProductDivergence
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ (s : ℝ))
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ (s : ℝ))
                i ξ))
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
          h3RawFinLerayOuterProductDivergence
            (W (s : ℝ)) (W (s : ℝ)) i ξ)

  let f2 : H3FourierComplexL2 :=
    h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
      hν U₀ hA hU₀ hq hqR i
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
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
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)

  have hRaw2 :
      MemLp raw 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3SelectedRestartForcingSecondCoordinate_memLp2
        hν U₀ hA hU₀ hsPos hsR i
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)

  have hCompat :
      FourierTransformInv.fourierInv raw
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    unfold h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
    unfold h3SelectedRestartForcingSecondCoordinateFourierL2
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
    h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab,
    r2, u2, f2, raw, W
  ] using hAE

/-- On a slab strictly inside the restart radius, the ordinary inverse Fourier
second-coordinate amplitude is pointwise the literal second spatial derivative
of the selected real Leray forcing. -/
theorem h3SelectedRestartRealLerayForcing_spatial_d_two_eq_fourierInvSecondOnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d a
      (spatial3.d b
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (s : ℝ)) (W (s : ℝ)) i x).re))
      =
    (fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol
              (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol
                (h3ClassicalizationFinOfAxis b) ξ *
              h3RawFinLerayOuterProductDivergence
                (W (s : ℝ)) (W (s : ℝ)) i ξ))
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let af : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  let bf : Fin 3 :=
    h3ClassicalizationFinOfAxis b

  let raw : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol af ξ *
        (h3FourierDerivativeSymbol bf ξ *
          h3RawFinLerayOuterProductDivergence
            (W (s : ℝ)) (W (s : ℝ)) i ξ)

  have hsPos : 0 < (s : ℝ) := by
    have hHalf : 0 < q / 2 := by positivity
    exact lt_of_lt_of_le hHalf s.property.1

  have hsR :
      (s : ℝ) < h3FinHeatLerayRestartRadius ν A :=
    lt_of_le_of_lt s.property.2 hqR

  funext x

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
      hν U₀ hA hU₀ hsPos hsR.le i af bf
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hPhysical :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_spatial_d_two_eq_re_secondFrechet
      hν U₀ hA hU₀ hsPos hsR i x a b

  have hInvEq :
      FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        =
      iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W (s : ℝ)) (W (s : ℝ)) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b
        ] := by
    dsimp only at hEndpoint
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative at hEndpoint
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude at hEndpoint
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W (s : ℝ)) (W (s : ℝ)) i
    ] at hEndpoint
    simpa only [
      raw, af, bf, W,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hEndpoint

  calc
    spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (s : ℝ)) (W (s : ℝ)) i y).re))
        x
        =
      (iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W (s : ℝ)) (W (s : ℝ)) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        ![
          h3FourierAxisDirection a,
          h3FourierAxisDirection b
        ]).re := hPhysical
    _ =
      (FourierTransformInv.fourierInv
          raw
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      congrArg Complex.re hInvEq.symm

/-- The transported physical package is a.e. the literal selected real Leray
forcing Hessian on every slab strictly inside the restart radius. -/
theorem h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab_ae_eq_spatial_d_two
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a b s : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (s : ℝ)) (W (s : ℝ)) i x).re))) := by
  dsimp only

  have hInv :=
    h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab_ae_eq_fourierInv
      hν U₀ hA hU₀ hq hqR.le i a b s

  have hPoint :=
    h3SelectedRestartRealLerayForcing_spatial_d_two_eq_fourierInvSecondOnSlab
      hν U₀ hA hU₀ hq hqR i a b s

  filter_upwards [hInv] with x hx
  rw [hx]
  exact congrFun hPoint x |>.symm

/-- Literal second spatial derivative of the selected real Leray forcing,
packaged as physical `H3ScalarL2` on a slab strictly inside the restart
radius. -/
noncomputable def h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
      hν U₀ hA hU₀
      (by
        have hHalf : 0 < q / 2 := by positivity
        exact lt_of_lt_of_le hHalf s.property.1)
      (lt_of_le_of_lt s.property.2 hqR)
      i a b).toLp
    (spatial3.d a
      (spatial3.d b
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (s : ℝ)) (W (s : ℝ)) i x).re)))

/-- The literal forcing-Hessian `L²` state equals the transported physical
package. -/
theorem h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab_eq_physicalL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b s
      =
    h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a b s := by
  apply MeasureTheory.Lp.ext

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLiteral :
      (((h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b s : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (s : ℝ)) (W (s : ℝ)) i x).re))) := by
    dsimp only [
      h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab,
      W
    ]
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
          hν U₀ hA hU₀
          (by
            have hHalf : 0 < q / 2 := by positivity
            exact lt_of_lt_of_le hHalf s.property.1)
          (lt_of_le_of_lt s.property.2 hqR)
          i a b)

  have hPackage :=
    h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab_ae_eq_spatial_d_two
      hν U₀ hA hU₀ hq hqR i a b s

  filter_upwards [hLiteral, hPackage] with x hxLiteral hxPackage
  exact hxLiteral.trans hxPackage.symm

/-- The literal selected Leray-forcing Hessian is strongly continuous in
physical `L²` on every positive slab strictly inside the restart radius. -/
theorem continuous_h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b) := by
  have hPhysical :
      Continuous
        (h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
          hν U₀ hA hU₀ hq hqR.le i a b) :=
    continuous_h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
      hν U₀ hA hU₀ hq hqR.le i a b

  have hEq :
      h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab
          hν U₀ hA hU₀ hq hqR i a b
        =
      h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
        hν U₀ hA hU₀ hq hqR.le i a b := by
    funext s
    exact
      h3SelectedRestartRealLerayForcingSecondCoordinateL2OnSlab_eq_physicalL2
        hν U₀ hA hU₀ hq hqR i a b s

  rw [hEq]
  exact hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
