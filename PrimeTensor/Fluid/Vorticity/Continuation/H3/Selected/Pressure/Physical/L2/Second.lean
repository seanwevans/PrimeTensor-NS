import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Raw.Forcing.Physical.L2.Second
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Pressure.Physical.L2.First
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C4

/-!
# Second differentiated selected pressure in physical L²

The selected pressure-force identity is

    -∂ⱼ p = rawⱼ - lerayⱼ.

The raw and Leray forcing coordinates now both have ordered second physical
spatial derivatives in `L²`.  Their selected representatives are spatially
`C²`, so differentiating the pressure-force identity twice gives physical
`L²` control of every ordered second derivative of the pressure force.

The selected pressure gradient is spatially `C³`.  Differentiating the sign
convention twice therefore identifies each ordered third pressure derivative
with the negative of the corresponding second pressure-force derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPressurePhysicalL2Second
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedPressurePhysicalL2Second :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The real inverse-Fourier reconstruction of one selected raw forcing
coordinate is spatially `C²` at every strict positive restart time. -/
private theorem h3SelectedRestartRealRawForcing_spatialC2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    SpatialC2
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W t) (W t) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  have hZero :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hOne :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTwo :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMoments :
      ∀ (n : ℕ), n ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ n * ‖N ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 2 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne
    · simpa only using hTwo

  have hFourier :
      ContDiff ℝ 2 (FourierTransform.fourier N) :=
    Real.contDiff_fourier hMoments

  have hNeg :
      ContDiff ℝ 2 (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 2
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv N x) := by
    have hComp :
        ContDiff ℝ 2
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier N (-x)) :=
      hFourier.comp hNeg
    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  have hToLp :
      ContDiff ℝ 2
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) :=
    PiLp.contDiff_toLp

  have hComplex :
      ContDiff ℝ 2
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) :=
    hInv.comp hToLp

  change
    ContDiff ℝ 2
      (Complex.reCLM ∘
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)))

  exact Complex.reCLM.contDiff.comp hComplex

/-- Every ordered second spatial derivative of the selected pressure force
belongs to physical `L²`. -/
theorem h3SelectedRestartPressureForce_spatial_d_two_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d b
          (fun x : Point3 =>
            PrimeTensor.Bridge.RealFluid.pressureForceComponent
              spatial3
              (h3RawFinPressureRealC1OfPath W)
              t x
              (h3AxisOfFin3 i))))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let R : ScalarField3 :=
    fun x : Point3 =>
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          (W t) (W t) i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re

  let L : ScalarField3 :=
    fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i x).re

  let F : ScalarField3 :=
    fun x : Point3 =>
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3RawFinPressureRealC1OfPath W)
        t x
        (h3AxisOfFin3 i)

  have hR2 :
      MemLp
        (spatial3.d a (spatial3.d b R))
        2
        (volume : Measure Point3) := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatial_d_two_memLp2
        hν U₀ hA hU₀ ht htR i a b

  have hL2 :
      MemLp
        (spatial3.d a (spatial3.d b L))
        2
        (volume : Measure Point3) := by
    dsimp only [L, W]
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
        hν U₀ hA hU₀ ht htR i a b

  have hSubAlg :
      MemLp
        ((spatial3.d a (spatial3.d b R)) -
          (spatial3.d a (spatial3.d b L)))
        2
        (volume : Measure Point3) :=
    hR2.sub hL2

  have hSubAE :
      (fun x : Point3 =>
        spatial3.d a (spatial3.d b R) x -
          spatial3.d a (spatial3.d b L) x)
        =ᵐ[(volume : Measure Point3)]
      ((spatial3.d a (spatial3.d b R)) -
        (spatial3.d a (spatial3.d b L))) := by
    filter_upwards with x
    rfl

  have hSub :
      MemLp
        (fun x : Point3 =>
          spatial3.d a (spatial3.d b R) x -
            spatial3.d a (spatial3.d b L) x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hSubAE).2 hSubAlg

  have hRC2 : SpatialC2 R := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatialC2
        hν U₀ hA hU₀ ht htR.le i

  have hRC1 : SpatialC1 R := by
    unfold SpatialC2 at hRC2
    exact hRC2.of_le (by norm_num)

  have hLC3 : SpatialC3 L := by
    unfold SpatialC3
    dsimp only [L, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hLC2 : SpatialC2 L := by
    unfold SpatialC3 at hLC3
    exact hLC3.of_le (by norm_num)

  have hLC1 : SpatialC1 L := by
    unfold SpatialC2 at hLC2
    exact hLC2.of_le (by norm_num)

  have hForceEq :
      F = fun x : Point3 => R x - L x := by
    funext x
    dsimp only [F, R, L]
    exact
      h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
        W t i x

  have hFirstEq :
      spatial3.d b F
        =
      fun x : Point3 =>
        spatial3.d b R x - spatial3.d b L x := by
    funext x
    rw [hForceEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRC1 hLC1 x b

  have hRbC1 :
      SpatialC1 (spatial3.d b R) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hRC2 b

  have hLbC1 :
      SpatialC1 (spatial3.d b L) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hLC2 b

  have hSecondEq :
      spatial3.d a (spatial3.d b F)
        =
      fun x : Point3 =>
        spatial3.d a (spatial3.d b R) x -
          spatial3.d a (spatial3.d b L) x := by
    funext x
    rw [hFirstEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRbC1 hLbC1 x a

  rw [hSecondEq]
  exact hSub

/-- Every ordered third spatial derivative of the selected pressure belongs to
physical `L²`. -/
theorem h3SelectedRestartPressureSpatialDerivative_three_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (a b j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d j
            ((h3RawFinPressureRealC1OfPath W) t))))
      2
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let i : Fin 3 := h3ClassicalizationFinOfAxis j

  let F : ScalarField3 :=
    fun x : Point3 =>
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3RawFinPressureRealC1OfPath W)
        t x j

  let G : ScalarField3 :=
    spatial3.d j ((h3RawFinPressureRealC1OfPath W) t)

  have hForceSecond :
      MemLp
        (spatial3.d a (spatial3.d b F))
        2
        (volume : Measure Point3) := by
    dsimp only [F]
    have h :=
      h3SelectedRestartPressureForce_spatial_d_two_memLp2
        hν U₀ hA hU₀ ht htR i a b
    simpa only [
      i,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using h

  have hNegAlg :
      MemLp
        (-(spatial3.d a (spatial3.d b F)))
        2
        (volume : Measure Point3) :=
    hForceSecond.neg

  have hNegAE :
      (fun x : Point3 =>
        - spatial3.d a (spatial3.d b F) x)
        =ᵐ[(volume : Measure Point3)]
      (-(spatial3.d a (spatial3.d b F))) := by
    filter_upwards with x
    rfl

  have hNeg :
      MemLp
        (fun x : Point3 =>
          - spatial3.d a (spatial3.d b F) x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hNegAE).2 hNegAlg

  have hGradC3 : SpatialC3 G := by
    dsimp only [G, W]
    exact
      h3RawFinPressureRealC1OfPath_selectedRestart_spatialDerivative_spatialC3
        hν U₀ hA hU₀ ht htR.le j

  have hGradC1 : SpatialC1 G := by
    unfold SpatialC3 at hGradC3
    exact hGradC3.of_le (by norm_num)

  have hFirstSign :
      spatial3.d b F
        =
      fun x : Point3 => - spatial3.d b G x := by
    funext x

    have hGrad :=
      hGradC1.hasDerivAt_coordinateLine_spatial_d x b

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ => F (coordinateLine x b r))
          (-(spatial3.d b G x))
          (x b) := by
      dsimp only [F, G]
      unfold PrimeTensor.Bridge.RealFluid.pressureForceComponent
      change
        HasDerivAt
          (-(fun r : ℝ =>
            spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t)
              (coordinateLine x b r)))
          (-(spatial3.d b
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t))
            x))
          (x b)
      exact hNegGrad

    have hForceValue :
        spatial3.d b F x = - spatial3.d b G x := by
      change partialDeriv b F x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    exact hForceValue

  have hGradFirstC2 :
      SpatialC2 (spatial3.d b G) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hGradC3 b

  have hGradFirstC1 :
      SpatialC1 (spatial3.d b G) := by
    unfold SpatialC2 at hGradFirstC2
    exact hGradFirstC2.of_le (by norm_num)

  have hEq :
      spatial3.d a (spatial3.d b G)
        =
      fun x : Point3 =>
        - spatial3.d a (spatial3.d b F) x := by
    funext x

    have hGrad :=
      hGradFirstC1.hasDerivAt_coordinateLine_spatial_d x a

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ =>
            (spatial3.d b F) (coordinateLine x a r))
          (-(spatial3.d a (spatial3.d b G) x))
          (x a) := by
      rw [hFirstSign]
      change
        HasDerivAt
          (-(fun r : ℝ =>
            (spatial3.d b G) (coordinateLine x a r)))
          (-(spatial3.d a (spatial3.d b G) x))
          (x a)
      exact hNegGrad

    have hForceValue :
        spatial3.d a (spatial3.d b F) x
          =
        -(spatial3.d a (spatial3.d b G) x) := by
      change partialDeriv a (spatial3.d b F) x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    linarith

  dsimp only [G] at hEq ⊢
  rw [hEq]
  exact hNeg

end

end Euclidean
end Bridge
end PrimeTensor
