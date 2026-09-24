import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Raw.Forcing.Physical.L2.Third
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Pressure.Physical.L2.Second
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C4

/-!
# Third differentiated selected pressure in physical L²

The selected pressure-force identity is

    -∂ⱼ p = rawⱼ - lerayⱼ.

The raw and Leray forcing coordinates now both have every ordered third
physical spatial derivative in `L²`. Their selected representatives are
spatially `C³`, so differentiating the pressure-force identity three times
gives physical `L²` control of every ordered third derivative of the pressure
force.

The selected pressure gradient is spatially `C³` by the existing pressure C⁴
regularity theorem. Propagating the sign convention through the same ordered
three derivatives therefore gives every ordered fourth pressure derivative in
physical `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPressurePhysicalL2Third
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedPressurePhysicalL2Third :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The real inverse-Fourier reconstruction of one selected raw forcing
coordinate is spatially `C³` at every strict positive restart time. -/
private theorem h3SelectedRestartRealRawForcing_spatialC3
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
    SpatialC3
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

  have hThree :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMoments :
      ∀ (n : ℕ), n ≤ (3 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ n * ‖N ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 3 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne
    · simpa only using hTwo
    · simpa only using hThree

  have hFourier :
      ContDiff ℝ 3 (FourierTransform.fourier N) :=
    Real.contDiff_fourier hMoments

  have hNeg :
      ContDiff ℝ 3 (fun x : H3FourierPoint3 => -x) := by
    fun_prop

  have hInv :
      ContDiff ℝ 3
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv N x) := by
    have hComp :
        ContDiff ℝ 3
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier N (-x)) :=
      hFourier.comp hNeg
    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  have hToLp :
      ContDiff ℝ 3
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) :=
    PiLp.contDiff_toLp

  have hComplex :
      ContDiff ℝ 3
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) :=
    hInv.comp hToLp

  change
    ContDiff ℝ 3
      (Complex.reCLM ∘
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)))

  exact Complex.reCLM.contDiff.comp hComplex

/-- Every ordered third spatial derivative of the selected pressure force
belongs to physical `L²`. -/
theorem h3SelectedRestartPressureForce_spatial_d_three_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              PrimeTensor.Bridge.RealFluid.pressureForceComponent
                spatial3
                (h3RawFinPressureRealC1OfPath W)
                t x
                (h3AxisOfFin3 i)))))
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

  have hR3 :
      MemLp
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c R)))
        2
        (volume : Measure Point3) := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatial_d_three_memLp2
        hν U₀ hA hU₀ ht htR i a b c

  have hL3 :
      MemLp
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c L)))
        2
        (volume : Measure Point3) := by
    dsimp only [L, W]
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
        hν U₀ hA hU₀ ht htR i a b c

  have hSubAlg :
      MemLp
        ((spatial3.d a (spatial3.d b (spatial3.d c R))) -
          (spatial3.d a (spatial3.d b (spatial3.d c L))))
        2
        (volume : Measure Point3) :=
    hR3.sub hL3

  have hSubAE :
      (fun x : Point3 =>
        spatial3.d a (spatial3.d b (spatial3.d c R)) x -
          spatial3.d a (spatial3.d b (spatial3.d c L)) x)
        =ᵐ[(volume : Measure Point3)]
      ((spatial3.d a (spatial3.d b (spatial3.d c R))) -
        (spatial3.d a (spatial3.d b (spatial3.d c L)))) := by
    filter_upwards with x
    rfl

  have hSub :
      MemLp
        (fun x : Point3 =>
          spatial3.d a (spatial3.d b (spatial3.d c R)) x -
            spatial3.d a (spatial3.d b (spatial3.d c L)) x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hSubAE).2 hSubAlg

  have hRC3 : SpatialC3 R := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatialC3
        hν U₀ hA hU₀ ht htR.le i

  have hLC3 : SpatialC3 L := by
    unfold SpatialC3
    dsimp only [L, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hRC1 : SpatialC1 R := by
    have h := hRC3
    unfold SpatialC3 at h
    exact h.of_le (by norm_num)

  have hLC1 : SpatialC1 L := by
    have h := hLC3
    unfold SpatialC3 at h
    exact h.of_le (by norm_num)

  have hForceEq :
      F = fun x : Point3 => R x - L x := by
    funext x
    dsimp only [F, R, L]
    exact
      h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
        W t i x

  have hFirstEq :
      spatial3.d c F
        =
      fun x : Point3 =>
        spatial3.d c R x - spatial3.d c L x := by
    funext x
    rw [hForceEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRC1 hLC1 x c

  have hRcC2 :
      SpatialC2 (spatial3.d c R) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hRC3 c

  have hLcC2 :
      SpatialC2 (spatial3.d c L) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hLC3 c

  have hRcC1 : SpatialC1 (spatial3.d c R) := by
    have h := hRcC2
    unfold SpatialC2 at h
    exact h.of_le (by norm_num)

  have hLcC1 : SpatialC1 (spatial3.d c L) := by
    have h := hLcC2
    unfold SpatialC2 at h
    exact h.of_le (by norm_num)

  have hSecondEq :
      spatial3.d b (spatial3.d c F)
        =
      fun x : Point3 =>
        spatial3.d b (spatial3.d c R) x -
          spatial3.d b (spatial3.d c L) x := by
    funext x
    rw [hFirstEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRcC1 hLcC1 x b

  have hRbcC1 :
      SpatialC1 (spatial3.d b (spatial3.d c R)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hRcC2 b

  have hLbcC1 :
      SpatialC1 (spatial3.d b (spatial3.d c L)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hLcC2 b

  have hThirdEq :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c F))
        =
      fun x : Point3 =>
        spatial3.d a
            (spatial3.d b
              (spatial3.d c R)) x -
          spatial3.d a
            (spatial3.d b
              (spatial3.d c L)) x := by
    funext x
    rw [hSecondEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRbcC1 hLbcC1 x a

  rw [hThirdEq]
  exact hSub

/-- Every ordered fourth spatial derivative of the selected pressure belongs
 to physical `L²`. -/
theorem h3SelectedRestartPressureSpatialDerivative_four_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (a b c j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t)))))
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

  have hForceThird :
      MemLp
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c F)))
        2
        (volume : Measure Point3) := by
    dsimp only [F]
    have h :=
      h3SelectedRestartPressureForce_spatial_d_three_memLp2
        hν U₀ hA hU₀ ht htR i a b c
    simpa only [
      i,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using h

  have hNegAlg :
      MemLp
        (-(spatial3.d a
          (spatial3.d b
            (spatial3.d c F))))
        2
        (volume : Measure Point3) :=
    hForceThird.neg

  have hNegAE :
      (fun x : Point3 =>
        - spatial3.d a
            (spatial3.d b
              (spatial3.d c F)) x)
        =ᵐ[(volume : Measure Point3)]
      (-(spatial3.d a
        (spatial3.d b
          (spatial3.d c F)))) := by
    filter_upwards with x
    rfl

  have hNeg :
      MemLp
        (fun x : Point3 =>
          - spatial3.d a
              (spatial3.d b
                (spatial3.d c F)) x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hNegAE).2 hNegAlg

  have hGradC3 : SpatialC3 G := by
    dsimp only [G, W]
    exact
      h3RawFinPressureRealC1OfPath_selectedRestart_spatialDerivative_spatialC3
        hν U₀ hA hU₀ ht htR.le j

  have hGradC1 : SpatialC1 G := by
    have h := hGradC3
    unfold SpatialC3 at h
    exact h.of_le (by norm_num)

  have hFirstSign :
      spatial3.d c F
        =
      fun x : Point3 => - spatial3.d c G x := by
    funext x

    have hGrad :=
      hGradC1.hasDerivAt_coordinateLine_spatial_d x c

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ => F (coordinateLine x c r))
          (-(spatial3.d c G x))
          (x c) := by
      dsimp only [F, G]
      unfold PrimeTensor.Bridge.RealFluid.pressureForceComponent
      change
        HasDerivAt
          (-(fun r : ℝ =>
            spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t)
              (coordinateLine x c r)))
          (-(spatial3.d c
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t))
            x))
          (x c)
      exact hNegGrad

    have hForceValue :
        spatial3.d c F x = - spatial3.d c G x := by
      change partialDeriv c F x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    exact hForceValue

  have hGradFirstC2 :
      SpatialC2 (spatial3.d c G) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hGradC3 c

  have hGradFirstC1 :
      SpatialC1 (spatial3.d c G) := by
    have h := hGradFirstC2
    unfold SpatialC2 at h
    exact h.of_le (by norm_num)

  have hSecondSign :
      spatial3.d b (spatial3.d c F)
        =
      fun x : Point3 =>
        - spatial3.d b (spatial3.d c G) x := by
    funext x

    have hGrad :=
      hGradFirstC1.hasDerivAt_coordinateLine_spatial_d x b

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ =>
            (spatial3.d c F) (coordinateLine x b r))
          (-(spatial3.d b (spatial3.d c G) x))
          (x b) := by
      rw [hFirstSign]
      change
        HasDerivAt
          (-(fun r : ℝ =>
            (spatial3.d c G) (coordinateLine x b r)))
          (-(spatial3.d b (spatial3.d c G) x))
          (x b)
      exact hNegGrad

    have hForceValue :
        spatial3.d b (spatial3.d c F) x
          =
        -(spatial3.d b (spatial3.d c G) x) := by
      change partialDeriv b (spatial3.d c F) x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    exact hForceValue

  have hGradSecondC1 :
      SpatialC1
        (spatial3.d b
          (spatial3.d c G)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hGradFirstC2 b

  have hEq :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c G))
        =
      fun x : Point3 =>
        - spatial3.d a
            (spatial3.d b
              (spatial3.d c F)) x := by
    funext x

    have hGrad :=
      hGradSecondC1.hasDerivAt_coordinateLine_spatial_d x a

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ =>
            (spatial3.d b
              (spatial3.d c F))
              (coordinateLine x a r))
          (-(spatial3.d a
            (spatial3.d b
              (spatial3.d c G)) x))
          (x a) := by
      rw [hSecondSign]
      change
        HasDerivAt
          (-(fun r : ℝ =>
            (spatial3.d b
              (spatial3.d c G))
              (coordinateLine x a r)))
          (-(spatial3.d a
            (spatial3.d b
              (spatial3.d c G)) x))
          (x a)
      exact hNegGrad

    have hForceValue :
        spatial3.d a
            (spatial3.d b
              (spatial3.d c F)) x
          =
        -(spatial3.d a
          (spatial3.d b
            (spatial3.d c G)) x) := by
      change
        partialDeriv a
          (spatial3.d b
            (spatial3.d c F)) x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    linarith

  dsimp only [G] at hEq ⊢
  rw [hEq]
  exact hNeg

end

end Euclidean
end Bridge
end PrimeTensor
