import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingPhysicalL2First
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingPhysicalL2Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPressurePhysicalL2Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C4

/-!
# First differentiated selected pressure in physical L²

The selected pressure-force identity is

    -∂ⱼ p = rawⱼ - lerayⱼ.

The raw and Leray terms now both have first physical spatial derivatives in
`L²`.  Their selected positive-time representatives are spatially `C¹`, so the
project's exact derivative-linearity theorem differentiates this identity once.
Hence every first spatial derivative of the pressure force belongs to `L²`.

The selected pressure itself is spatially `C⁴`; therefore its first pressure
partial is `C³`.  Differentiating the sign convention

    pressureForceⱼ = -∂ⱼ p

identifies the pressure Hessian with the negative pressure-force derivative.
Thus every ordered second pressure partial belongs to physical `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPressurePhysicalL2First
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedPressurePhysicalL2First :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The real inverse-Fourier reconstruction of the selected raw forcing is
spatially `C¹` at every strict positive restart time. -/
private theorem h3SelectedRestartRealRawForcing_spatialC1
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
    SpatialC1
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

  have hMoments :
      ∀ (n : ℕ), n ≤ (1 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ n * ‖N ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hnNat : n ≤ 1 := by
      exact_mod_cast hn
    interval_cases n
    · simpa only [pow_zero, one_mul] using hZero.norm
    · simpa only [pow_one] using hOne

  have hFourier :
      ContDiff ℝ 1 (FourierTransform.fourier N) :=
    Real.contDiff_fourier hMoments

  have hInv :
      ContDiff ℝ 1
        (fun x : H3FourierPoint3 =>
          FourierTransformInv.fourierInv N x) := by
    have hComp :
        ContDiff ℝ 1
          (fun x : H3FourierPoint3 =>
            FourierTransform.fourier N (-x)) :=
      hFourier.comp (by fun_prop)
    simpa only [Real.fourierInv_eq_fourier_neg] using hComp

  have hToLp :
      ContDiff ℝ 1
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) :=
    PiLp.contDiff_toLp

  have hComplex :
      ContDiff ℝ 1
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) :=
    hInv.comp hToLp

  change
    ContDiff ℝ 1
      (Complex.reCLM ∘
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            N
            ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)))

  exact Complex.reCLM.contDiff.comp hComplex

/-- One spatial derivative of the selected pressure force belongs to physical
`L²`. -/
theorem h3SelectedRestartPressureForce_spatial_d_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (fun x : Point3 =>
          PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath W)
            t x
            (h3AxisOfFin3 i)))
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

  have hR1 :
      MemLp (spatial3.d a R) 2 (volume : Measure Point3) := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatial_d_memLp2
        hν U₀ hA hU₀ ht htR i a

  have hL1 :
      MemLp (spatial3.d a L) 2 (volume : Measure Point3) := by
    dsimp only [L, W]
    exact
      h3SelectedRestartRealLerayForcing_spatial_d_memLp2
        hν U₀ hA hU₀ ht htR i a

  have hR1SubL1Alg :
      MemLp
        ((spatial3.d a R) - (spatial3.d a L))
        2
        (volume : Measure Point3) :=
    hR1.sub hL1

  have hR1SubL1AE :
      (fun x : Point3 =>
        spatial3.d a R x - spatial3.d a L x)
        =ᵐ[(volume : Measure Point3)]
      ((spatial3.d a R) - (spatial3.d a L)) := by
    filter_upwards with x
    rfl

  have hR1SubL1 :
      MemLp
        (fun x : Point3 =>
          spatial3.d a R x - spatial3.d a L x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hR1SubL1AE).2 hR1SubL1Alg

  have hRC1 : SpatialC1 R := by
    dsimp only [R, W]
    exact
      h3SelectedRestartRealRawForcing_spatialC1
        hν U₀ hA hU₀ ht htR.le i

  have hLC3 : ContDiff ℝ 3 L := by
    dsimp only [L, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hLC1 : SpatialC1 L :=
    hLC3.of_le (by norm_num)

  have hForceEq :
      F = fun x : Point3 => R x - L x := by
    funext x
    dsimp only [F, R, L]
    exact
      h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
        W t i x

  have hDerivEq :
      spatial3.d a F
        =
      fun x : Point3 =>
        spatial3.d a R x - spatial3.d a L x := by
    funext x
    rw [hForceEq]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
        hRC1 hLC1 x a

  rw [hDerivEq]
  exact hR1SubL1

/-- Every ordered second spatial pressure derivative of the selected pressure
belongs to physical `L²`. -/
theorem h3SelectedRestartPressureSpatialDerivative_two_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (a j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (spatial3.d a
        (spatial3.d j
          ((h3RawFinPressureRealC1OfPath W) t)))
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

  have hForceDeriv :
      MemLp (spatial3.d a F) 2 (volume : Measure Point3) := by
    dsimp only [F]
    have h :=
      h3SelectedRestartPressureForce_spatial_d_memLp2
        hν U₀ hA hU₀ ht htR i a
    simpa only [
      i,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using h

  have hNegAlg :
      MemLp
        (-(spatial3.d a F))
        2
        (volume : Measure Point3) :=
    hForceDeriv.neg

  have hNegAE :
      (fun x : Point3 => - spatial3.d a F x)
        =ᵐ[(volume : Measure Point3)]
      (-(spatial3.d a F)) := by
    filter_upwards with x
    rfl

  have hNeg :
      MemLp
        (fun x : Point3 => - spatial3.d a F x)
        2
        (volume : Measure Point3) :=
    (memLp_congr_ae hNegAE).2 hNegAlg

  have hGradC3 :
      SpatialC3
        (spatial3.d j
          ((h3RawFinPressureRealC1OfPath W) t)) := by
    dsimp only [W]
    exact
      h3RawFinPressureRealC1OfPath_selectedRestart_spatialDerivative_spatialC3
        hν U₀ hA hU₀ ht htR.le j

  have hGradC1 :
      SpatialC1
        (spatial3.d j
          ((h3RawFinPressureRealC1OfPath W) t)) := by
    unfold SpatialC3 at hGradC3
    exact hGradC3.of_le (by norm_num)

  have hEq :
      spatial3.d a
          (spatial3.d j
            ((h3RawFinPressureRealC1OfPath W) t))
        =
      (fun x : Point3 => - spatial3.d a F x) := by
    funext x

    have hGrad :=
      hGradC1.hasDerivAt_coordinateLine_spatial_d x a

    have hNegGrad := hGrad.neg

    have hForceTrace :
        HasDerivAt
          (fun r : ℝ =>
            F (coordinateLine x a r))
          (-(spatial3.d a
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t))
            x))
          (x a) := by
      dsimp only [F]
      unfold PrimeTensor.Bridge.RealFluid.pressureForceComponent
      change
        HasDerivAt
          (-(fun r : ℝ =>
            spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t)
              (coordinateLine x a r)))
          (-(spatial3.d a
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) t))
            x))
          (x a)
      exact hNegGrad

    have hForceValue :
        spatial3.d a F x
          =
        -(spatial3.d a
          (spatial3.d j
            ((h3RawFinPressureRealC1OfPath W) t))
          x) := by
      change partialDeriv a F x = _
      exact partialDeriv_eq_of_hasDerivAt hForceTrace

    linarith

  rw [hEq]
  exact hNeg

end

end Euclidean
end Bridge
end PrimeTensor
