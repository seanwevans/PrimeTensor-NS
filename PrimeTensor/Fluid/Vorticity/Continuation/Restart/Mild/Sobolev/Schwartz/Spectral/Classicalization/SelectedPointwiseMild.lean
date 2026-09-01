import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedClassicalDuhamel
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityThirdJetContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Real.C3.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Physical.Solution

/-!
# Pointwise mild identity for the selected restart velocity

The selected Banach path already satisfies the exact signed spectral mild
equation at every physical time in the restart interval.

`SelectedClassicalDuhamel` now supplies the missing nonlinear
classicalization: the canonical selected Duhamel reconstruction is literally
the classical retarded integral at every spatial point.

This file transports the spectral mild equation through the canonical H³
inverse-Fourier representative.

There are four bookkeeping steps.

* The generic H³ `C¹` representative of a positive-time heat-evolved state is
  identified exactly with the already-named heat `C³` representative.
* The physical-time mild equation is specialized to the canonical H³ restart
  radius.
* Coordinate projection and inverse-Fourier linearity give an exact complex
  pointwise mild equation.
* Taking real parts and transporting to `Point3` gives the corresponding
  selected real-velocity component identity.

No `L²` point evaluation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedPointwiseMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The generic arbitrary-H³ classical representative of a positive-time heat
state is exactly the named positive-time heat `C³` representative. -/
theorem h3SpectralScalarC1Representative_heatApplyNN_eq_heatC3Representative
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    h3SpectralScalarC1Representative
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) G)
      =
    h3SpectralScalarHeatC3Representative ν t G := by
  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk t ht.le) G

  have hGeneric :=
    h3SpectralScalarRawFourierL2_ae H

  have hHeat :=
    h3SpectralScalarHeatRawRepresentativeL2_ae
      hν ht G

  have hL2Eq :=
    h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
      hν ht G

  have hCoeEq :
      (((h3SpectralScalarRawFourierL2 H :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
        =
      (((h3SpectralScalarHeatRawRepresentativeL2
          ν t hν ht G :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)) := by
    exact
      congrArg
        (fun Z : H3FourierComplexL2 =>
          ((Z : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ))
        hL2Eq.symm

  have hRaw :
      h3SpectralScalarRawFourier H
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative ν t G := by
    filter_upwards [hGeneric, hHeat] with ξ hGenericξ hHeatξ
    exact
      hGenericξ.symm.trans
        ((congrFun hCoeEq ξ).trans hHeatξ)

  funext x
  unfold h3SpectralScalarC1Representative
  unfold h3SpectralScalarHeatC3Representative
  exact
    _root_.Real.fourierInv_congr_ae hRaw x

/-- The Banach-selected path satisfies the exact signed spectral mild equation
at every nonnegative time inside the canonical restart radius. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_satisfies_mild_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht) U₀
      -
    h3SpectralFinHeatLerayDuhamel
        ν t hν W W
      =
    W t := by
  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let q : Set.Icc (0 : ℝ) R :=
    ⟨t, ht, by simpa only [R] using htR⟩

  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact
      (h3FinHeatLerayRestartRadius_pos ν hA).le

  have hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt R
        ≤ 1 := by
    dsimp only [R]
    exact
      h3FinHeatLerayRestartRadius_smallness ν hA.le

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      (ν := ν)
      (τ := R)
      (A := A)
      hν hR0 U₀ hA hU₀ hsmall q

  rw [h3SpectralFinHeatLerayPhysicalMildSolution_apply] at hMild

  change
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht) U₀
      -
    h3SpectralFinHeatLerayDuhamel
        ν t hν W W
      =
    W t
    at hMild

  exact hMild

/-- At every strict positive time inside the canonical restart radius, each
selected spectral coordinate satisfies the literal pointwise classical mild
identity. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
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
    h3SpectralScalarC1Representative (W t i)
      =
    h3SpectralScalarHeatC3Representative
        ν t (U₀ i)
      -
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_satisfies_mild_at
      hν U₀ hA hU₀ ht.le htR

  dsimp only at hMild

  have hCoord0 :=
    congrArg
      (fun V : H3SpectralFinVectorState => V i)
      hMild

  have hCoord :
      h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (U₀ i)
        -
      h3SpectralFinHeatLerayDuhamel
          ν t hν W W i
        =
      W t i := by
    change
      h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (U₀ i)
        -
      h3SpectralFinHeatLerayDuhamel
          ν t hν W W i
        =
      W t i
      at hCoord0
    exact hCoord0

  have hRep :=
    congrArg h3SpectralScalarC1Representative hCoord

  rw [h3SpectralScalarC1Representative_sub] at hRep

  have hHeat :
      h3SpectralScalarC1Representative
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (U₀ i))
        =
      h3SpectralScalarHeatC3Representative
        ν t (U₀ i) :=
    h3SpectralScalarC1Representative_heatApplyNN_eq_heatC3Representative
      hν ht (U₀ i)

  have hSelectedGeneric :=
    h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
      hν U₀ hA hU₀ ht i

  have hSelectedClassical :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  dsimp only at hSelectedGeneric hSelectedClassical

  have hDuhamel :
      h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν t hν W W i)
        =
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i :=
    hSelectedGeneric.symm.trans hSelectedClassical

  calc
    h3SpectralScalarC1Representative (W t i)
        =
      h3SpectralScalarC1Representative
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (U₀ i))
        -
      h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν t hν W W i) :=
      hRep.symm
    _ =
      h3SpectralScalarHeatC3Representative
          ν t (U₀ i)
        -
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i := by
      rw [hHeat, hDuhamel]

/-- Real `Point3` form of the selected coordinatewise mild identity. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_mild_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (W t i) x
      =
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3
        ν t (U₀ i) x
      -
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let y : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  have hComplex :=
    congrFun
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ ht htR i)
      y

  have hReal :=
    congrArg Complex.re hComplex

  unfold h3SpectralScalarRealC1RepresentativeOnPoint3
  unfold h3SpectralScalarRealC1Representative
  unfold h3SpectralScalarHeatRealC3RepresentativeOnPoint3
  unfold h3SpectralScalarHeatRealC3Representative

  simpa only [W, y, Pi.sub_apply, Complex.sub_re] using hReal

/-- Intrinsic-axis form: the selected real velocity itself satisfies the
classical pointwise mild identity componentwise on the positive restart
window. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_mild_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let i : Fin 3 :=
      h3ClassicalizationFinOfAxis j
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hA hU₀ t x).component j
      =
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3
        ν t (U₀ i) x
      -
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  change
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (W t i) x
      =
    h3SpectralScalarHeatRealC3RepresentativeOnPoint3
        ν t (U₀ i) x
      -
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_mild_at
      hν U₀ hA hU₀ ht htR i x

end

end Euclidean
end Bridge
end PrimeTensor
