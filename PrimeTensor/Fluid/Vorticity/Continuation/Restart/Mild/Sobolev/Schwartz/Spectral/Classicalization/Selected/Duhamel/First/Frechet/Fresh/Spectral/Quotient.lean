import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Spectral.Duhamel.Coordinate.Bridge

/-!
# Classicalization: spectral first-Fréchet fresh quotient

The selected fresh-tail limit was first closed for the literal classical
retarded derivative integral,

    h⁻¹ • ∫ₜ^{t+h} D_a K(t+h,s,x) ds
      ⟶
    D_a N(W(t),W(t))(x).

The generic spectral Duhamel coordinate bridge now identifies the coordinate
`fderiv` of an H³-valued Duhamel state with the corresponding source-time
retarded derivative integral.

Apply that bridge to the shifted paths

    r ↦ W(r+t)

on the short interval `0..h`.  Translation invariance of the interval integral
then sends `r` to `s = r+t`, producing exactly the literal fresh integral on
`t..t+h`.

Consequently the *actual spectral fresh remainder* appearing in the exact
first-Fréchet quotient split has the same normalized right limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetFreshSpectralQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The normalized coordinate `fderiv` of the actual shifted spectral H³
fresh Duhamel remainder converges from the right to the instantaneous forcing
coordinate derivative. -/
theorem tendsto_inv_smul_h3SelectedDuhamelFresh_fderiv_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν h hν
                  (fun r => W (r + t))
                  (fun r => W (r + t))
                  i))
              x) ea))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x) ea)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ r : ℝ, ‖W r‖ ≤ 2 * A := by
    intro r
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ r

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hShiftCont :
      Continuous (fun r : ℝ => W (r + t)) := by
    exact
      hWcont.comp
        (continuous_id.add continuous_const)

  have hShiftBound :
      ∀ r : ℝ, ‖W (r + t)‖ ≤ 2 * A := by
    intro r
    exact hWbound (r + t)

  have hLiteral :=
    tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a x

  have hLiteral' :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ •
            (∫ s in t..t + h,
              h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
                ν (t + h) W W i x s ea))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          ((fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W t) (W t) i)
              x) ea)) := by
    simpa only [W, ea] using hLiteral

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν h hν
                  (fun r => W (r + t))
                  (fun r => W (r + t))
                  i))
              x) ea))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
              ν (t + h) W W i x s ea)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh

    have hSpec :=
      h3SpectralFinHeatLerayDuhamel_C1_fderiv_coordinate_eq_intervalIntegral
        hν hh.le h2A h2A
        (fun r : ℝ => W (r + t))
        (fun r : ℝ => W (r + t))
        hShiftCont hShiftCont
        hShiftBound hShiftBound
        i a x

    let F : ℝ → ℂ :=
      fun s =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν (t + h) W W i a x s

    have hPoint :
        ∀ r : ℝ,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν h
              (fun q => W (q + t))
              (fun q => W (q + t))
              i a x r
            =
          F (r + t) := by
      intro r
      dsimp only [F]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      congr 1 <;> ring

    have hTranslate :
        (∫ r in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν h
            (fun q => W (q + t))
            (fun q => W (q + t))
            i a x r)
          =
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν (t + h) W W i a x s := by
      calc
        (∫ r in (0 : ℝ)..h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν h
            (fun q => W (q + t))
            (fun q => W (q + t))
            i a x r)
            =
          ∫ r in (0 : ℝ)..h, F (r + t) := by
            apply intervalIntegral.integral_congr_uIoo
            intro r hr
            exact hPoint r
        _ =
          ∫ s in (0 : ℝ) + t..h + t, F s := by
            rw [intervalIntegral.integral_comp_add_right]
        _ =
          ∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν (t + h) W W i a x s := by
            dsimp only [F]
            congr 1 <;> ring

    have hAxisIntegral :
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν (t + h) W W i a x s)
          =
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
            ν (t + h) W W i x s ea := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      dsimp only [ea]
      exact
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_axis
          ν (t + h) W W i a x s).symm

    have hFresh :
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (h3SpectralFinHeatLerayDuhamel
                ν h hν
                (fun r => W (r + t))
                (fun r => W (r + t))
                i))
            x) ea
          =
        ∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
            ν (t + h) W W i x s ea := by
      exact hSpec.trans (hTranslate.trans hAxisIntegral)

    rw [hFresh]

  exact
    Tendsto.congr'
      hEq.symm
      hLiteral'

end

end Euclidean
end Bridge
end PrimeTensor
