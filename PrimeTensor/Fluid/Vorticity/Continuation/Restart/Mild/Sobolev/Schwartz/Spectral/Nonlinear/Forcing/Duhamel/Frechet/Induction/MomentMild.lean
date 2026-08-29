import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentDuhamel
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdMildMass

/-!
# Fréchet endpoint induction: generic mild-state moment assembly

The complete selected Duhamel contribution is now exponent-parametric.  This
file removes the last exponent-specific bookkeeping in the mild decomposition.

At every positive restart time and for every nonnegative real exponent `p`,

    selected mild = free heat + selected Duhamel.

Therefore an integrable `p` moment on both summands gives an integrable `p`
moment on the named quotient-safe mild Fourier `L²` state, and independent
scalar budgets add.  The same conclusion is then transferred to the canonical
pointwise raw Fourier representative consumed by the nonlinear forcing layer.

This file is deliberately structural: it assumes the free-heat `p` moment as
an input rather than pretending that the existing order-three heat theorem is
already all-orders.  The next induction primitive proves that all-orders
free-heat statement separately.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic mild-state moment integrability from matching moments on the free
heat and complete selected Duhamel pieces. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integrable_of_heat_duhamel
    {p ν A t : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeat' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact hHeat

  have hDuhamel' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDuhamel

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖ +
            h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat'.add hDuhamel'

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hp).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable W).norm

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards [hRep] with ξ hξ

  have hw :
      0 ≤ h3FourierMomentWeight p ξ :=
    h3FourierMomentWeight_nonneg p ξ

  have hTarget0 :
      0 ≤ h3FourierMomentWeight p ξ * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTarget0]
  rw [hξ]

  calc
    h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖
        ≤
      h3FourierMomentWeight p ξ * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (D ξ))
        hw
    _ =
      h3FourierMomentWeight p ξ * ‖H ξ‖ +
        h3FourierMomentWeight p ξ * ‖D ξ‖ := by
      ring

/-- Quantitative generic mild-state moment estimate from independent free-heat
and complete-Duhamel budgets. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integral_le_of_heat_duhamel
    {p ν A t BHeat BDuhamel : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hHeatLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤ BHeat)
    (hDuhamelLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤ BDuhamel) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    BHeat + BDuhamel := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeat' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact hHeat

  have hDuhamel' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDuhamel

  have hFull :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_moment_integrable_of_heat_duhamel
        hp hν U₀ hA hU₀ ht htR i hHeat hDuhamel

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFull.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖ +
            h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat'.add hDuhamel'

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖
          ≤
        h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖D ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierMomentWeight p ξ :=
      h3FourierMomentWeight_nonneg p ξ

    calc
      h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖
          ≤
        h3FourierMomentWeight p ξ * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (D ξ))
          hw
      _ =
        h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖ :=
    integral_congr_ae hWeightedRep

  have hHeatLe' :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        ≤ BHeat := by
    dsimp only [H]
    exact hHeatLe

  have hDuhamelLe' :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        ≤ BDuhamel := by
    dsimp only [D]
    exact hDuhamelLe

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ‖) +
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖D ξ‖) := by
      rw [integral_add hHeat' hDuhamel']
    _ ≤
      BHeat + BDuhamel :=
      add_le_add hHeatLe' hDuhamelLe'

/-!
## Transfer to the canonical raw Fourier representative
-/

/-- The generic weighted density of the canonical selected mild raw Fourier
representative agrees almost everywhere with the named quotient-safe `L²`
package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_moment_ae_eq_rawFourierL2
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierMomentWeight p ξ *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierMomentWeight p ξ *
        ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ t i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := t)
      hν U₀ hA hU₀ i

  filter_upwards [hRep] with ξ hξ
  rw [← hξ]

/-- A generic moment proved on the named mild `L²` package transfers to the
canonical raw Fourier representative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_moment_integrable_of_L2
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hNamed :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                hν U₀ hA hU₀ t i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3)) :
    H3RawFourierMomentIntegrable
      p
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t i) := by
  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_moment_ae_eq_rawFourierL2
      (p := p) (t := t) hν U₀ hA hU₀ i

  unfold H3RawFourierMomentIntegrable
  exact hNamed.congr hEq.symm

/-- A quantitative generic moment bound on the named mild `L²` package
transfers unchanged to the canonical generic raw Fourier moment mass. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_momentMass_le_of_L2
    {p ν A t B : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hNamedLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                hν U₀ hA hU₀ t i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤ B) :
    h3SpectralScalarRawFourierMomentMass
        p
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ t i)
      ≤
    B := by
  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_moment_ae_eq_rawFourierL2
      (p := p) (t := t) hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierMomentMass
  rw [hIntegralEq]
  exact hNamedLe

end
end Euclidean
end Bridge
end PrimeTensor
