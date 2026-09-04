import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayVariationOfConstantsRawFourierAmplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.L2.Bridge

/-!
# Classicalization: quotient-safe L² variation of constants

The pointwise all-frequency variation-of-constants formula now uses the same
named raw Fourier Duhamel amplitude that represents exact H³ deweighting of the
Banach-valued Duhamel state almost everywhere.

This file crosses the remaining quotient boundary.

At positive time, the linear heat term has an explicit raw Fourier
representative whose canonical `L²` package is exactly the deweighted weighted
spectral heat state.  The nonlinear amplitude is already known to represent the
deweighted Duhamel state almost everywhere.  Combining those two
representative statements with the pointwise variation-of-constants identity
gives an equality of actual Fourier `L²` classes.

No representative is evaluated to define an `L²` state; pointwise identities
are used only under almost-everywhere extensionality.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayVariationOfConstantsRawFourierL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The deweighted `L²` state of positive-time weighted spectral heat evolution
has the explicit raw heat multiplier as an almost-everywhere representative. -/
theorem h3SpectralScalarRawFourierL2_heatApplyNN_ae_rawRepresentative
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    ((h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) G) :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarHeatRawRepresentative ν t G := by
  rw [
    ← h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
      hν ht G
  ]
  exact
    h3SpectralScalarHeatRawRepresentativeL2_ae
      hν ht G

/-- Coordinatewise variation of constants as an equality of genuine raw
Fourier `L²` classes.  The linear term is the exact deweighting of weighted
spectral heat evolution and the nonlinear term is exact deweighting of the
Banach-valued Duhamel state. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_rawFourierL2
    {ν t M : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (hM : 0 ≤ M)
    (W : ℝ → H3SpectralFinVectorState)
    (hWcont : Continuous W)
    (hW : ∀ s : ℝ, ‖W s‖ ≤ M)
    (hFContinuous :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt ν ξ W s)
    (hWeightedForcing :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              •
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ)
          volume
          0
          t)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2 (W t i)
      =
    h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (W 0 i))
      -
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayDuhamel
        ν t hν W W i) := by
  have hVOC :=
    h3FinHeatLerayVariationOfConstants_retarded_rawAmplitude
      ht.le W hFContinuous hODE hWeightedForcing

  have hFinal :=
    h3SpectralScalarRawFourierL2_ae (W t i)

  have hHeat :=
    h3SpectralScalarRawFourierL2_heatApplyNN_ae_rawRepresentative
      hν ht (W 0 i)

  have hDuhamel :=
    h3SpectralFinHeatLerayDuhamel_rawFourierL2_ae_eq_rawAmplitude
      hν ht.le hM hM W W
      hWcont hWcont hW hW i

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hFinal,
    hHeat,
    hDuhamel,
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) (W 0 i)))
      (h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          ν t hν W W i))
  ] with ξ hFinalξ hHeatξ hDuhamelξ hSubξ

  simp only [Pi.sub_apply] at hSubξ

  rw [hFinalξ, hSubξ, hHeatξ, hDuhamelξ]

  unfold h3SpectralScalarHeatRawRepresentative

  exact congrFun (congrFun hVOC i) ξ

end

end Euclidean
end Bridge
end PrimeTensor
