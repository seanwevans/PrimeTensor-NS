import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayVariationOfConstantsRawFourierL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.RawL2Shift
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Algebra

/-!
# Classicalization: reconstruct the H³ variation-of-constants state

The previous checkpoint proves variation of constants after exact H³ deweighting
as an equality of genuine Fourier `L²` classes.

This file proves that exact deweighting is injective.  The proof does not appeal
to an abstract inverse operator: equality of the packaged raw `L²` classes gives
equality of their raw representatives almost everywhere, and the already-proved
pointwise reweighting identity recovers the original weighted H³ states.

Injectivity lifts the quotient-safe Fourier `L²` formula back to the actual
weighted spectral H³ state, first coordinatewise and then as the complete
three-component velocity state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayVariationOfConstantsState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact H³ deweighting into raw Fourier `L²` is injective. -/
theorem h3SpectralScalarRawFourierL2_injective :
    Function.Injective h3SpectralScalarRawFourierL2 := by
  intro F G h

  have hF :=
    h3SpectralScalarRawFourierL2_ae F
  have hG :=
    h3SpectralScalarRawFourierL2_ae G

  rw [h] at hF

  apply MeasureTheory.Lp.ext

  filter_upwards [hF, hG] with ξ hFξ hGξ

  have hRaw :
      h3SpectralScalarRawFourier F ξ
        =
      h3SpectralScalarRawFourier G ξ := by
    calc
      h3SpectralScalarRawFourier F ξ
          =
        (h3SpectralScalarRawFourierL2 G :
          H3FourierPoint3 → ℂ) ξ := hFξ.symm
      _ =
        h3SpectralScalarRawFourier G ξ := hGξ

  calc
    F ξ
        =
      (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SpectralScalarRawFourier F ξ := by
      symm
      exact
        h3SpectralScalarRawFourier_reweight_pointwise F ξ
    _ =
      (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SpectralScalarRawFourier G ξ := by
      rw [hRaw]
    _ = G ξ :=
      h3SpectralScalarRawFourier_reweight_pointwise G ξ

/-- Coordinatewise variation of constants lifted from raw Fourier `L²` back to
the actual weighted spectral H³ scalar state. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_state_coordinate
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
    W t i
      =
    h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (W 0 i)
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W i := by
  have hRaw :=
    h3FinHeatLerayVariationOfConstants_retarded_rawFourierL2
      hν ht hM W hWcont hW
      hFContinuous hODE hWeightedForcing i

  apply h3SpectralScalarRawFourierL2_injective

  calc
    h3SpectralScalarRawFourierL2 (W t i)
        =
      h3SpectralScalarRawFourierL2
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (W 0 i))
        -
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          ν t hν W W i) := hRaw
    _ =
      h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (W 0 i)
          -
         h3SpectralFinHeatLerayDuhamel
            ν t hν W W i) := by
      simpa only [h3SpectralScalarRawFourierL2CLM_apply] using
        (h3SpectralScalarRawFourierL2CLM.map_sub
          (h3SpectralScalarHeatApplyNN
            ν hν.le (NNReal.mk t ht.le) (W 0 i))
          (h3SpectralFinHeatLerayDuhamel
            ν t hν W W i)).symm

/-- Full three-component weighted spectral H³ variation of constants. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_state
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
          t) :
    W t
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (W 0)
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W := by
  funext i

  change
    W t i
      =
    h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (W 0 i)
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W i

  exact
    h3FinHeatLerayVariationOfConstants_retarded_state_coordinate
      hν ht hM W hWcont hW
      hFContinuous hODE hWeightedForcing i

end

end Euclidean
end Bridge
end PrimeTensor
