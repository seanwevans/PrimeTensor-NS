import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryHeatC1Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Cocycle

/-!
# Selected Duhamel diagonal C¹ cocycle

The old-history heat orbit has now been identified exactly with the canonical
`C¹` representative of the spectrally heat-evolved selected Duhamel state.

This file pushes the exact spectral Duhamel cocycle through the canonical
pointwise `C¹` reconstruction.

There are two bookkeeping steps.

First, the arbitrary-H³ `C¹` reconstruction is additive.  This is proved
quotient-safely: the chosen `L²` representatives of `G + H`, `G`, and `H`
satisfy the expected addition identity almost everywhere; deweighting
preserves that identity; and ordinary inverse Fourier additivity upgrades it
to an exact pointwise equality.

Second, specialize the spectral Duhamel cocycle to

    a = 0,  b = t,  c = h.

Coordinatewise this says

    D_spec(t+h)
      = H_h D_spec(t) + D_spec^fresh(t,h).

Applying the exact `C¹` additivity theorem and the landed history-heat bridge
gives

    C1(D_spec(t+h))
      = oldHistoryHeat(h) + C1(D_spec^fresh(t,h)).

Thus the only remaining representation boundary before the actual diagonal
difference quotient is the fresh shifted spectral remainder.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3DuhamelDiagonalC1Cocycle
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical pointwise `C¹` reconstruction of arbitrary spectral H³
scalar states is exactly additive. -/
theorem h3SpectralScalarC1Representative_add
    (G H : H3SpectralScalarState) :
    h3SpectralScalarC1Representative (G + H)
      =
    h3SpectralScalarC1Representative G
      +
    h3SpectralScalarC1Representative H := by
  have hRaw :
      h3SpectralScalarRawFourier (G + H)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (h3SpectralScalarRawFourier G
        +
      h3SpectralScalarRawFourier H) := by
    filter_upwards [MeasureTheory.Lp.coeFn_add G H] with ξ hξ
    unfold h3SpectralScalarRawFourier
    simp only [Pi.add_apply] at hξ ⊢
    rw [hξ]
    ring

  have hG :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hH :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  funext x

  have hInvRaw :
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier (G + H)) x
        =
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier G
            + h3SpectralScalarRawFourier H) x :=
    _root_.Real.fourierInv_congr_ae hRaw x

  have hInvAdd :
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier G
            + h3SpectralScalarRawFourier H) x
        =
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier G) x
        +
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier H) x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (h3SpectralScalarRawFourier G
            + h3SpectralScalarRawFourier H)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (h3SpectralScalarRawFourier G)
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (h3SpectralScalarRawFourier H)
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hG
          hH)
        x

  unfold h3SpectralScalarC1Representative
  exact hInvRaw.trans hInvAdd

/-- Coordinatewise selected Duhamel cocycle after canonical `C¹`
reconstruction, with the old-history heat term replaced by its explicit
physical representative. -/
theorem h3SelectedDuhamelC1Representative_add_time_eq_history_add_fresh
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let Dt : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let Dfresh : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν h hν
        (fun r => W (r + t))
        (fun r => W (r + t))
        i
    h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayDuhamel
          ν (t + h) hν W W i)
      =
    h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i
      +
    h3SpectralScalarC1Representative Dfresh := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Dt : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let Dfresh : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν h hν
      (fun r => W (r + t))
      (fun r => W (r + t))
      i

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hSpec :=
    h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
      (a := (0 : ℝ))
      hν ht hh h2A h2A W W
      hWcont hWcont hWbound hWbound

  have hCoord :
      h3SpectralFinHeatLerayDuhamel
          ν (t + h) hν W W i
        =
      h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk h hh.le) Dt
        +
      Dfresh := by
    have hi := congrFun hSpec i
    dsimp only [Dt, Dfresh]
    simpa only [
      add_zero,
      Pi.add_apply,
      h3SpectralVelocityHeatApplyNN_apply
    ] using hi

  have hC1 :=
    congrArg h3SpectralScalarC1Representative hCoord

  rw [h3SpectralScalarC1Representative_add] at hC1

  have hHistory :=
    h3SelectedDuhamelHistoryHeatRepresentative_eq_spectralScalarC1Representative_heatApplyNN
      (h := h)
      hν U₀ hA hU₀ ht hh i

  dsimp only [W, Dt] at hHistory
  dsimp only [Dt, Dfresh] at hC1 ⊢

  rw [← hHistory] at hC1
  exact hC1

end

end Euclidean
end Bridge
end PrimeTensor
