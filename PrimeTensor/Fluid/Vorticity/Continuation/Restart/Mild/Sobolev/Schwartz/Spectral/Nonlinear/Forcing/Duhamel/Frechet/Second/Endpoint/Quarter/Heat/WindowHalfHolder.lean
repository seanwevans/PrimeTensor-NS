import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.UniformHalfHolder

/-!
# Two-time positive-window half-Hölder heat estimate

`Quarter.Heat.UniformHalfHolder` is stated as a base time plus a nonnegative
increment.  Downstream endpoint arguments naturally use two source/target
times `s ≤ t`.  This file repackages the same estimate in that form on a fixed
positive window `δ ≤ s ≤ t`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Scalar two-time half-Hölder estimate on a positive heat window. -/
theorem norm_h3SpectralScalarHeatApplyNN_sub_le_halfHolder_onPositiveWindow
    {ν δ s t : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδs : δ ≤ s)
    (hst : s ≤ t)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) G‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖G‖) *
      Real.sqrt (t - s) := by
  have hs : 0 < s := lt_of_lt_of_le hδ hδs
  have hh : 0 ≤ t - s := sub_nonneg.mpr hst

  have hMain :=
    norm_h3SpectralScalarHeatApplyNN_add_sub_le_halfHolder_uniformPositiveLag
      hν hδ hδs hh G

  simpa only [show s + (t - s) = t by ring] using hMain

/-- Scalar endpoint-oriented version of the positive-window estimate. -/
theorem norm_h3SpectralScalarHeatApplyNN_sub_rev_le_halfHolder_onPositiveWindow
    {ν δ s t : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδs : δ ≤ s)
    (hst : s ≤ t)
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) G‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖G‖) *
      Real.sqrt (t - s) := by
  calc
    ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) G‖
        =
      ‖h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) G -
        h3SpectralScalarHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) G‖ := by
            exact norm_sub_rev _ _
    _ ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖G‖) *
        Real.sqrt (t - s) :=
      norm_h3SpectralScalarHeatApplyNN_sub_le_halfHolder_onPositiveWindow
        hν hδ hδs hst G

/-- Velocity two-time half-Hölder estimate on a positive heat window. -/
theorem norm_h3SpectralVelocityHeatApplyNN_sub_le_halfHolder_onPositiveWindow
    {ν δ s t : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδs : δ ≤ s)
    (hst : s ≤ t)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) U‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖U‖) *
      Real.sqrt (t - s) := by
  have hs : 0 < s := lt_of_lt_of_le hδ hδs
  have hh : 0 ≤ t - s := sub_nonneg.mpr hst

  have hMain :=
    norm_h3SpectralVelocityHeatApplyNN_add_sub_le_halfHolder_uniformPositiveLag
      hν hδ hδs hh U

  simpa only [show s + (t - s) = t by ring] using hMain

/-- Velocity endpoint-oriented version of the positive-window estimate. -/
theorem norm_h3SpectralVelocityHeatApplyNN_sub_rev_le_halfHolder_onPositiveWindow
    {ν δ s t : ℝ}
    (hν : 0 < ν)
    (hδ : 0 < δ)
    (hδs : δ ≤ s)
    (hst : s ≤ t)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) U‖
      ≤
    (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖U‖) *
      Real.sqrt (t - s) := by
  calc
    ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) U‖
        =
      ‖h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t (le_trans (le_trans hδ.le hδs) hst)) U -
        h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk s (le_trans hδ.le hδs)) U‖ := by
            exact norm_sub_rev _ _
    _ ≤
      (h3HeatPositiveLagHalfHolderCoefficient ν δ * ‖U‖) *
        Real.sqrt (t - s) :=
      norm_h3SpectralVelocityHeatApplyNN_sub_le_halfHolder_onPositiveWindow
        hν hδ hδs hst U

end

end Euclidean
end Bridge
end PrimeTensor
