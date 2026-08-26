import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Semigroup

/-!
# Quarter-power heat increments of a positive-lag Duhamel kernel

A retarded heat--Leray kernel already carries positive heat time.  Splitting a
positive lag `τ` into two equal pieces writes

    K_τ(U,V) = H_{τ/2}(K_{τ/2}(U,V)).

The quarter-Hölder heat-state estimate can therefore be applied to the outer
half of the heat evolution.  The remaining `K_{τ/2}` factor is controlled by
the standard heat--Leray kernel estimate.

This gives the pointwise history estimate needed before integrating the old
part of the Duhamel term in time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- Scalar majorant for the quarter-power heat increment of a positive-lag
heat--Leray kernel. -/
noncomputable def h3DuhamelQuarterHistoryKernelMajorant
    (ν τ h MU MV : ℝ) : ℝ :=
  h3HeatQuarterIncrementCoefficient ν (τ / 2) h *
    (288 * h3SobolevDeweightingConstant *
      (Real.sqrt (ν * (τ / 2)))⁻¹ * MU * MV)

/-- A positive-lag heat--Leray kernel is quarter-Hölder under an additional
nonnegative heat evolution. -/
theorem norm_h3SpectralVelocityHeatApplyNN_heatLerayVelocityApply_sub_le_quarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (h : NNReal)
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V) -
        h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V‖
      ≤
    h3DuhamelQuarterHistoryKernelMajorant
      ν τ (h : ℝ) ‖U‖ ‖V‖ := by
  let τ₂ : ℝ := τ / 2
  have hτ₂ : 0 < τ₂ := by
    dsimp only [τ₂]
    linarith

  let a₂ : NNReal := ⟨τ₂, hτ₂.le⟩
  let K₂ : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayVelocityApply ν τ₂ hν hτ₂ U V

  have hsplit : τ₂ + τ₂ = τ := by
    dsimp only [τ₂]
    ring

  have hKernelSplit :
      h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V
        =
      h3SpectralVelocityHeatApplyNN ν hν.le a₂ K₂ := by
    let Kpos : {r : ℝ // 0 < r} → H3SpectralFinVectorState :=
      fun q =>
        h3SpectralFinHeatLerayVelocityApply
          ν q.1 hν q.2 U V
    have hsum : 0 < τ₂ + τ₂ :=
      add_pos_of_pos_of_nonneg hτ₂ hτ₂.le
    have hq :
        (⟨τ, hτ⟩ : {r : ℝ // 0 < r}) =
          ⟨τ₂ + τ₂, hsum⟩ := by
      apply Subtype.ext
      exact hsplit.symm
    have htransport :
        h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V =
          h3SpectralFinHeatLerayVelocityApply
            ν (τ₂ + τ₂) hν hsum U V := by
      change Kpos ⟨τ, hτ⟩ = Kpos ⟨τ₂ + τ₂, hsum⟩
      rw [hq]
    calc
      h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V
          = h3SpectralFinHeatLerayVelocityApply
              ν (τ₂ + τ₂) hν hsum U V := htransport
      _ = h3SpectralVelocityHeatApplyNN ν hν.le a₂ K₂ := by
        exact
          h3SpectralFinHeatLerayVelocityApply_add_time
            (ν := ν) (a := τ₂) (b := τ₂)
            hν hτ₂ hτ₂.le U V

  have ha₂ : 0 < (a₂ : ℝ) := by
    change 0 < τ₂
    exact hτ₂

  have hState :
      ‖h3SpectralVelocityHeatApplyNN ν hν.le (a₂ + h) K₂ -
          h3SpectralVelocityHeatApplyNN ν hν.le a₂ K₂‖
        ≤
      h3HeatQuarterIncrementCoefficient
          ν (a₂ : ℝ) (h : ℝ) * ‖K₂‖ :=
    norm_h3SpectralVelocityHeatApplyNN_add_sub_le_quarter
      hν a₂ h ha₂ K₂

  have hK₂ :
      ‖K₂‖ ≤
        288 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * τ₂))⁻¹ * ‖U‖ * ‖V‖ := by
    dsimp only [K₂]
    exact
      norm_h3SpectralFinHeatLerayVelocityApply_le
        hν hτ₂ U V

  have hQ :
      0 ≤
        h3HeatQuarterIncrementCoefficient
          ν τ₂ (h : ℝ) :=
    h3HeatQuarterIncrementCoefficient_nonneg
      hν.le hτ₂.le h.property

  rw [hKernelSplit]
  rw [← h3SpectralVelocityHeatApplyNN_add_time
    ν hν.le a₂ h K₂]

  calc
    ‖h3SpectralVelocityHeatApplyNN ν hν.le (a₂ + h) K₂ -
        h3SpectralVelocityHeatApplyNN ν hν.le a₂ K₂‖
        ≤
      h3HeatQuarterIncrementCoefficient
          ν (a₂ : ℝ) (h : ℝ) * ‖K₂‖ := hState
    _ ≤
      h3HeatQuarterIncrementCoefficient
          ν τ₂ (h : ℝ) *
        (288 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * τ₂))⁻¹ * ‖U‖ * ‖V‖) := by
      have hcoe : (a₂ : ℝ) = τ₂ := rfl
      rw [hcoe]
      exact mul_le_mul_of_nonneg_left hK₂ hQ
    _ =
      h3DuhamelQuarterHistoryKernelMajorant
        ν τ (h : ℝ) ‖U‖ ‖V‖ := by
      simp only [h3DuhamelQuarterHistoryKernelMajorant, τ₂]

end

end Euclidean
end Bridge
end PrimeTensor
