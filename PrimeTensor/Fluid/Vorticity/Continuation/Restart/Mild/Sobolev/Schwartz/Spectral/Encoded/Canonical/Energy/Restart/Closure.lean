import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Encoded.Restart.Radius.Closure

/-!
# Canonical-energy encoded restart closure

The encoded canonical-radius theorem previously required a separate solver-state
bound `‖U₀‖ ≤ A`.  The spectral encoder already proves the exact identity

    1 + ∑ j, ‖U₀ j‖² = velocityH3EnergyAt u t.

This file converts that identity into the sup-norm bound needed by the finite
heat--Leray solver.  Consequently a canonical H³ energy ceiling `E ≥ 1`
automatically supplies the solver bound with `A = E`, and hence the positive
restart radius and the full physically realized mild step.

This removes one more hypothesis between the project's canonical-energy local
well-posedness frontier and the spectral restart construction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

/-- A canonical H³ energy ceiling controls the finite-product spectral solver
norm.  We deliberately use the coarse bound `‖U₀‖ ≤ E`; for `E ≥ 1` this is
sufficient for the restart-radius construction and avoids an unnecessary
square-root normalization in downstream interfaces. -/
theorem norm_velocityH3SpectralStateAt_le_energyCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t E : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hE : 1 ≤ E)
    (hEnergy : velocityH3EnergyAt u t ≤ E) :
    ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ E := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier

  have hExact :
      1 + h3SpectralVelocitySquareEnergy U = velocityH3EnergyAt u t := by
    simpa only [U] using
      one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
        hFourier

  have hSquareEnergy :
      h3SpectralVelocitySquareEnergy U ≤ E - 1 := by
    linarith

  have hEnonneg : 0 ≤ E := by
    linarith

  change ‖U‖ ≤ E
  apply (pi_norm_le_iff_of_nonneg hEnonneg).2
  intro j

  have hCoordinateSquare :
      ‖U j‖ ^ 2 ≤ h3SpectralVelocitySquareEnergy U := by
    unfold h3SpectralVelocitySquareEnergy
    exact
      Finset.single_le_sum
        (fun i _ => sq_nonneg ‖U i‖)
        (Finset.mem_univ j)

  have hCoordinateSquareE : ‖U j‖ ^ 2 ≤ E := by
    linarith

  have hNormNonneg : 0 ≤ ‖U j‖ := norm_nonneg _
  have hShiftSquare : 0 ≤ (‖U j‖ - 1) ^ 2 := sq_nonneg _

  nlinarith

/-- Canonical-energy form of the encoded restart-radius closure.

No separate spectral norm bound is required: it follows from the exact
spectral-energy identity. -/
theorem h3SpectralEncodedCanonicalEnergyRestart_fullStep_realized
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hE : 1 ≤ E)
    (hEnergy : velocityH3EnergyAt u t ≤ E) :
    let hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
    let U₀ : H3SpectralVelocityState :=
      velocityH3SpectralStateAt u t hInt hMeas hFourier
    let T : NNReal := h3FinHeatLerayRestartRadiusNN ν E hEpos
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hEpos
          (norm_velocityH3SpectralStateAt_le_energyCeiling
            hFourier hE hEnergy)
    let R : H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν 0 hν W W T
    (∀ j : Fin 3,
      h3SpectralVelocityDecodeRealL2 U₀ j
        = h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))
      ∧
    (
      h3SpectralFinVectorDecodeComplexL2 (W (T : ℝ))
          = h3ComplexPhysicalVelocityHeatApplyNN ν hν.le T (W 0)
            + h3SpectralFinVectorDecodeComplexL2 R
        ∧
      h3SpectralFinVectorDecodeComplexL2 R
          ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
              ν (T : ℝ) hν
    ) := by
  dsimp only
  exact
    h3SpectralEncodedRestartRadius_fullStep_realized
      hν
      hFourier
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier hE hEnergy)

/-- The canonical energy ceiling also gives a concrete positive restart radius
without any solver-specific side condition. -/
theorem h3SpectralEncodedCanonicalEnergyRestartRadius_pos
    {ν E : ℝ}
    (hν : 0 < ν)
    (hE : 1 ≤ E) :
    0 < h3FinHeatLerayRestartRadius ν E := by
  exact
    h3FinHeatLerayRestartRadius_pos
      ν
      (lt_of_lt_of_le zero_lt_one hE)

end

end Euclidean
end Bridge
end PrimeTensor
