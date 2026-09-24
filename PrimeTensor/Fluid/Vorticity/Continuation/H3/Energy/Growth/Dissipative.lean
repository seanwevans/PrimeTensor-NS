import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Dissipation

/-!
# Retain the exact H³ viscous dissipation in the scalar growth inequality

The previous autonomous estimate discarded the viscous term after proving only

    velocityH3DiffusionDerivativeAt u t ≤ 0.

The exact diffusion identity is stronger:

    velocityH3DiffusionDerivativeAt u t
      = -2 * velocityH3DissipationAt u t.

Combining that identity with the already-closed exact PDE split, pressure
cancellation, transport commutator estimate, and the sharp square-root-energy
gradient envelope gives

    E'(t) + 2 D(t)
      ≤ 4422 * (1 + C₁ sqrt(E(t))) * E(t).

Since `E(t) ≥ 1`, this also implies

    E'(t) + 2 D(t)
      ≤ K * sqrt(E(t)) * E(t),

with the same Riccati coefficient introduced previously.

This is the correct coercive form of the current scalar estimate.  No
dissipation magnitude is discarded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Exact closed H³ growth with the positive viscous dissipation retained on
the left-hand side. -/
theorem deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergyGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
        + 2 * velocityH3DissipationAt u t
      ≤
    4422
      *
    (
      1 +
        abs
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
          )
    )
      *
    velocityH3EnergyAt u t := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hDerivativeAt :
      H3OrderEnergyDerivativeIdentities u t :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass t ht

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have hHigher :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p
        t := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht

  have hPDEPairing :
      H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
        u T hH3 a hClass t ht

  have hSplit :
      deriv (velocityH3EnergyAt u) t
        =
      velocityH3DiffusionDerivativeAt u t
        -
      velocityH3TransportDerivativeAt u t
        -
      velocityH3PressureDerivativeAt u p t :=
    deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure
      hPDE
      htAbs
      hDerivativeAt
      hHigher
      hPDEPairing

  have hPressure :
      velocityH3PressureDerivativeAt u p t = 0 := by
    dsimp only [p]
    exact
      h3PathEnergyClassProducesPressureCancellation_closed
        u T hH3 a hClass t ht

  have hDiffusion :
      velocityH3DiffusionDerivativeAt u t
        =
      -2 * velocityH3DissipationAt u t :=
    h3Path_velocityH3DiffusionDerivativeAt_eq_neg_two_mul_dissipation_closed
      hH3 hClass ht

  let h : ℝ → ℝ :=
    h3PathCanonicalSqrtEnergyGradientEnvelope u

  have hGradient :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h s := by
    intro s hs
    dsimp only [h]
    exact
      h3PathCanonicalSqrtEnergyGradientEnvelope_at
        hH3 hClass hs

  have hTransportTail :
      H3TransportControlledOnTail
        u a T h 4422 :=
    h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3
      hClass
      hGradient

  have hTransport :
      -
        velocityH3TransportDerivativeAt u t
        ≤
      4422
        * (1 + |h t|)
        * velocityH3EnergyAt u t :=
    neg_transport_le_of_commutatorBound
      (hTransportTail t ht).2

  rw [hSplit, hPressure, hDiffusion]

  dsimp only [
    h,
    h3PathCanonicalSqrtEnergyGradientEnvelope
  ] at hTransport ⊢

  linarith

/-- Riccati-normalized retained-dissipation inequality. -/
theorem deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
        + 2 * velocityH3DissipationAt u t
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t)
      *
    velocityH3EnergyAt u t := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  let E : ℝ :=
    velocityH3EnergyAt u t

  have hRaw :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergyGrowth
      hH3 hClass ht

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hEOne :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3EnergyAt u t

  have hENonneg :
      0 ≤ E := by
    linarith

  have hSqrtNonneg :
      0 ≤ Real.sqrt E :=
    Real.sqrt_nonneg E

  have hSqrtOne :
      1 ≤ Real.sqrt E := by
    have h :=
      Real.sqrt_le_sqrt hEOne
    simpa only [Real.sqrt_one] using h

  have hFactor :
      1 + C * Real.sqrt E
        ≤
      (C + 1) * Real.sqrt E := by
    nlinarith

  have hAbs :
      abs
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
          )
        =
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by
    exact
      abs_of_nonneg
        (mul_nonneg
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
          (Real.sqrt_nonneg _))

  have hRaw' :
      deriv (velocityH3EnergyAt u) t
          + 2 * velocityH3DissipationAt u t
        ≤
      4422
        *
      (1 + C * Real.sqrt E)
        *
      E := by
    rw [hAbs] at hRaw
    simpa only [C, E] using hRaw

  calc
    deriv (velocityH3EnergyAt u) t
        + 2 * velocityH3DissipationAt u t
        ≤
      4422
        *
      (1 + C * Real.sqrt E)
        *
      E :=
      hRaw'

    _ ≤
      4422
        *
      ((C + 1) * Real.sqrt E)
        *
      E := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            hFactor
            (by norm_num))
          hENonneg

    _ =
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t)
        *
      velocityH3EnergyAt u t := by
      dsimp only [
        h3PathSqrtEnergyRiccatiCoefficient,
        C,
        E
      ]
      ring

/-- A pointwise absorption inequality against the exact viscous dissipation
would force nonincrease of the canonical H³ energy at that time. -/
theorem deriv_velocityH3EnergyAt_nonpos_of_dissipation_absorbs_sqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAbsorb :
      h3PathSqrtEnergyRiccatiCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t)
          *
        velocityH3EnergyAt u t
        ≤
      2 * velocityH3DissipationAt u t) :
    deriv (velocityH3EnergyAt u) t ≤ 0 := by

  have hGrowth :=
    deriv_velocityH3EnergyAt_add_two_dissipation_le_sqrtEnergy_mul_energy
      hH3 hClass ht

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
