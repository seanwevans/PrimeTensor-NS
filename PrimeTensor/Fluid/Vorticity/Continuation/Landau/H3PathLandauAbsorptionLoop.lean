import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathExactDissipativeBalance

/-!
# The current Landau transport estimate loops back to sqrt-energy integrability

The exact dissipative balance reduced the remaining coercive question to

    -T_H3(t) ≤ D(t) + c(t) E(t)

with an integrable coefficient `c`.

This file records what the *existing* Landau transport closure supplies when
combined with the sharp spectral gradient envelope

    |∇u(t)| ≤ C₁ sqrt(E(t)).

The present commutator theorem gives

    -T_H3(t)
      ≤ 4422 * (1 + C₁ sqrt(E(t))) * E(t).

Since `D(t) ≥ 0`, this is an absorption estimate with

    c(t) = 4422 * (1 + C₁ sqrt(E(t))).

On a finite terminal interval, the constant part is integrable.  Therefore the
integrability of this `c` follows from exactly the already-isolated condition

    sqrt(E) ∈ L¹.

So retaining the exact viscous dissipation does not, by itself, improve the
temporal continuation criterion while the transport term is estimated only by
the current `L∞` gradient commutator bound.  A genuine advance must sharpen the
transport estimate so that part of `D` is used *inside* the nonlinear estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The coefficient produced by the current Landau commutator estimate after
inserting the canonical square-root H³ gradient envelope. -/
noncomputable def h3PathCanonicalLandauTransportCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    4422
      *
    (
      1
        +
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t)
    )

theorem h3PathCanonicalLandauTransportCoefficient_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathCanonicalLandauTransportCoefficient u t := by

  unfold h3PathCanonicalLandauTransportCoefficient

  have hC :
      0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hS :
      0 ≤ Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_nonneg _

  positivity

/-- Pointwise, the current Landau commutator closure gives the generic
transport/dissipation absorption interface with the canonical coefficient. -/
theorem h3TransportDissipationAbsorptionAt_of_currentLandau
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3TransportDissipationAbsorptionAt
      u
      (h3PathCanonicalLandauTransportCoefficient u)
      t := by

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

  have hTransport :=
    neg_transport_le_of_commutatorBound
      (hTransportTail t ht).2

  have hEnvelopeNonneg :
      0 ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
          *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)

  have hTransportCanonical :
      - velocityH3TransportDerivativeAt u t
        ≤
      h3PathCanonicalLandauTransportCoefficient u t
        *
      velocityH3EnergyAt u t := by

    dsimp only [
      h,
      h3PathCanonicalSqrtEnergyGradientEnvelope
    ] at hTransport

    rw [abs_of_nonneg hEnvelopeNonneg] at hTransport

    simpa only [
      h3PathCanonicalLandauTransportCoefficient
    ] using hTransport

  have hD :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  unfold H3TransportDissipationAbsorptionAt

  linarith

/-- If `sqrt(E_H3)` is integrable on a finite energy-class tail, then the
coefficient produced by the current Landau transport estimate is integrable on
that same tail. -/
theorem h3PathCanonicalLandauTransportCoefficient_integrableOn_of_sqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T)) :
    MeasureTheory.IntegrableOn
      (h3PathCanonicalLandauTransportCoefficient u)
      (Set.Ioo a T) := by

  have hOneInterval :
      IntervalIntegrable
        (fun _ : ℝ => (1 : ℝ))
        volume
        a T :=
    intervalIntegrable_const

  have hOne :
      MeasureTheory.IntegrableOn
        (fun _ : ℝ => (1 : ℝ))
        (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_of_lt hClass.terminal_start.2)).1
      hOneInterval

  have hScaled :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
            *
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) :=
    hSqrt.const_mul
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hSum :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          1
            +
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
            *
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) :=
    hOne.add hScaled

  have hCoefficient :=
    hSum.const_mul (4422 : ℝ)

  change
    MeasureTheory.Integrable
      (fun t : ℝ =>
        4422
          *
        (
          1
            +
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
            *
          Real.sqrt (velocityH3EnergyAt u t)
        ))
      ((volume : Measure ℝ).restrict (Set.Ioo a T))

  exact hCoefficient

/-- The previously isolated universal sqrt-energy integrability statement
implies the new transport/dissipation absorption frontier through the *current*
Landau estimate.  Thus this route has not yet reduced the genuine temporal
difficulty. -/
theorem h3PathEnergyClassProducesTransportDissipationAbsorption_of_sqrtEnergyIntegrable
    (hSqrt :
      H3PathSqrtEnergyIntegrableOnPreterminal) :
    H3PathEnergyClassProducesTransportDissipationAbsorption := by

  intro u T hH3 a hClass

  have hSqrtFull :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo (0 : ℝ) T) :=
    hSqrt u T hH3

  have hSqrtTail :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) := by

    apply hSqrtFull.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hClass.terminal_start.1 ht.1,
        ht.2
      ⟩

  refine
    ⟨
      h3PathCanonicalLandauTransportCoefficient u,
      h3PathCanonicalLandauTransportCoefficient_integrableOn_of_sqrtEnergy
        hClass hSqrtTail,
      ?_
    ⟩

  intro t ht

  exact
    h3TransportDissipationAbsorptionAt_of_currentLandau
      hH3 hClass ht

end

end Euclidean
end Bridge
end PrimeTensor
