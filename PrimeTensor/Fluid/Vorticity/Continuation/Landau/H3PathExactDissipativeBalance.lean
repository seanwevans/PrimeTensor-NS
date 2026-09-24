import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathRetainedDissipationGrowth

/-!
# Exact dissipative H³ balance on an admissible path

The retained-dissipation estimate still passed through the coarse transport
commutator bound.  The exact Navier--Stokes energy split is stronger.

On every strict H³ energy-class slice:

* the canonical H³ derivative identity is closed;
* all PDE pairings are integrable;
* pressure cancels exactly;
* diffusion is exactly `-2 * velocityH3DissipationAt`.

Therefore

    E'(t) + 2 D(t) = - T_H3(t),

where `T_H3` is the exact full H³ transport derivative.

This is the natural next frontier.  Global closure no longer asks for any
energy differentiation, pressure, or diffusion theorem.  It asks for a
transport estimate strong enough to be absorbed by the exact viscous
dissipation, up to a lower-order integrable remainder.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Exact H³ energy-dissipation-transport balance. -/
theorem deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
        + 2 * velocityH3DissipationAt u t
      =
    - velocityH3TransportDerivativeAt u t := by

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

  rw [hPressure, hDiffusion] at hSplit

  linarith

/--
Pointwise transport absorption with one copy of the exact dissipation and a
lower-order scalar coefficient.

This is the useful coercive target:

    -T_H3(t) ≤ D(t) + c(t) E(t).

Inserted into the exact balance, it leaves one positive copy of the
dissipation on the left and only linear energy growth on the right.
-/
def H3TransportDissipationAbsorptionAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (c : ℝ → ℝ)
    (t : ℝ) : Prop :=
  - velocityH3TransportDerivativeAt u t
    ≤
  velocityH3DissipationAt u t
    + c t * velocityH3EnergyAt u t

/-- Exact balance plus transport absorption gives the coercive linear-growth
inequality `E' + D ≤ c E`. -/
theorem deriv_velocityH3EnergyAt_add_dissipation_le_of_transportAbsorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAbsorb : H3TransportDissipationAbsorptionAt u c t) :
    deriv (velocityH3EnergyAt u) t
        + velocityH3DissipationAt u t
      ≤
    c t * velocityH3EnergyAt u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht

  unfold H3TransportDissipationAbsorptionAt at hAbsorb

  linarith

/-- Dropping the remaining nonnegative dissipation gives ordinary linear
energy growth once transport has been absorbed. -/
theorem deriv_velocityH3EnergyAt_le_of_transportAbsorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAbsorb : H3TransportDissipationAbsorptionAt u c t) :
    deriv (velocityH3EnergyAt u) t
      ≤
    c t * velocityH3EnergyAt u t := by

  have hCoercive :=
    deriv_velocityH3EnergyAt_add_dissipation_le_of_transportAbsorption
      hH3 hClass ht hAbsorb

  have hD :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  linarith

/-- Tail-level formulation of the remaining coercive transport frontier. -/
def H3PathEnergyClassProducesTransportDissipationAbsorption : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∃ c : ℝ → ℝ,
            MeasureTheory.IntegrableOn c (Set.Ioo a T)
              ∧
            ∀ t : ℝ,
              t ∈ Set.Ioo a T →
                H3TransportDissipationAbsorptionAt u c t

end

end Euclidean
end Bridge
end PrimeTensor
