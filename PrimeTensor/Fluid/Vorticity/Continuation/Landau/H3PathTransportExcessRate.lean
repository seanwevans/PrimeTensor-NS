import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTransportAbsorptionContinuation

/-!
# Minimal transport excess rate

The mixed coercive continuation frontier is

    -T_H3(t) ≤ D_H3(t) + c(t) E_H3(t),

with an integrable nonnegative coefficient `c`.

Because the normalized canonical H³ energy always satisfies `E_H3(t) ≥ 1`,
there is a canonical *minimal* nonnegative coefficient:

    q(t) = max(0, (-T_H3(t) - D_H3(t)) / E_H3(t)).

It has three useful properties:

1. `q(t) ≥ 0`;
2. `-T_H3(t) ≤ D_H3(t) + q(t) E_H3(t)`;
3. every other nonnegative coefficient satisfying the same absorption
   inequality is at least `q(t)`.

Thus the remaining global H³-path problem can be stated with no existential
majorant at all: prove that this explicit scalar excess rate is integrable on
each terminal energy-class tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The exact positive part of transport growth left after spending one copy
of the H³ viscous dissipation, normalized by the positive H³ energy. -/
noncomputable def h3PathTransportExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (
        (
          - velocityH3TransportDerivativeAt u t
            - velocityH3DissipationAt u t
        )
          /
        velocityH3EnergyAt u t
      )

theorem h3PathTransportExcessRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathTransportExcessRate u t := by
  unfold h3PathTransportExcessRate
  exact le_max_left _ _

/-- The canonical excess rate always supplies the exact mixed
transport/dissipation absorption inequality. -/
theorem h3TransportDissipationAbsorptionAt_transportExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    H3TransportDissipationAbsorptionAt
      u
      (h3PathTransportExcessRate u)
      t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hDiv :
      (
        - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t
        ≤
      h3PathTransportExcessRate u t := by

    unfold h3PathTransportExcessRate

    exact
      le_max_right
        0
        (
          (
            - velocityH3TransportDerivativeAt u t
              - velocityH3DissipationAt u t
          )
            /
          velocityH3EnergyAt u t
        )

  have hScaled :
      - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
        ≤
      h3PathTransportExcessRate u t
        * velocityH3EnergyAt u t := by

    exact
      (div_le_iff₀ hEPos).1
        hDiv

  unfold H3TransportDissipationAbsorptionAt

  linarith

/-- Minimality: every nonnegative absorption coefficient dominates the
canonical transport excess rate pointwise. -/
theorem h3PathTransportExcessRate_le_of_absorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {c : ℝ → ℝ}
    {t : ℝ}
    (hc : 0 ≤ c t)
    (hAbsorb :
      H3TransportDissipationAbsorptionAt u c t) :
    h3PathTransportExcessRate u t ≤ c t := by

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hNumerator :
      - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
        ≤
      c t * velocityH3EnergyAt u t := by

    unfold H3TransportDissipationAbsorptionAt at hAbsorb

    linarith

  have hDiv :
      (
        - velocityH3TransportDerivativeAt u t
          - velocityH3DissipationAt u t
      )
        /
      velocityH3EnergyAt u t
        ≤
      c t := by

    exact
      (div_le_iff₀ hEPos).2
        hNumerator

  unfold h3PathTransportExcessRate

  exact
    max_le
      hc
      hDiv

/-- Explicit scalar version of the remaining coercive frontier. -/
def H3PathEnergyClassProducesIntegrableTransportExcessRate : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          MeasureTheory.IntegrableOn
            (h3PathTransportExcessRate u)
            (Set.Ioo a T)

/-- Integrability of the explicit minimal excess rate discharges the previous
existential transport/dissipation absorption frontier. -/
theorem h3PathEnergyClassProducesTransportDissipationAbsorption_of_integrableExcessRate
    (hRate :
      H3PathEnergyClassProducesIntegrableTransportExcessRate) :
    H3PathEnergyClassProducesTransportDissipationAbsorption := by

  intro u T hH3 a hClass

  refine
    ⟨
      h3PathTransportExcessRate u,
      hRate u T hH3 a hClass,
      ?_
    ⟩

  intro t ht

  exact
    h3TransportDissipationAbsorptionAt_transportExcessRate
      u t

/-- The explicit scalar excess-rate frontier is sufficient for smooth
continuation of every admissible H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_integrableTransportExcessRate
    (hRate :
      H3PathEnergyClassProducesIntegrableTransportExcessRate) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  exact
    everyH3PathPreterminalNavierStokesSolutionExtends_of_transportDissipationAbsorption
      (h3PathEnergyClassProducesTransportDissipationAbsorption_of_integrableExcessRate
        hRate)

/-- Contrapositive: failure of H³-path continuation forces failure of the
universal integrability statement for the explicit transport excess rate. -/
theorem not_integrableTransportExcessRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ H3PathEnergyClassProducesIntegrableTransportExcessRate := by

  intro hRate

  exact
    hNoExtension
      (
        everyH3PathPreterminalNavierStokesSolutionExtends_of_integrableTransportExcessRate
          hRate
          u T hH3
      )

end

end Euclidean
end Bridge
end PrimeTensor
