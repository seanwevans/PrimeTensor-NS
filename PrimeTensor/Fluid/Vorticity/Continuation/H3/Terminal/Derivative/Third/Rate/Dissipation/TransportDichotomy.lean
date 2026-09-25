import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Eventual
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact

/-!
# Terminal dissipation versus transport/energy-decay dichotomy

The eventual top-dissipation theorem proves that hypothetical nonextension
forces

    1 ≤ A(t) D₃(t)³,

where

    A(t) = 81 K⁸ (T - t)⁸ E₀(b).

The exact H³ balance is

    E'(t) + 2 D(t) = -T_H3(t),

and the full dissipation dominates its top block,

    D₃(t) ≤ D(t).

Consequently, at every strict H³ energy-class time there is a pointwise
alternative:

    E'(t) ≤ -D₃(t)

or

    D₃(t) ≤ -T_H3(t).

Indeed, if the energy is not decreasing at least as fast as `D₃`, then the
exact transport term must pay for at least one full copy of `D₃`.

On the eventual nonextension tail the already-forced cubic dissipation rate
therefore transfers to one of two quantities:

    1 ≤ A(t) (-E'(t))³

or

    1 ≤ A(t) (-T_H3(t))³.

This is deliberately neutral.  Large top dissipation does not by itself force
large transport, because rapid negative energy derivative remains an
algebraically valid alternative in the exact balance.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Full dissipation dominates the top block -/

theorem velocityH3Dissipation3At_le_dissipationAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3Dissipation3At u t
      ≤
    velocityH3DissipationAt u t := by

  have h0 :=
    velocityH3Dissipation0At_nonneg u t

  have h1 :=
    velocityH3Dissipation1At_nonneg u t

  have h2 :=
    velocityH3Dissipation2At_nonneg u t

  unfold velocityH3DissipationAt

  linarith

/-! ## Exact pointwise balance dichotomy -/

/--
At every strict H³ energy-class time, either the total H³ energy decreases by
at least one top-dissipation block, or the negative transport derivative
dominates that top block.
-/
theorem deriv_energy_le_neg_dissipation3_or_dissipation3_le_neg_transport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
        ≤
      - velocityH3Dissipation3At u t
      ∨
    velocityH3Dissipation3At u t
        ≤
      - velocityH3TransportDerivativeAt u t := by

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hTop :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  by_cases hDecay :
      deriv (velocityH3EnergyAt u) t
        ≤
      - velocityH3Dissipation3At u t

  · exact Or.inl hDecay

  · right

    have hDecayStrict :
        - velocityH3Dissipation3At u t
          <
        deriv (velocityH3EnergyAt u) t := by
      exact lt_of_not_ge hDecay

    linarith

/-! ## Propagate a cubic D₃ rate through the exact dichotomy -/

/--
Any cubic lower rate carried by `D₃` transfers, through the exact balance, to
either the negative energy derivative or the negative transport derivative.
-/
theorem cubic_dissipation3_rate_implies_energyDecay_or_transport_rate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hA : 0 ≤ A)
    (hRate :
      1
        ≤
      A * velocityH3Dissipation3At u t ^ 3) :
    (
      1
        ≤
      A
        *
      (- deriv (velocityH3EnergyAt u) t) ^ 3
    )
      ∨
    (
      1
        ≤
      A
        *
      (- velocityH3TransportDerivativeAt u t) ^ 3
    ) := by

  have hD3 :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  rcases
    deriv_energy_le_neg_dissipation3_or_dissipation3_le_neg_transport
      hH3
      hClass
      ht
    with hDecay | hTransport

  · left

    have hDom :
        velocityH3Dissipation3At u t
          ≤
        - deriv (velocityH3EnergyAt u) t := by
      linarith

    have hCube :
        velocityH3Dissipation3At u t ^ 3
          ≤
        (- deriv (velocityH3EnergyAt u) t) ^ 3 :=
      pow_le_pow_left₀
        hD3
        hDom
        3

    exact
      le_trans
        hRate
        (mul_le_mul_of_nonneg_left
          hCube
          hA)

  · right

    have hCube :
        velocityH3Dissipation3At u t ^ 3
          ≤
        (- velocityH3TransportDerivativeAt u t) ^ 3 :=
      pow_le_pow_left₀
        hD3
        hTransport
        3

    exact
      le_trans
        hRate
        (mul_le_mul_of_nonneg_left
          hCube
          hA)

/-! ## Eventual quantitative dichotomy under nonextension -/

/--
On a sufficiently late terminal interval, hypothetical nonextension forces
either an inverse-scale negative energy derivative or an inverse-scale negative
transport derivative at every time.

The common division-free coefficient is

    A(t) = 81 K⁸ (T - t)⁸ E₀(b).
-/
theorem exists_terminalTail_energyDecay_or_transportRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        (
          1
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            (T - t) ^ 8
              *
            velocityH3Energy0At u b
          )
            *
          (- deriv (velocityH3EnergyAt u) t) ^ 3
        )
          ∨
        (
          1
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            (T - t) ^ 8
              *
            velocityH3Energy0At u b
          )
            *
          (- velocityH3TransportDerivativeAt u t) ^ 3
        ) := by

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  have htAnchor :
      t ∈ Set.Ioo b T :=
    ⟨
      lt_trans hc.1 ht.1,
      ht.2
    ⟩

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 htAnchor.1,
      htAnchor.2
    ⟩

  let A : ℝ :=
    81
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 8
      *
    (T - t) ^ 8
      *
    velocityH3Energy0At u b

  have hA :
      0 ≤ A := by

    have hE0 :
        0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg
        u b

    dsimp only [A]
    positivity

  have hRateA :
      1
        ≤
      A * velocityH3Dissipation3At u t ^ 3 := by

    dsimp only [A]

    simpa only [mul_assoc] using
      (hRate t ht)

  have hAlternative :=
    cubic_dissipation3_rate_implies_energyDecay_or_transport_rate
      hH3
      hClass
      htClass
      hA
      hRateA

  simpa only [A] using hAlternative

/--
Canonical midpoint-anchor specialization of the eventual exact-balance
dichotomy.
-/
theorem exists_terminalTail_energyDecay_or_transportRate_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈
        Set.Ioo
          (h3BKMKineticTailMidpoint a T)
          T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        (
          1
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            (T - t) ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          (- deriv (velocityH3EnergyAt u) t) ^ 3
        )
          ∨
        (
          1
            ≤
          (
            81
              *
            h3PathSqrtEnergyRiccatiCoefficient ^ 8
              *
            (T - t) ^ 8
              *
            velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
          )
            *
          (- velocityH3TransportDerivativeAt u t) ^ 3
        ) := by

  exact
    exists_terminalTail_energyDecay_or_transportRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
