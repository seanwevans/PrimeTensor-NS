import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.TransportHarmonicSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportDichotomy

/-!
# Sharp cubic adverse-transport rate on positive H³-energy growth times

The eventual top-order dissipation estimate under hypothetical nonextension is

    1 ≤ A(t) D₃(t)^3,

where

    A(t) =
      81 K^8 (T-t)^8 E₀(b).

At any strict energy-class time with nonnegative raw H³-energy derivative,
exact balance gives

    -T_H3(t) = E'(t) + 2 D(t) ≥ 2 D(t) ≥ 2 D₃(t).

Cubing and using `A(t) ≥ 0` yields the sharper transport rate

    8 ≤ A(t) (-T_H3(t))^3.

This is the division-free form of an inverse-`8/3` adverse-transport scale.
No cube roots are needed in Lean.

The derivative blowup sequence constructed earlier is eventually positive and
eventually enters the dissipation-rate tail, so the same sharp cubic transport
rate holds eventually along that sequence.

These remain necessary conditions on a hypothetical nonextension branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise cubic transfer through exact balance -/

/--
If `D₃` carries a cubic lower rate with nonnegative coefficient `A`, then at
any time of nonnegative H³-energy growth the adverse transport carries eight
times that rate.

The factor `8` is exactly the cube of the factor `2` in the exact H³ balance.
-/
theorem eight_le_cubic_negativeTransport_of_cubic_dissipation3_rate_of_nonnegative_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hA : 0 ≤ A)
    (hDerivative :
      0 ≤ deriv (velocityH3EnergyAt u) t)
    (hRate :
      1
        ≤
      A * velocityH3Dissipation3At u t ^ 3) :
    8
      ≤
    A * (- velocityH3TransportDerivativeAt u t) ^ 3 := by

  have hD3 :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  have hTop :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClass
      ht

  have hTwiceD3 :
      2 * velocityH3Dissipation3At u t
        ≤
      - velocityH3TransportDerivativeAt u t := by

    linarith

  have hTwiceD3Nonneg :
      0 ≤ 2 * velocityH3Dissipation3At u t := by

    positivity

  have hCube :
      (2 * velocityH3Dissipation3At u t) ^ 3
        ≤
      (- velocityH3TransportDerivativeAt u t) ^ 3 :=
    pow_le_pow_left₀
      hTwiceD3Nonneg
      hTwiceD3
      3

  have hScaledCube :
      A * (2 * velocityH3Dissipation3At u t) ^ 3
        ≤
      A * (- velocityH3TransportDerivativeAt u t) ^ 3 :=
    mul_le_mul_of_nonneg_left
      hCube
      hA

  have hRateEight :
      8
        ≤
      8 * (A * velocityH3Dissipation3At u t ^ 3) := by

    nlinarith [hRate]

  have hAlgebra :
      8 * (A * velocityH3Dissipation3At u t ^ 3)
        =
      A * (2 * velocityH3Dissipation3At u t) ^ 3 := by
    ring

  rw [hAlgebra] at hRateEight

  exact
    le_trans
      hRateEight
      hScaledCube

/-! ## Eventual sharp transport rate -/

/--
On a sufficiently late terminal interval, hypothetical nonextension forces the
sharp cubic adverse-transport rate at every time where the raw H³-energy
derivative is nonnegative.
-/
theorem exists_terminalTail_eight_le_negativeTransport_cubicRate_of_nonnegative_deriv_of_noH3PathExtension
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
        0 ≤ deriv (velocityH3EnergyAt u) t →
        8
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
        (- velocityH3TransportDerivativeAt u t) ^ 3 := by

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

  intro t ht hDerivative

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

  have hTransportRate :=
    eight_le_cubic_negativeTransport_of_cubic_dissipation3_rate_of_nonnegative_deriv
      hH3
      hClass
      htClass
      hA
      hDerivative
      hRateA

  simpa only [A] using
    hTransportRate

/--
Canonical midpoint-anchor specialization of the sharp cubic transport rate.
-/
theorem exists_terminalTail_eight_le_negativeTransport_cubicRate_midpoint_of_nonnegative_deriv_of_noH3PathExtension
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
        0 ≤ deriv (velocityH3EnergyAt u) t →
        8
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
        (- velocityH3TransportDerivativeAt u t) ^ 3 := by

  exact
    exists_terminalTail_eight_le_negativeTransport_cubicRate_of_nonnegative_deriv_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

/-! ## Sharp cubic rate along the positive-derivative blowup sequence -/

/--
The positive-derivative terminal sequence eventually satisfies the sharp
division-free inverse-`8/3` adverse-transport rate.
-/
theorem exists_deriv_blowupSequence_eventually_eight_le_negativeTransport_cubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            deriv (velocityH3EnergyAt u) (σ n)
        )
        atTop
        atTop
        ∧
      ∀ᶠ n : ℕ in atTop,
        8
          ≤
        (
          81
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 8
            *
          (T - σ n) ^ 8
            *
          velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T)
        )
          *
        (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨c, hc, hRate⟩ :=
    exists_terminalTail_eight_le_negativeTransport_cubicRate_midpoint_of_nonnegative_deriv_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hSigmaAboveC :
      ∀ᶠ n : ℕ in atTop,
        c < σ n :=
    (tendsto_order.1 hSigmaTendsto).1
      c
      hc.2

  have hDerivativePositive :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ deriv (velocityH3EnergyAt u) (σ n) :=
    hDerivativeTendsto.eventually
      (eventually_ge_atTop 0)

  have hEventuallyRate :
      ∀ᶠ n : ℕ in atTop,
        8
          ≤
        (
          81
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 8
            *
          (T - σ n) ^ 8
            *
          velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T)
        )
          *
        (- velocityH3TransportDerivativeAt u (σ n)) ^ 3 := by

    filter_upwards
      [
        hSigmaAboveC,
        hDerivativePositive
      ]
      with n hcn hDerivative

    have hTail :
        σ n ∈ Set.Ioo c T :=
      ⟨
        hcn,
        (hσ n).1.2
      ⟩

    exact
      hRate
        (σ n)
        hTail
        hDerivative

  exact
    ⟨
      σ,
      (fun n => (hσ n).1),
      hSigmaTendsto,
      hDerivativeTendsto,
      hEventuallyRate
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
