import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyDissipationCascade
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Total.Closure

/-!
# Full-energy normalized terminal H³ cascade

The preceding full-tail cascade proves, under hypothetical nonextension,

    E₃(t) -> +∞,
    D₃(t) / E₃(t) -> +∞,
    D(t) / E₃(t) -> +∞.

This file transfers those statements from the top energy block `E₃` to the
full normalized H³ energy

    E(t) = velocityH3EnergyAt u t.

The key point is not merely the lower bound `E₃ ≤ E`.  The endpoint Fourier
interpolation theorem gives the reverse comparison up to a fixed terminal-tail
constant:

    E(t) ≤ 1 + 3 (E₀(t) + E₃(t)).

On a strict terminal tail the kinetic block is antitone, hence

    E₀(t) ≤ E₀(b).

Since `E₃(t) -> +∞`, eventually `1 ≤ E₃(t)`, and therefore

    E(t)
      ≤
    (4 + 3 E₀(b)) E₃(t).

Thus the full H³ energy and its top block are eventually comparable up to a
fixed positive coefficient.  Consequently hypothetical nonextension forces

    E(t) -> +∞,
    D₃(t) / E(t) -> +∞,
    D(t) / E(t) -> +∞

along the entire left terminal neighborhood.

These are necessary consequences of hypothetical nonextension.  No singular
branch is asserted to exist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Full H³ energy divergence -/

/--
Since the third-order block is a nonnegative summand of the full normalized
H³ energy, full-tail divergence of `E₃` forces full-tail divergence of `E`.
-/
theorem velocityH3EnergyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (velocityH3EnergyAt u)
      (𝓝[<] T)
      atTop := by

  have hE3 :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ velocityH3Energy3At u t :=
    hE3.eventually
      (eventually_ge_atTop M)

  filter_upwards
    [hEventually]
    with t ht

  exact
    le_trans
      ht
      (
        velocityH3Energy3At_le_velocityH3EnergyAt
          u t
      )

/-! ## Eventual comparison of E and E₃ -/

/--
For any fixed strict anchor `b`, hypothetical nonextension forces the full H³
energy eventually to satisfy

    E(t) ≤ (4 + 3 E₀(b)) E₃(t).

The coefficient is fixed in time.
-/
theorem eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3EnergyAt u t
        ≤
      (
        4
          +
        3 * velocityH3Energy0At u b
      )
        *
      velocityH3Energy3At u t := by

  have hE3Tendsto :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hE3One :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        1 ≤ velocityH3Energy3At u t :=
    hE3Tendsto.eventually
      (eventually_ge_atTop 1)

  have hTail :
      Set.Ioo b T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT
      hb.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hE0Anchor :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  filter_upwards
    [
      hE3One,
      hTail
    ]
    with t hThirdOne htTail

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 htTail.1,
      htTail.2
    ⟩

  have hE0Bound :
      velocityH3Energy0At u t
        ≤
      velocityH3Energy0At u b :=
    hKineticAnti
      hb
      htClass
      (le_of_lt htTail.1)

  have hEndpoint :
      velocityH3EnergyAt u t
        ≤
      1
        +
      3
        *
      (
        velocityH3Energy0At u t
          +
        velocityH3Energy3At u t
      ) :=
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
      hH3
      hClass
      htClass

  have hCoeffNonneg :
      0
        ≤
      1 + 3 * velocityH3Energy0At u b := by
    linarith

  have hThirdMinusOne :
      0
        ≤
      velocityH3Energy3At u t - 1 := by
    linarith

  have hProduct :
      0
        ≤
      (
        1
          +
        3 * velocityH3Energy0At u b
      )
        *
      (
        velocityH3Energy3At u t
          -
        1
      ) :=
    mul_nonneg
      hCoeffNonneg
      hThirdMinusOne

  nlinarith

/-! ## Full-energy normalized top dissipation -/

/--
Hypothetical nonextension forces

    D₃(t) / E(t) -> +∞

along the entire left terminal neighborhood.
-/
theorem velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (
        fun t : ℝ =>
          velocityH3Dissipation3At u t
            /
          velocityH3EnergyAt u t
      )
      (𝓝[<] T)
      atTop := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  have hE0Anchor :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hCPos :
      0 < C := by

    dsimp only [C]

    linarith

  have hUpper :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3EnergyAt u t
          ≤
        C * velocityH3Energy3At u t := by

    dsimp only [C]

    exact
      eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb

  have hTopRatio :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hE3Tendsto :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  by_cases hM :
      M ≤ 0

  · exact
      Eventually.of_forall
        (
          fun t =>
            le_trans
              hM
              (
                div_nonneg
                  (velocityH3Dissipation3At_nonneg
                    u t)
                  (
                    le_trans
                      (by norm_num : (0 : ℝ) ≤ 1)
                      (one_le_velocityH3EnergyAt
                        u t)
                  )
              )
        )

  · have hMPos :
        0 < M :=
      lt_of_not_ge
        hM

    have hRatioEventually :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          M * C
            ≤
          velocityH3Dissipation3At u t
            /
          velocityH3Energy3At u t :=
      hTopRatio.eventually
        (eventually_ge_atTop (M * C))

    have hE3One :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          1 ≤ velocityH3Energy3At u t :=
      hE3Tendsto.eventually
        (eventually_ge_atTop 1)

    filter_upwards
      [
        hRatioEventually,
        hE3One,
        hUpper
      ]
      with t hRatio hThirdOne hEnergyUpper

    have hThirdPos :
        0 < velocityH3Energy3At u t := by
      linarith

    have hEnergyPos :
        0 < velocityH3EnergyAt u t := by
      have hOne :=
        one_le_velocityH3EnergyAt
          u t
      linarith

    have hTopLower :
        (M * C) * velocityH3Energy3At u t
          ≤
        velocityH3Dissipation3At u t :=
      (le_div_iff₀ hThirdPos).1
        hRatio

    have hScaledEnergy :
        M * velocityH3EnergyAt u t
          ≤
        M * (C * velocityH3Energy3At u t) :=
      mul_le_mul_of_nonneg_left
        hEnergyUpper
        (le_of_lt hMPos)

    have hLinear :
        M * velocityH3EnergyAt u t
          ≤
        velocityH3Dissipation3At u t := by

      calc
        M * velocityH3EnergyAt u t
            ≤
          M * (C * velocityH3Energy3At u t) :=
          hScaledEnergy

        _ =
          (M * C) * velocityH3Energy3At u t := by
          ring

        _ ≤
          velocityH3Dissipation3At u t :=
          hTopLower

    exact
      (le_div_iff₀ hEnergyPos).2
        hLinear

/-! ## Full-energy normalized full dissipation -/

/--
Because `D₃ ≤ D`, hypothetical nonextension also forces

    D(t) / E(t) -> +∞

along the full left terminal neighborhood.
-/
theorem velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (
        fun t : ℝ =>
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
      )
      (𝓝[<] T)
      atTop := by

  have hTopRatio :=
    velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M
          ≤
        velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t :=
    hTopRatio.eventually
      (eventually_ge_atTop M)

  filter_upwards
    [hEventually]
    with t ht

  have hEnergyNonneg :
      0 ≤ velocityH3EnergyAt u t := by

    have hOne :=
      one_le_velocityH3EnergyAt
        u t

    linarith

  have hTop :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  have hRatio :
      velocityH3Dissipation3At u t
          /
        velocityH3EnergyAt u t
        ≤
      velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t :=
    div_le_div_of_nonneg_right
      hTop
      hEnergyNonneg

  exact
    le_trans
      ht
      hRatio

/-! ## Neutral full-energy cascade package -/

/--
Neutral full-energy terminal package.

Either smooth continuation exists across `T`, or along the full left terminal
neighborhood all three canonical full-energy statements hold:

* `E -> +∞`;
* `D₃/E -> +∞`;
* `D/E -> +∞`.

The theorem does not select a branch.
-/
theorem smoothContinuationExtension_or_full_h3_energy_normalized_cascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      Tendsto
        (velocityH3EnergyAt u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (
          fun t : ℝ =>
            velocityH3Dissipation3At u t
              /
            velocityH3EnergyAt u t
        )
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (
          fun t : ℝ =>
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
        )
        (𝓝[<] T)
        atTop
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        ⟨
          velocityH3EnergyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3Dissipation3At_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
