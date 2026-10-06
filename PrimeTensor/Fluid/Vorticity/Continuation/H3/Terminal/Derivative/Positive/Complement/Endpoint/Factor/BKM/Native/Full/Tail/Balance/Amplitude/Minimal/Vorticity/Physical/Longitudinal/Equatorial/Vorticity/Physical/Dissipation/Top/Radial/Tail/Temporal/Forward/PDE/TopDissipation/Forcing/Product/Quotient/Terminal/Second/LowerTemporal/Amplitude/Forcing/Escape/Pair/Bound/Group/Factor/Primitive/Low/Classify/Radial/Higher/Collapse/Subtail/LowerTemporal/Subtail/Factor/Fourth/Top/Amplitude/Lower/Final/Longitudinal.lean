import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Strong.H3
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Velocity.Energy.Boundedness

/-!
# Synchronize the final resolved-PDE witness with longitudinal spectral escape

The resolved-PDE scalar tree now yields one explicit terminal sequence on
which the total physical H³ energy diverges.

A surviving physical-vorticity strong-H³ endpoint at coordinate `i` already
gives strong-H³ endpoint control, hence eventual spectral H³ boundedness, for
both transverse velocity coordinates `j ≠ i`.

Therefore total H³-energy escape on any terminal sequence converging to `T`
from below must be carried by the same-index longitudinal velocity component.

This file performs that synchronization for the explicit final PDE-selected
sequence.  The result reconnects the completed PDE closure to the original
equatorial longitudinal obstruction on one common witness sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

/--
If total H³ energy diverges along a strict terminal sequence and one physical
vorticity component has a strong H³ endpoint, then the same-index longitudinal
velocity spectral H³ norm diverges along that very sequence.
-/
theorem longitudinalVelocityComponentSpectralNorm_tendstoAtTop_of_h3Energy_escape_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hEnergyTop :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ n))
        atTop atTop) :
    Tendsto
      (
        fun n : ℕ =>
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3
                i
                (τ n)
                ⟨
                  lt_trans hClass.terminal_start.1 (hτ n).1,
                  (hτ n).2
                ⟩
            )
      )
      atTop
      atTop := by

  fin_cases i

  · have hStrong1 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (1 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hStrong2 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (2 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain ⟨b1, B1, hb1T, hBound1⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong1

    obtain ⟨b2, B2, hb2T, hBound2⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong2

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0
    let B : ℝ := max R (max B1 B2)

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hR0 :
        0 ≤ R := by
      dsimp only [R]
      exact le_max_right M 0

    have hRLeB :
        R ≤ B := by
      dsimp only [B]
      exact le_max_left R (max B1 B2)

    have hB1Le :
        B1 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_left B1 B2)
          (le_max_right R (max B1 B2))

    have hB2Le :
        B2 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_right B1 B2)
          (le_max_right R (max B1 B2))

    have hB0 :
        0 ≤ B :=
      hR0.trans hRLeB

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          1 + 3 * B ^ 2
            <
          velocityH3EnergyAt u (τ n) :=
      hEnergyTop.eventually
        (eventually_gt_atTop (1 + 3 * B ^ 2))

    have hTime1 :
        ∀ᶠ n : ℕ in atTop,
          b1 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b1 hb1T

    have hTime2 :
        ∀ᶠ n : ℕ in atTop,
          b2 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b2 hb2T

    filter_upwards [hEnergyLarge, hTime1, hTime2] with n hnLarge hn1 hn2

    have ht :
        τ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1,
        (hτ n).2
      ⟩

    have hLong :
        R
          <
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 (0 : Fin 3) (τ n) ht
          ) := by

      by_contra hNot

      have hLongLe :
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3 (0 : Fin 3) (τ n) ht
            )
            ≤
          R :=
        le_of_not_gt hNot

      have hComponent :
          ∀ j : Fin 3,
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3 j (τ n) ht
              )
              ≤
            B := by

        intro j
        fin_cases j

        · exact
            hLongLe.trans hRLeB

        · exact
            (hBound1 (τ n) ht hn1).trans hB1Le

        · exact
            (hBound2 (τ n) ht hn2).trans hB2Le

      have hEnergyLe :
          velocityH3EnergyAt u (τ n)
            ≤
          1 + 3 * B ^ 2 :=
        velocityH3EnergyAt_le_one_add_three_mul_sq_of_terminalComponentNormBound
          hH3
          ht
          hB0
          hComponent

      exact
        (not_lt_of_ge hEnergyLe)
          hnLarge

    exact
      hMLe.trans
        (le_of_lt hLong)

  · have hStrong0 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (0 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hStrong2 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (2 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain ⟨b0, B0, hb0T, hBound0⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong0

    obtain ⟨b2, B2, hb2T, hBound2⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong2

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0
    let B : ℝ := max R (max B0 B2)

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hR0 :
        0 ≤ R := by
      dsimp only [R]
      exact le_max_right M 0

    have hRLeB :
        R ≤ B := by
      dsimp only [B]
      exact le_max_left R (max B0 B2)

    have hB0Le :
        B0 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_left B0 B2)
          (le_max_right R (max B0 B2))

    have hB2Le :
        B2 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_right B0 B2)
          (le_max_right R (max B0 B2))

    have hBnonneg :
        0 ≤ B :=
      hR0.trans hRLeB

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          1 + 3 * B ^ 2
            <
          velocityH3EnergyAt u (τ n) :=
      hEnergyTop.eventually
        (eventually_gt_atTop (1 + 3 * B ^ 2))

    have hTime0 :
        ∀ᶠ n : ℕ in atTop,
          b0 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b0 hb0T

    have hTime2 :
        ∀ᶠ n : ℕ in atTop,
          b2 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b2 hb2T

    filter_upwards [hEnergyLarge, hTime0, hTime2] with n hnLarge hn0 hn2

    have ht :
        τ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1,
        (hτ n).2
      ⟩

    have hLong :
        R
          <
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 (1 : Fin 3) (τ n) ht
          ) := by

      by_contra hNot

      have hLongLe :
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3 (1 : Fin 3) (τ n) ht
            )
            ≤
          R :=
        le_of_not_gt hNot

      have hComponent :
          ∀ j : Fin 3,
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3 j (τ n) ht
              )
              ≤
            B := by

        intro j
        fin_cases j

        · exact
            (hBound0 (τ n) ht hn0).trans hB0Le

        · exact
            hLongLe.trans hRLeB

        · exact
            (hBound2 (τ n) ht hn2).trans hB2Le

      have hEnergyLe :
          velocityH3EnergyAt u (τ n)
            ≤
          1 + 3 * B ^ 2 :=
        velocityH3EnergyAt_le_one_add_three_mul_sq_of_terminalComponentNormBound
          hH3
          ht
          hBnonneg
          hComponent

      exact
        (not_lt_of_ge hEnergyLe)
          hnLarge

    exact
      hMLe.trans
        (le_of_lt hLong)

  · have hStrong0 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (0 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hStrong1 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (1 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain ⟨b0, B0, hb0T, hBound0⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong0

    obtain ⟨b1, B1, hb1T, hBound1⟩ :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3 hStrong1

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 0
    let B : ℝ := max R (max B0 B1)

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 0

    have hR0 :
        0 ≤ R := by
      dsimp only [R]
      exact le_max_right M 0

    have hRLeB :
        R ≤ B := by
      dsimp only [B]
      exact le_max_left R (max B0 B1)

    have hB0Le :
        B0 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_left B0 B1)
          (le_max_right R (max B0 B1))

    have hB1Le :
        B1 ≤ B := by
      dsimp only [B]
      exact
        le_trans
          (le_max_right B0 B1)
          (le_max_right R (max B0 B1))

    have hBnonneg :
        0 ≤ B :=
      hR0.trans hRLeB

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          1 + 3 * B ^ 2
            <
          velocityH3EnergyAt u (τ n) :=
      hEnergyTop.eventually
        (eventually_gt_atTop (1 + 3 * B ^ 2))

    have hTime0 :
        ∀ᶠ n : ℕ in atTop,
          b0 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b0 hb0T

    have hTime1 :
        ∀ᶠ n : ℕ in atTop,
          b1 < τ n :=
      (tendsto_order.1 hTauTendsto).1 b1 hb1T

    filter_upwards [hEnergyLarge, hTime0, hTime1] with n hnLarge hn0 hn1

    have ht :
        τ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1,
        (hτ n).2
      ⟩

    have hLong :
        R
          <
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 (2 : Fin 3) (τ n) ht
          ) := by

      by_contra hNot

      have hLongLe :
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3 (2 : Fin 3) (τ n) ht
            )
            ≤
          R :=
        le_of_not_gt hNot

      have hComponent :
          ∀ j : Fin 3,
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3 j (τ n) ht
              )
              ≤
            B := by

        intro j
        fin_cases j

        · exact
            (hBound0 (τ n) ht hn0).trans hB0Le

        · exact
            (hBound1 (τ n) ht hn1).trans hB1Le

        · exact
            hLongLe.trans hRLeB

      have hEnergyLe :
          velocityH3EnergyAt u (τ n)
            ≤
          1 + 3 * B ^ 2 :=
        velocityH3EnergyAt_le_one_add_three_mul_sq_of_terminalComponentNormBound
          hH3
          ht
          hBnonneg
          hComponent

      exact
        (not_lt_of_ge hEnergyLe)
          hnLarge

    exact
      hMLe.trans
        (le_of_lt hLong)

/--
The explicit terminal sequence selected by the completed resolved-PDE closure
simultaneously carries total H³-energy escape and longitudinal spectral H³
escape at the surviving physical-vorticity coordinate.
-/
theorem exists_fixed_terminalSequence_h3Energy_and_longitudinalSpectralNorm_escape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ n))
            atTop atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                norm
                  (
                    h3TerminalVelocityComponentSpectralStateAt
                      hH3
                      i
                      (τ n)
                      ⟨
                        lt_trans hClass.terminal_start.1 (hτ n).1.1,
                        (hτ n).1.2
                      ⟩
                  )
            )
            atTop
            atTop := by

  obtain
    ⟨_j₀, τ, hτ, hTauTendsto, hEnergyTop⟩ :=
    exists_fixed_terminalSequence_h3Energy_escape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  have hLongitudinalTop :=
    longitudinalVelocityComponentSpectralNorm_tendstoAtTop_of_h3Energy_escape_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      τ
      (fun n : ℕ => (hτ n).1)
      hTauTendsto
      hEnergyTop

  exact
    ⟨
      _j₀,
      τ,
      hτ,
      hTauTendsto,
      hEnergyTop,
      hLongitudinalTop
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
