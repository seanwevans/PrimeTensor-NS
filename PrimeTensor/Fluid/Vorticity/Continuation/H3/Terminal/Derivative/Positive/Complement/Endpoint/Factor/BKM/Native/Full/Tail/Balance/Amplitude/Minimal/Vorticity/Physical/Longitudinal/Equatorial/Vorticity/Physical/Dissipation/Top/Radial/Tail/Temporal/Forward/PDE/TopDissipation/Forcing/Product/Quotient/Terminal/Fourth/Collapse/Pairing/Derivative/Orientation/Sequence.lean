import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation

/-!
# Terminal escape sequence for the oriented resolved-channel derivative

Hypothetical nonextension has now been reduced to one fixed coordinate, one
fixed resolved physical PDE channel, and one fixed orientation for which the
ordinary scalar channel derivative is cofinally unbounded on every strict
terminal tail.

This file converts that intrinsic cofinal statement into the explicit
sequential form used throughout the terminal cascade machinery.  For every
`n`, choose `τ n` so that

    T - 1 / (n + 1) < τ n < T

and

    n < orientedValue s (A'(τ n)).

Then `τ n -> T` and the oriented derivative tends to `+∞` along the selected
sequence.

No new analytic estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
Under hypothetical nonextension, one fixed coordinate, one fixed resolved
physical PDE channel, and one fixed orientation admit a quantitatively
localized terminal sequence along which the oriented scalar amplitude
derivative tends to `+∞`.
-/
theorem exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
        ∃ s : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            (
              ∀ n : ℕ,
                τ n ∈ Set.Ioo a T
                  ∧
                τ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                (n : ℝ)
                  <
                h3TerminalOrientedValue
                  s
                  (
                    deriv
                      (
                        h3TerminalResolvedPhysicalPDEChannelAmplitude
                          hH3 hClass j₀ channel
                      )
                      (τ n)
                  )
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalOrientedValue
                    s
                    (
                      deriv
                        (
                          h3TerminalResolvedPhysicalPDEChannelAmplitude
                            hH3 hClass j₀ channel
                        )
                        (τ n)
                    )
              )
              atTop
              atTop := by

  obtain
    ⟨
      j₀,
      channel,
      s,
      hCofinal
    ⟩ :=
    exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  have haT :
      a < T :=
    hClass.terminal_start.2

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈ Set.Ioo a T
            ∧
          t ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            s
            (
              deriv
                (
                  h3TerminalResolvedPhysicalPDEChannelAmplitude
                    hH3 hClass j₀ channel
                )
                t
            ) := by

    intro n

    let ε : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hε :
        0 < ε := by
      dsimp only [ε]
      positivity

    let c : ℝ :=
      max
        ((a + T) / 2)
        (T - ε)

    have hMidAbove :
        a < (a + T) / 2 := by
      linarith

    have hMidBelow :
        (a + T) / 2 < T := by
      linarith

    have hNearBelow :
        T - ε < T := by
      linarith

    have hc :
        c ∈ Set.Ioo a T := by
      constructor
      · dsimp only [c]
        exact
          lt_of_lt_of_le
            hMidAbove
            (le_max_left _ _)
      · dsimp only [c]
        exact
          max_lt
            hMidBelow
            hNearBelow

    obtain
      ⟨
        t,
        ht,
        hLarge
      ⟩ :=
      hCofinal c hc (n : ℝ)

    have htClass :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

    have hNearBase :
        T - ε ≤ c := by
      dsimp only [c]
      exact le_max_right _ _

    have htNear :
        t ∈ Set.Ioo (T - ε) T :=
      ⟨
        lt_of_le_of_lt
          hNearBase
          ht.1,
        ht.2
      ⟩

    exact
      ⟨
        t,
        htClass,
        by simpa only [ε] using htNear,
        hLarge
      ⟩

  choose τ hτ using hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    have hInv :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / ((n : ℝ) + 1)
          )
          atTop
          (𝓝 0) := by

      simpa only [
        Nat.cast_add,
        Nat.cast_one
      ] using
        tendsto_one_div_add_atTop_nhds_zero_nat

    have hNormBound :
        ∀ n : ℕ,
          ‖τ n - T‖
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by

      intro n

      have hNear :=
        (hτ n).2.1

      rw [
        Real.norm_eq_abs,
        abs_of_nonpos
          (
            sub_nonpos.mpr
              (le_of_lt hNear.2)
          )
      ]

      linarith [hNear.1]

    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (
          squeeze_zero'
            (
              Filter.Eventually.of_forall
                (
                  fun n =>
                    norm_nonneg (τ n - T)
                )
            )
            (
              Filter.Eventually.of_forall
                hNormBound
            )
            hInv
        )

  have hDerivativeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              s
              (
                deriv
                  (
                    h3TerminalResolvedPhysicalPDEChannelAmplitude
                      hH3 hClass j₀ channel
                  )
                  (τ n)
              )
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt M

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNn :
        (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hIndexLarge :
        M < (n : ℝ) :=
      lt_of_lt_of_le
        hN
        hNn

    exact
      le_of_lt
        (
          lt_trans
            hIndexLarge
            (hτ n).2.2
        )

  exact
    ⟨
      j₀,
      channel,
      s,
      τ,
      hτ,
      hTauTendsto,
      hDerivativeTendsto
    ⟩

/--
Neutral sequential formulation: either the H³ path extends smoothly through
`T`, or one fixed oriented resolved-channel scalar derivative tends to `+∞`
along a strict sequence converging quantitatively to `T`.
-/
theorem smoothContinuationExtension_or_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
          ∃ s : H3TerminalOrientation,
            ∃ τ : ℕ → ℝ,
              (
                ∀ n : ℕ,
                  τ n ∈ Set.Ioo a T
                    ∧
                  τ n ∈
                    Set.Ioo
                      (T - (1 : ℝ) / ((n : ℝ) + 1))
                      T
                    ∧
                  (n : ℝ)
                    <
                  h3TerminalOrientedValue
                    s
                    (
                      deriv
                        (
                          h3TerminalResolvedPhysicalPDEChannelAmplitude
                            hH3 hClass j₀ channel
                        )
                        (τ n)
                    )
              )
                ∧
              Tendsto τ atTop (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalOrientedValue
                      s
                      (
                        deriv
                          (
                            h3TerminalResolvedPhysicalPDEChannelAmplitude
                              hH3 hClass j₀ channel
                          )
                          (τ n)
                      )
                )
                atTop
                atTop
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
