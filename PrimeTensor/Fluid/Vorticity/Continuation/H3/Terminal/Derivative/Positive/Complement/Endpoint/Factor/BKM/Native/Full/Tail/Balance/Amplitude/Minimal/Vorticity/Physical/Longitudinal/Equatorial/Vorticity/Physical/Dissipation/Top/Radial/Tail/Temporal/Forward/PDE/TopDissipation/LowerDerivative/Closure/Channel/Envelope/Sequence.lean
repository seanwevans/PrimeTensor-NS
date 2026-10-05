import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope

/-!
# Terminal sequence for the global resolved physical PDE envelope

The global resolved physical PDE envelope is already known to be cofinally
unbounded on every strict terminal tail under hypothetical nonextension.

This file converts that intrinsic cofinal statement into the explicit
asymptotic sequence form used by the terminal cascade machinery.

For every `n`, choose a time `τ n` satisfying

    T - 1 / (n + 1) < τ n < T

and

    n < h3TerminalResolvedPhysicalPDEEnvelope hH3 hClass (τ n).

Consequently `τ n -> T` and the global envelope tends to `+∞` along the
selected sequence.

No new analytic estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 900000

/--
Under the retained endpoint hypotheses and hypothetical nonextension, the
global resolved physical PDE envelope exceeds every finite threshold
arbitrarily close to the terminal time.
-/
theorem resolvedPhysicalPDEEnvelope_arbitrarilyLarge_arbitrarilyNearTerminal_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T
            ∧
          t ∈ Set.Ioo a T
            ∧
          M <
            h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass t := by

  have hCofinal :=
    resolvedPhysicalPDEEnvelope_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  intro ε hε M

  let b : ℝ :=
    max
      ((a + T) / 2)
      (T - ε / 2)

  have haT :
      a < T :=
    hClass.terminal_start.2

  have hMidAbove :
      a < (a + T) / 2 := by
    linarith

  have hMidBelow :
      (a + T) / 2 < T := by
    linarith

  have hNearLtT :
      T - ε / 2 < T := by
    linarith

  have hab :
      a < b := by
    exact
      lt_of_lt_of_le
        hMidAbove
        (le_max_left _ _)

  have hbT :
      b < T := by
    dsimp only [b]
    exact
      max_lt
        hMidBelow
        hNearLtT

  have hb :
      b ∈ Set.Ioo a T :=
    ⟨hab, hbT⟩

  obtain
    ⟨t, ht, hLarge⟩ :=
    hCofinal b hb M

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hab ht.1,
      ht.2
    ⟩

  have hHalfNear :
      T - ε < T - ε / 2 := by
    linarith

  have hBaseLe :
      T - ε / 2 ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have htNear :
      t ∈ Set.Ioo (T - ε) T :=
    ⟨
      lt_trans
        hHalfNear
        (lt_of_le_of_lt hBaseLe ht.1),
      ht.2
    ⟩

  exact
    ⟨
      t,
      htNear,
      htClass,
      hLarge
    ⟩

/--
Under hypothetical nonextension there is a strict terminal sequence along
which the one global resolved physical PDE envelope tends to `+∞`.

The sequence is quantitatively localized by `1 / (n + 1)` and the envelope is
larger than `n` at the `n`th selected time.
-/
theorem exists_resolvedPhysicalPDEEnvelope_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          (n : ℝ) <
            h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass (τ n)
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEEnvelope
            hH3 hClass (τ n))
        atTop
        atTop := by

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
          (n : ℝ) <
            h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass t := by

    intro n

    have hDen :
        0 < (n : ℝ) + 1 := by
      positivity

    have hε :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      exact one_div_pos.mpr hDen

    obtain
      ⟨t, htNear, htClass, hLarge⟩ :=
      resolvedPhysicalPDEEnvelope_arbitrarilyLarge_arbitrarilyNearTerminal_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
        hH3 hClass hPhysical hCauchy hNoExtension
        ((1 : ℝ) / ((n : ℝ) + 1))
        hε
        (n : ℝ)

    exact
      ⟨
        t,
        htClass,
        htNear,
        hLarge
      ⟩

  choose τ hτ using hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    have hInv :
        Tendsto
          (fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1))
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

      have hNearN :=
        (hτ n).2.1

      rw [
        Real.norm_eq_abs,
        abs_of_nonpos
          (sub_nonpos.mpr
            (le_of_lt hNearN.2))
      ]

      linarith [hNearN.1]

    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (
          squeeze_zero'
            (Filter.Eventually.of_forall
              (fun n =>
                norm_nonneg (τ n - T)))
            (Filter.Eventually.of_forall
              hNormBound)
            hInv
        )

  have hEnvelopeTendsto :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEEnvelope
            hH3 hClass (τ n))
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hNatLarge :
        ∀ᶠ n : ℕ in atTop,
          M < (n : ℝ) := by

      obtain
        ⟨N : ℕ, hN⟩ :=
        exists_nat_gt M

      filter_upwards
        [eventually_ge_atTop N]
        with n hn

      exact
        lt_of_lt_of_le
          hN
          (by exact_mod_cast hn)

    filter_upwards
      [hNatLarge]
      with n hn

    exact
      le_of_lt
        (
          lt_trans
            hn
            (hτ n).2.2
        )

  exact
    ⟨
      τ,
      hτ,
      hTauTendsto,
      hEnvelopeTendsto
    ⟩

/--
Neutral sequential endpoint formulation.

Either the path extends smoothly through `T`, or there is a strict preterminal
sequence converging to `T` along which the single global resolved physical PDE
envelope tends to `+∞`.
-/
theorem smoothContinuationExtension_or_resolvedPhysicalPDEEnvelope_blowupSequence
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
            (n : ℝ) <
              h3TerminalResolvedPhysicalPDEEnvelope
                hH3 hClass (τ n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass (τ n))
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
          exists_resolvedPhysicalPDEEnvelope_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
