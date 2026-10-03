import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape

/-!
# Cofinal terminal escape of one fixed physical PDE channel

The preceding checkpoint freezes, under hypothetical nonextension, one fixed
forcing coordinate and one of three physical channels on a strict terminal
sequence:

* the lower neighboring forcing mass `M₂`;
* the fourth-radial temporal derivative norm-square;
* the sixth-radial diffusion norm-square.

This file removes the sequence artifact.

A generic terminal lemma shows that if

    τₙ -> T

and

    f(τₙ) -> +∞,

with every `τₙ` lying in `(a,T)`, then `f` is cofinally unbounded on every
strict terminal tail `(c,T)`.

Applying that lemma to the three frozen channels gives an intrinsic terminal
obstruction: one fixed coordinate and one fixed PDE channel exceeds every
finite threshold arbitrarily close to `T`.

A neutral continuation alternative is recorded at the end.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingPDECofinal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 900000

/-! ## Generic sequence-to-cofinal upgrade -/

private theorem cofinallyUnbounded_on_terminal_tails_of_blowupSequence
    {a T : ℝ}
    {τ : ℕ → ℝ}
    {f : ℝ → ℝ}
    (hTauMem :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hTop :
      Tendsto
        (fun n : ℕ => f (τ n))
        atTop
        atTop) :
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          M < f t := by

  intro c hc M

  have hPast :
      ∀ᶠ n : ℕ in atTop,
        c < τ n :=
    hTauTendsto.eventually
      (Ioi_mem_nhds hc.2)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M < f (τ n) :=
    hTop.eventually
      (eventually_gt_atTop M)

  obtain
    ⟨n, hnPast, hnLarge⟩ :=
    (hPast.and hLarge).exists

  exact
    ⟨
      τ n,
      ⟨
        hnPast,
        (hTauMem n).2
      ⟩,
      hnLarge
    ⟩

/-! ## Fixed-coordinate cofinal PDE-channel escape -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
physical forcing coordinate has one fixed channel cofinally unbounded on every
terminal tail.

The three alternatives remain exhaustive and none is discarded.
-/
theorem exists_fixed_thirdRadialForcing_PDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      (
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                  hH3 hClass j₀ t
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                (
                  ‖deriv
                      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                        hH3 hClass j₀)
                      t‖ : ℝ
                ) ^ 2
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                (
                  ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                      hH3 hClass j₀ t‖ : ℝ
                ) ^ 2
        )
      ) := by

  obtain
    ⟨
      j₀,
      τ,
      hTauData,
      hTauTendsto,
      hBranch
    ⟩ :=
    exists_fixed_thirdRadialForcing_PDEChannel_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  have hTauMem :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T :=
    fun n =>
      (hTauData n).1

  refine
    ⟨
      j₀,
      ?_
    ⟩

  rcases hBranch with hSecond | hTemporal | hDiffusion

  · left

    exact
      cofinallyUnbounded_on_terminal_tails_of_blowupSequence
        hTauMem
        hTauTendsto
        hSecond

  · right
    left

    exact
      cofinallyUnbounded_on_terminal_tails_of_blowupSequence
        hTauMem
        hTauTendsto
        hTemporal

  · right
    right

    exact
      cofinallyUnbounded_on_terminal_tails_of_blowupSequence
        hTauMem
        hTauTendsto
        hDiffusion

/-! ## Neutral continuation alternative -/

/--
Neutral endpoint formulation.

Either the H³ path extends smoothly through `T`, or one fixed physical forcing
coordinate has one fixed PDE channel cofinally unbounded on every strict
terminal tail.
-/
theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_PDEChannel_cofinallyUnbounded
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
        (
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                    hH3 hClass j₀ t
          )
            ∨
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  (
                    ‖deriv
                        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                          hH3 hClass j₀)
                        t‖ : ℝ
                  ) ^ 2
          )
            ∨
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  (
                    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                        hH3 hClass j₀ t‖ : ℝ
                  ) ^ 2
          )
        )
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
          exists_fixed_thirdRadialForcing_PDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3
            hClass
            hPhysical
            hCauchy
            hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
