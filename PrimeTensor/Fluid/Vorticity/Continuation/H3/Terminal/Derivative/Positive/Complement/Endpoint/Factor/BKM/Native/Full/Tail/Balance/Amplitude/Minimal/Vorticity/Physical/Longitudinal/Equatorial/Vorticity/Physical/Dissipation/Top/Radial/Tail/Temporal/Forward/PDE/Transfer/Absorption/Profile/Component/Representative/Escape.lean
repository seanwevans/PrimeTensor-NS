import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative

/-!
# Cofinal escape of one fixed physical third-radial forcing coordinate

The preceding checkpoint identifies the fixed third-radial Hilbert norm blowup
with the literal physical weighted Fourier mass

    ∫ |ξ|⁶ |P div(U(t) ⊗ U(t))_j(ξ)|² dξ.

This file upgrades the sequential statement to a tail-wide one.

First, the raw physical mass path is continuous on every strict physical
energy-class interval because it is exactly the square of the already-continuous
third-radial forcing Hilbert norm.

Second, the fixed-coordinate terminal blowup sequence immediately yields
cofinal unboundedness: the same coordinate exceeds every finite threshold on
every terminal subtail `(c,T)`.

Thus hypothetical nonextension does not merely produce one specially chosen
large sequence. One fixed physical nonlinear-forcing coordinate remains
arbitrarily large arbitrarily late.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingRepresentativeEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 900000

theorem h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    ContinuousOn
      (
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
          hH3 hClass j
      )
      (Set.Ioo a T) := by

  have hNorm :
      ContinuousOn
        (
          fun t : ℝ =>
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖
        )
        (Set.Ioo a T) :=
    continuous_norm.comp_continuousOn
      (
        h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousOn
          hH3 hClass j
      )

  have hSq :
      ContinuousOn
        (
          fun t : ℝ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
        )
        (Set.Ioo a T) :=
    hNorm.pow 2

  apply hSq.congr

  intro t ht

  exact
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
      hH3 hClass ht j

theorem exists_fixed_thirdRadialForcingRawFourierMass_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∀ M : ℝ,
          ∃ t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            M
              <
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
              hH3 hClass j₀ t := by

  obtain
    ⟨j₀, τ, hTauData, hTauTendsto, hMassTendsto⟩ :=
    exists_fixed_thirdRadialForcingRawFourierMass_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  refine ⟨j₀, ?_⟩

  intro c hc M

  have hPast :
      ∀ᶠ n : ℕ in atTop,
        c < τ n :=
    hTauTendsto.eventually
      (Ioi_mem_nhds hc.2)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M
          <
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
          hH3 hClass j₀ (τ n) :=
    hMassTendsto.eventually
      (eventually_gt_atTop M)

  obtain
    ⟨n, hnPast, hnLarge⟩ :=
    (hPast.and hLarge).exists

  exact
    ⟨
      τ n,
      ⟨
        hnPast,
        (hTauData n).1.2
      ⟩,
      hnLarge
    ⟩

theorem exists_fixed_thirdRadialForcingRawFourierMass_continuous_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      ContinuousOn
        (
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
            hH3 hClass j₀
        )
        (Set.Ioo a T)
        ∧
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ t : ℝ,
              t ∈ Set.Ioo c T
                ∧
              M
                <
              h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
                hH3 hClass j₀ t
      ) := by

  obtain
    ⟨j₀, hCofinal⟩ :=
    exists_fixed_thirdRadialForcingRawFourierMass_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  exact
    ⟨
      j₀,
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_continuousOn
        hH3 hClass j₀,
      hCofinal
    ⟩

theorem smoothContinuationExtension_or_fixed_thirdRadialForcingRawFourierMass_cofinallyUnbounded
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
        ContinuousOn
          (
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
              hH3 hClass j₀
          )
          (Set.Ioo a T)
          ∧
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
                  hH3 hClass j₀ t
        )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_thirdRadialForcingRawFourierMass_continuous_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
