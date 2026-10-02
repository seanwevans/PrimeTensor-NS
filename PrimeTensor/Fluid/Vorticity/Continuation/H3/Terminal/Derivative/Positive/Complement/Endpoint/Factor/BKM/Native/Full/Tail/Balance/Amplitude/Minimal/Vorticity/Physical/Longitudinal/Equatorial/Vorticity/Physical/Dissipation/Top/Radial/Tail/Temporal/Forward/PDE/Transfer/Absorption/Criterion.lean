import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Integral

/-!
# Cubic-forcing terminal integrability criterion

The localized top-tail analysis is now completely cutoff-free.

For every natural sharp cutoff and every strict physical time, the preceding
checkpoint proved

    deriv Tail₃(t,n+1)
      ≤
    fullForcingCubicMass(t),

where

    fullForcingCubicMass(t)
      =
    Σ_j ∫ q(ξ)^3 |F_j(U(t),U(t))(ξ)|² dξ.

This file packages that strict-time quantity as one scalar profile on `ℝ`,
extended by zero outside `(a,T)`, and connects its terminal `L¹` integrability
directly to the already-closed one-sided derivative continuation criterion.

No new estimate is asserted here.  In particular, terminal integrability of the
cubic forcing mass remains an explicit analytic condition.

The neutral endpoint alternative is therefore:

* either the H³ path extends smoothly through `T`;
* or this single full-space cubic forcing profile is not integrable on `(a,T)`.

All cutoff dependence, localized PDE balance, and local derivative
integrability have already been discharged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Global scalar profile -/

/--
The full cubic forcing mass on the strict physical interval, extended by zero
outside `(a,T)`.
-/
noncomputable def h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht
  else
    0

theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass t
      =
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by

  simp [
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile,
    ht
  ]

theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    0
      ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
      hH3 hClass t := by

  unfold
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile

  split_ifs with ht

  · exact
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_nonneg
        hH3 hClass ht

  · exact le_rfl

/-! ## Integrability of this one profile closes the upper derivative criterion -/

/--
Terminal `L¹` integrability of the full cubic forcing profile supplies the
common cutoff-independent upper derivative majorant.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint_of_fullForcingCubicMassProfile
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint
      hH3 hClass := by

  let g : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
      hH3 hClass

  have hBalance :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
      hH3 hClass

  have hLocal :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable_closed
      hH3 hClass

  refine
    ⟨
      g,
      ?_,
      ?_
    ⟩

  · simpa only [g] using
      hProfile

  · intro n

    refine
      ⟨
        ?_,
        ?_,
        ?_
      ⟩

    · intro t ht

      exact
        (hBalance n t ht).1

    · intro s hs t ht hst

      exact
        hLocal
          n
          s
          hs
          t
          ht
          hst

    · intro t ht

      have hUpper :=
        deriv_h3TerminalPhysicalTopDissipationNaturalRadialTailPath_le_fullForcingCubicMass
          hH3 hClass n ht

      calc
        deriv
            (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
              hH3 hClass n)
            t
            ≤
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass ht :=
          hUpper
        _ =
          g t := by
            dsimp only [g]
            exact
              (
                h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
                  hH3 hClass ht
              ).symm

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, terminal integrability of the single
full cubic forcing profile is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fullForcingCubicMassProfileIntegrable_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformIntegrableUpperDerivativeMajorant_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (
        h3TerminalPhysicalTopDissipationNaturalRadialTailUniformIntegrableUpperDerivativeMajorantAtEndpoint_of_fullForcingCubicMassProfile
          hH3 hClass hProfile
      )

/-! ## Neutral endpoint formulation -/

/--
Under the retained endpoint hypotheses, either the path extends smoothly
through `T` or the full cubic forcing mass profile fails to be terminal-`L¹`.
-/
theorem smoothContinuationExtension_or_not_integrableOn_fullForcingCubicMassProfile
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
    ¬
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume := by

  classical

  by_cases hProfile :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume

  · exact
      Or.inl
        (
          smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fullForcingCubicMassProfileIntegrable_of_actualVorticityStrongH3EndpointPath
            hH3
            hClass
            hPhysical
            hCauchy
            hProfile
        )

  · exact
      Or.inr hProfile

/--
Equivalent obstruction form: if no smooth continuation exists under the
retained endpoint hypotheses, then the full cubic forcing mass profile is not
integrable on `(a,T)`.
-/
theorem not_integrableOn_fullForcingCubicMassProfile_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ¬
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume := by

  intro hProfile

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_fullForcingCubicMassProfileIntegrable_of_actualVorticityStrongH3EndpointPath
          hH3
          hClass
          hPhysical
          hCauchy
          hProfile
      )

end

end Euclidean
end Bridge
end PrimeTensor
