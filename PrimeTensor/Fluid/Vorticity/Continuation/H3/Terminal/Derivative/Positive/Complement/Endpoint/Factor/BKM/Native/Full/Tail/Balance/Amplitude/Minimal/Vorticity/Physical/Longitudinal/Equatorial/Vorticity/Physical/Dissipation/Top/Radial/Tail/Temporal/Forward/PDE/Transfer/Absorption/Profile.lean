import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Continuity

/-!
# Continuity and terminal mass obstruction for the cubic forcing profile

The previous checkpoints identify the remaining continuation obstruction as

    G(t)
      =
    (2π)^6
      Σ_j ‖F³_j(t)‖²,

where each canonical physical third-radial forcing path `F³_j` is strongly
continuous in Fourier `L²` on the strict energy-class interval `(a,T)`.

Therefore `G` itself is continuous and nonnegative on `(a,T)`.

Combining this topology with the already-proved continuation criterion removes
the last possible measurability ambiguity: if the retained endpoint hypotheses
hold and no smooth continuation exists, then `G` is a continuous nonnegative
function whose terminal `L¹` mass is genuinely infinite.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingProfile
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Exact physical norm-square representation -/

/--
On the strict physical interval, the global cubic forcing profile is exactly
the fixed `(2π)^6` multiple of the sum of the three physical third-radial
forcing norm squares.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass t
      =
    (2 * Real.pi) ^ 6
      *
    ∑ j : Fin 3,
      (
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ
      ) ^ 2 := by

  rw [
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
      hH3 hClass ht,
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_eq_sum_norm_sq_thirdRadial
      hH3 hClass ht
  ]

  congr 1

  apply
    Finset.sum_congr rfl

  intro j hj

  rw [
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
      hH3 hClass ht j
  ]

/-! ## Scalar continuity -/

/--
The full cubic forcing mass profile is continuous on the complete strict
energy-class interval.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ContinuousOn
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass
      )
      (Set.Ioo a T) := by

  have hEach :
      ∀ j : Fin 3,
        ContinuousOn
          (fun t : ℝ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖ : ℝ
            ) ^ 2)
          (Set.Ioo a T) := by

    intro j

    have hPath :
        ContinuousOn
          (
            h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j
          )
          (Set.Ioo a T) :=
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousOn
        hH3 hClass j

    have hNorm :
        ContinuousOn
          (fun t : ℝ =>
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j t‖)
          (Set.Ioo a T) :=
      continuous_norm.comp_continuousOn
        hPath

    exact
      hNorm.pow 2

  have hSum :
      ContinuousOn
        (fun t : ℝ =>
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖ : ℝ
            ) ^ 2)
        (Set.Ioo a T) := by

    simpa using
      (
        continuousOn_finsetSum
          (Finset.univ : Finset (Fin 3))
          (fun j hj => hEach j)
      )

  have hModel :
      ContinuousOn
        (fun t : ℝ =>
          (2 * Real.pi) ^ 6
            *
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖ : ℝ
            ) ^ 2)
        (Set.Ioo a T) :=
    hSum.const_mul
      ((2 * Real.pi) ^ 6)

  apply
    hModel.congr

  intro t ht

  exact
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
      hH3 hClass ht

/--
The continuous cubic forcing profile is strongly measurable with respect to
Lebesgue measure restricted to `(a,T)`.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    AEStronglyMeasurable
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass
      )
      (
        (volume : Measure ℝ).restrict
          (Set.Ioo a T)
      ) := by

  exact
    ContinuousOn.aestronglyMeasurable
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
          hH3 hClass
      )
      measurableSet_Ioo

/-! ## Nonextension forces genuine infinite terminal mass -/

/--
If there is no smooth continuation under the retained endpoint hypotheses,
then the continuous cubic forcing profile does not have finite terminal
integral.  The failure of `IntegrableOn` is therefore not a measurability
failure.
-/
theorem not_hasFiniteIntegral_fullForcingCubicMassProfile_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      HasFiniteIntegral
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (
          (volume : Measure ℝ).restrict
            (Set.Ioo a T)
        ) := by

  intro hFinite

  have hMeas :
      AEStronglyMeasurable
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (
          (volume : Measure ℝ).restrict
            (Set.Ioo a T)
        ) :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_aestronglyMeasurable
      hH3 hClass

  have hIntegrable :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume :=
    ⟨hMeas, hFinite⟩

  exact
    (
      not_integrableOn_fullForcingCubicMassProfile_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
        hH3
        hClass
        hPhysical
        hCauchy
        hNoExtension
    )
      hIntegrable

/--
Equivalent extended-integral formulation: on a nonextension branch satisfying
the retained endpoint hypotheses, the terminal `L¹` norm mass of the cubic
forcing profile is infinite.
-/
theorem lintegral_enorm_fullForcingCubicMassProfile_eq_top_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    (
      ∫⁻ t : ℝ,
        ‖h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass t‖ₑ
        ∂(
          (volume : Measure ℝ).restrict
            (Set.Ioo a T)
        )
    )
      =
    ∞ := by

  have hNotFinite :=
    not_hasFiniteIntegral_fullForcingCubicMassProfile_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  unfold HasFiniteIntegral at hNotFinite

  exact
    top_unique
      (not_lt.mp hNotFinite)

end

end Euclidean
end Bridge
end PrimeTensor
