import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Start

/-!
# Cubic forcing mass diverges on every terminal tail

The cubic forcing obstruction was originally packaged relative to a chosen
`PreterminalH3EnergyClass u a T`.  The preceding arbitrary-start checkpoint
shows that every strict physical time can itself be used as a new energy-class
start.

The scalar forcing mass is nevertheless a physical quantity: on overlapping
times it is independent of which energy-class start was used to justify the
high-order analysis.  The only class-dependent data entering its definition are
proofs that the same physical time lies in `(0,T)`.

After recording that class-start independence, a nonextension branch can be
restarted at any `c ∈ (a,T)`.  Applying the already-closed nonintegrability
criterion to the energy class starting at `c` and transporting back to the
original profile yields

    G ∉ L¹((c,T))

for every `c ∈ (a,T)`.

Hence the previously identified infinite cubic-forcing mass is genuinely
terminal: no matter how far forward one truncates the physical interval, the
remaining tail still has infinite mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingTerminal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Independence of the energy-class start -/

/--
At a common physical time, one coordinate of the cubic forcing density is
independent of which energy-class tail was used to justify the construction.
-/
theorem h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_of_energyClasses
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClassA : PreterminalH3EnergyClass u a T)
    (hClassB : PreterminalH3EnergyClass u b T)
    (htA : t ∈ Set.Ioo a T)
    (htB : t ∈ Set.Ioo b T)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClassA htA j ξ
      =
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClassB htB j ξ := by

  unfold
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

  rfl

/--
At a common physical time, the complete cubic forcing mass is independent of
the energy-class start.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_eq_of_energyClasses
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClassA : PreterminalH3EnergyClass u a T)
    (hClassB : PreterminalH3EnergyClass u b T)
    (htA : t ∈ Set.Ioo a T)
    (htB : t ∈ Set.Ioo b T) :
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClassA htA
      =
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClassB htB := by

  unfold
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt

  apply
    Finset.sum_congr rfl

  intro j hj

  apply
    integral_congr_ae

  exact
    Filter.Eventually.of_forall
      (fun ξ =>
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_of_energyClasses
          hH3
          hClassA
          hClassB
          htA
          htB
          j
          ξ)

/--
On the overlap of two energy-class tails, their global cubic forcing profiles
have exactly the same value.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_of_energyClasses
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClassA : PreterminalH3EnergyClass u a T)
    (hClassB : PreterminalH3EnergyClass u b T)
    (htA : t ∈ Set.Ioo a T)
    (htB : t ∈ Set.Ioo b T) :
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClassA t
      =
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClassB t := by

  rw [
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
      hH3 hClassA htA,
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
      hH3 hClassB htB
  ]

  exact
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_eq_of_energyClasses
      hH3
      hClassA
      hClassB
      htA
      htB

/-! ## Nonextension forces divergence on every terminal tail -/

/--
Under the retained endpoint hypotheses and failure of smooth continuation, the
original cubic forcing profile is nonintegrable on every later terminal tail
`(c,T)`.
-/
theorem not_integrableOn_fullForcingCubicMassProfile_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hc : c ∈ Set.Ioo a T) :
    ¬
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo c T)
        volume := by

  have hcAbs :
      c ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        hc.1,
      hc.2
    ⟩

  let hClassC :
      PreterminalH3EnergyClass u c T :=
    h3Preterminal_energyClass_from_of_h3PathAdmissible
      hH3 hcAbs

  have hNotC :
      ¬
        IntegrableOn
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClassC
          )
          (Set.Ioo c T)
          volume :=
    not_integrableOn_fullForcingCubicMassProfile_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClassC
      hPhysical
      hCauchy
      hNoExtension

  intro hInt

  have hIntC :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClassC
        )
        (Set.Ioo c T)
        volume := by

    exact
      IntegrableOn.congr_fun
        hInt
        (fun t ht => by
          have htA :
              t ∈ Set.Ioo a T :=
            ⟨
              lt_trans
                hc.1
                ht.1,
              ht.2
            ⟩

          have htC :
              t ∈ Set.Ioo c T :=
            ht

          exact
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_of_energyClasses
              hH3
              hClass
              hClassC
              htA
              htC)
        measurableSet_Ioo

  exact
    hNotC hIntC

/--
Measure-theoretic strengthening: on every terminal tail `(c,T)`, nonextension
forces infinite extended `L¹` mass of the cubic forcing profile.
-/
theorem lintegral_enorm_fullForcingCubicMassProfile_eq_top_on_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hc : c ∈ Set.Ioo a T) :
    (
      ∫⁻ t : ℝ,
        ‖h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass t‖ₑ
        ∂(
          (volume : Measure ℝ).restrict
            (Set.Ioo c T)
        )
    )
      =
    ∞ := by

  have hNotInt :
      ¬
        IntegrableOn
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass
          )
          (Set.Ioo c T)
          volume :=
    not_integrableOn_fullForcingCubicMassProfile_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hc

  have hCont :
      ContinuousOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo c T) := by

    exact
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
          hH3 hClass
      ).mono
        (by
          intro t ht

          exact
            ⟨
              lt_trans
                hc.1
                ht.1,
              ht.2
            ⟩)

  have hMeas :
      AEStronglyMeasurable
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (
          (volume : Measure ℝ).restrict
            (Set.Ioo c T)
        ) :=
    ContinuousOn.aestronglyMeasurable
      hCont
      measurableSet_Ioo

  have hNotFinite :
      ¬
        HasFiniteIntegral
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass
          )
          (
            (volume : Measure ℝ).restrict
              (Set.Ioo c T)
          ) := by

    intro hFinite

    exact
      hNotInt
        ⟨
          hMeas,
          hFinite
        ⟩

  unfold HasFiniteIntegral at hNotFinite

  exact
    top_unique
      (not_lt.mp hNotFinite)

end

end Euclidean
end Bridge
end PrimeTensor
