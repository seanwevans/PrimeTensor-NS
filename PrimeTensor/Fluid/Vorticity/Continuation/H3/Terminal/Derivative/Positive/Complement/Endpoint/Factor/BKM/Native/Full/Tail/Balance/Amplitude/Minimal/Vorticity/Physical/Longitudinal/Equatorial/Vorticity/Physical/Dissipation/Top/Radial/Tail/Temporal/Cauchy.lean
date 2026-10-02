import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Cutoff.Scale.Cofinality

/-!
# Uniform temporal Cauchy control of canonical top-order radial tails

The present endpoint obstruction is loss of uniform radial-tail decay as
`t → T`, even though every fixed strict preterminal state has vanishing radial
tail as the cutoff tends to infinity.

This file isolates a genuinely temporal route to compactness.

For the natural radial tails

    Tail₃(t,n+1),

require terminal Cauchy control which is uniform in the cutoff index `n`:
for every `δ > 0`, all sufficiently late strict times `s,t` satisfy

    |Tail₃(s,n+1) - Tail₃(t,n+1)| < δ

simultaneously for every `n`.

That property upgrades the already-proved fixed-time tail decay to terminal
uniform tail decay: choose one late anchor time `s`, use fixed-time decay there,
and transfer the small tail to every nearby time uniformly in `n`.

Consequently, under the retained raw-Fourier `L²` Cauchy and physical-vorticity
endpoint hypotheses, uniform temporal Cauchy control of the top radial tails is
sufficient for smooth continuation.

The remaining analytic task is therefore dynamic: derive this uniform temporal
control, or a sufficient flux/derivative estimate implying it, directly from
the Navier--Stokes evolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Uniform terminal temporal Cauchy property -/

/--
The canonical natural top-order radial tails are terminal Cauchy in time,
uniformly over every natural cutoff index.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ s : ℝ,
        ∀ hs : s ∈ Set.Ioo a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              dist s T < η
                →
              dist t T < η
                →
              ∀ n : ℕ,
                abs
                    (
                      h3TerminalPhysicalTopDissipationRadialTailMassAt
                          hH3 hClass s hs ((n : ℝ) + 1)
                        -
                      h3TerminalPhysicalTopDissipationRadialTailMassAt
                        hH3 hClass t ht ((n : ℝ) + 1)
                    )
                  <
                δ

/-! ## Uniform temporal Cauchy plus fixed-time decay gives uniform tail decay -/

/--
Uniform terminal temporal Cauchy control of all natural radial tails upgrades
fixed-time radial-tail decay to terminal uniform radial-tail decay.
-/
theorem naturalRadialTailUniformVanishingAtEndpoint_of_uniformTemporalCauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTemporal :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailUniformVanishingAtEndpoint
      hH3 hClass := by

  intro δ hδ

  obtain
    ⟨
      η,
      hη,
      hCauchy
    ⟩ :=
    hTemporal
      (δ / 2)
      (by positivity)

  let r : ℝ :=
    min
      (η / 2)
      ((T - a) / 2)

  have hTa :
      0 < T - a :=
    sub_pos.mpr
      hClass.terminal_start.2

  have hr :
      0 < r := by

    dsimp only [r]

    exact
      lt_min
        (by positivity)
        (by positivity)

  have hrη :
      r ≤ η / 2 := by

    dsimp only [r]

    exact
      min_le_left
        (η / 2)
        ((T - a) / 2)

  have hrTa :
      r ≤ (T - a) / 2 := by

    dsimp only [r]

    exact
      min_le_right
        (η / 2)
        ((T - a) / 2)

  let s : ℝ :=
    T - r

  have hs :
      s ∈ Set.Ioo a T := by

    constructor

    · dsimp only [s]
      linarith

    · dsimp only [s]
      linarith

  have hsNear :
      dist s T < η := by

    have hrη' :
        r < η := by
      linarith

    calc
      dist s T = r := by
        rw [Real.dist_eq]
        dsimp only [s]
        have hSub :
            T - r - T = -r := by
          ring
        rw [
          hSub,
          abs_neg,
          abs_of_nonneg (le_of_lt hr)
        ]

      _ < η := hrη'

  have hFixed :=
    h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
      hH3
      hClass
      hs

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalPhysicalTopDissipationRadialTailMassAt
            hH3 hClass s hs ((n : ℝ) + 1)
          <
        δ / 2 :=
    hFixed.eventually
      (Iio_mem_nhds
        (by positivity))

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    eventually_atTop.1
      hEventually

  refine
    ⟨
      N,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear n hn

  have hAnchor :
      h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass s hs ((n : ℝ) + 1)
        <
      δ / 2 :=
    hN
      n
      hn

  have hDifference :
      abs
          (
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass s hs ((n : ℝ) + 1)
              -
            h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass t ht ((n : ℝ) + 1)
          )
        <
      δ / 2 :=
    hCauchy
      s
      hs
      t
      ht
      hsNear
      htNear
      n

  have hLower :=
    (abs_lt.mp hDifference).1

  linarith

/-! ## Continuation consequence -/

/--
Under the retained endpoint hypotheses, uniform temporal Cauchy control of the
canonical natural top-order radial tails is sufficient for smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformTemporalCauchy_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTemporal :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      (naturalRadialTailUniformVanishingAtEndpoint_of_uniformTemporalCauchy
        hH3
        hClass
        hTemporal)

/-! ## Nonextension obstruction -/

/--
Under the retained endpoint hypotheses, hypothetical nonextension forces
failure of uniform temporal Cauchy control of the canonical natural top-order
radial tails.
-/
theorem not_naturalTopDissipationRadialTailUniformTemporalCauchy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
        hH3 hClass := by

  intro hTemporal

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_naturalTopDissipationRadialTailUniformTemporalCauchy_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hTemporal)

/-! ## Neutral formulation -/

/--
Neutral endpoint alternative: either the H³ path extends smoothly through `T`,
or the canonical natural top-order radial tails fail to be terminal Cauchy in
time uniformly over the cutoff index.

This formulation turns the remaining compactness obstruction into an explicit
temporal estimate that can be targeted by the Navier--Stokes evolution.
-/
theorem smoothContinuationExtension_or_not_naturalTopDissipationRadialTailUniformTemporalCauchy
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
    ¬ H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (not_naturalTopDissipationRadialTailUniformTemporalCauchy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
