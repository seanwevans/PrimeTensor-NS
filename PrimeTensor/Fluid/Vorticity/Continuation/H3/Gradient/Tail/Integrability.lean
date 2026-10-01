import PrimeTensor.Fluid.Vorticity.Continuation.H3.BKM.Closure

/-!
# Tail-local velocity-gradient continuation

The exact H³ energy estimate already gives, for every common first-derivative
envelope `h`,

    E'(t) ≤ 4422 * (1 + |h(t)|) * E(t).

No BKM vorticity-to-gradient endpoint estimate is needed once such a gradient
envelope is supplied directly.

Because the normalized H³ energy satisfies `E ≥ 1`, the existing logarithmic
Grönwall theorem applies whenever `h` is integrable on one strict terminal H³
energy-class tail.

Consequently, hypothetical nonextension forces every genuine common
velocity-gradient envelope to be nonintegrable on every strict terminal H³
subtail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Closed scalar dynamics used by the direct gradient criterion -/

private theorem h3PathCanonicalGradientGrowth_for_tailIntegrability :
    H3PathEnergyClassProducesCanonicalGradientGrowth := by

  have hSigns :
      H3PathEnergyClassProducesFullScalarSigns :=
    h3PathEnergyClassProducesFullScalarSigns_of_pressureCancellation
      h3PathEnergyClassProducesPressureCancellation_closed

  exact
    h3PathEnergyClassProducesCanonicalGradientGrowth_of_exactEnergy
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hSigns

/-! ## Tail-local continuation -/

/--
An integrable common first-spatial-derivative envelope on one strict H³
energy-class tail is sufficient for smooth continuation through the terminal
time.
-/
theorem h3PathExtension_of_integrableVelocityGradientEnvelopeOnEnergyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hhIntegrable :
      MeasureTheory.IntegrableOn
        h
        (Set.Ioo a T))
    (hhEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3
      ha

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        a T h
        (velocityH3EnergyAt u)
        4422 :=
    h3PathCanonicalGradientGrowth_for_tailIntegrability
      u T hH3
      a hClass
      h
      hhEnvelope

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hGrowth :
      BKMLogGrowthInequalityFrom
        a T h
        (velocityH3EnergyAt u)
        4422 := by

    intro t ht

    have hLinear :
        deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
      hEnergyGrowth
        t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      hEOne
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t := by
      linarith

    have hLogNonneg :
        0 ≤ Real.log (velocityH3EnergyAt u t) :=
      Real.log_nonneg
        hEtOne

    have hBaseNonneg :
        0 ≤
          4422
            * (1 + |h t|)
            * velocityH3EnergyAt u t := by

      exact
        mul_nonneg
          (
            mul_nonneg
              (by norm_num)
              (by positivity)
          )
          hEtNonneg

    have hLogFactor :
        1 ≤ 1 + Real.log (velocityH3EnergyAt u t) := by
      linarith

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hLinear

      _ ≤
        (
          4422
            * (1 + |h t|)
            * velocityH3EnergyAt u t
        )
          *
        (1 + Real.log (velocityH3EnergyAt u t)) := by

        exact
          le_mul_of_one_le_right
            hBaseNonneg
            hLogFactor

      _ =
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        ring

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico a T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc a q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      ha

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3
        a hClass
        s hs

    have hDeriv :
        deriv (velocityH3EnergyAt u) s
          =
        velocityH3FormalDerivativeAt u s :=
      deriv_velocityH3EnergyAt
        hIds

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      ha.2
      hhIntegrable
      (by norm_num)
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

  have hTail :
      TerminalTailH3Control u T := by

    refine
      ⟨
        a,
        M,
        ha,
        hM,
        ?_
      ⟩

    intro t ht

    exact
      velocityH3BoundAt_mono
        (hProfile t ht).2
        (hEM t ht)

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/-! ## Contrapositive terminal obstruction -/

/--
Under hypothetical nonextension, every common velocity-gradient envelope valid
on an H³ energy-class tail is nonintegrable there.
-/
theorem not_integrableOn_velocityGradientEnvelope_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hhEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h t) :
    ¬ MeasureTheory.IntegrableOn
        h
        (Set.Ioo a T) := by

  intro hhIntegrable

  exact
    hNoExtension
      (
        h3PathExtension_of_integrableVelocityGradientEnvelopeOnEnergyClassTail
          hH3
          hClass
          hhIntegrable
          hhEnvelope
      )

/--
The velocity-gradient-envelope obstruction persists on every strict later
terminal subtail.
-/
theorem not_integrableOn_velocityGradientEnvelope_on_every_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀
      c : ℝ,
        c ∈ Set.Ioo a T →
        ∀
          h : ℝ → ℝ,
            (
              ∀ t : ℝ,
                t ∈ Set.Ioo c T →
                  VelocityGradientEnvelope u h t
            )
              →
            ¬ MeasureTheory.IntegrableOn
                h
                (Set.Ioo c T) := by

  intro c hc h hhEnvelope

  have hClassC :
      PreterminalH3EnergyClass u c T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hc.1)
      hc.2

  exact
    not_integrableOn_velocityGradientEnvelope_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClassC
      hhEnvelope

/-! ## Neutral package -/

/--
Neutral direct-gradient terminal alternative: either the path extends smoothly,
or every common velocity-gradient envelope on every strict terminal H³
subtail is nonintegrable.
-/
theorem smoothContinuationExtension_or_every_terminalVelocityGradientEnvelope_nonintegrable
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
      ∀
        c : ℝ,
          c ∈ Set.Ioo a T →
          ∀
            h : ℝ → ℝ,
              (
                ∀ t : ℝ,
                  t ∈ Set.Ioo c T →
                    VelocityGradientEnvelope u h t
              )
                →
              ¬ MeasureTheory.IntegrableOn
                  h
                  (Set.Ioo c T)
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
        (
          not_integrableOn_velocityGradientEnvelope_on_every_strictSubtail_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
