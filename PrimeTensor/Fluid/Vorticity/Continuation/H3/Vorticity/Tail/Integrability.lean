import PrimeTensor.Fluid.Vorticity.Continuation.H3.BKM.Closure

/-!
# Tail-local BKM vorticity-envelope continuation

The public BKM endpoint is packaged through `VorticityL1LinfControl u T`,
which asks for one integrable common vorticity envelope on the whole
preterminal interval `(0,T)`.

The actual BKM/Osgood argument is terminal-tail local.

This file extracts that locality directly.  If an admissible H³ path has one
strict energy-class tail `(a,T)` on which a common scalar vorticity envelope
`g` is integrable, then the path extends smoothly through `T`.

Consequently, on a hypothetical nonextension branch, every genuine common
vorticity envelope is nonintegrable on every strict terminal energy-class
subtail.

This is stronger than nonintegrability of the canonical square-root-energy
envelope and does not introduce a spatial supremum or essential-supremum
definition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Closed scalar-dynamics ingredients -/

private theorem h3PathCanonicalGradientGrowth_closed :
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

private theorem h3PathCanonicalEnergyDifferentiability_closed :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by

  exact
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed

private theorem h3PathBKMZerothVelocityL2LateTail_closed :
    H3PathEnergyClassProducesBKMZerothVelocityL2LateTail := by

  exact
    h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed

/-! ## Tail-local continuation -/

/--
An integrable common vorticity envelope on one strict H³ energy-class tail is
already sufficient for smooth continuation through the terminal time.
-/
theorem h3PathExtension_of_integrableVorticityEnvelopeOnEnergyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hgIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo a T))
    (hgEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hbOld :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        ha.2

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo_zero
        ha

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hbOld.1)
      hbOld.2

  obtain
    ⟨L, hLowB⟩ :=
    h3PathBKMZerothVelocityL2LateTail_closed
      u T hH3
      a hClass
      b hbOld

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VorticityEnvelope u g t := by

    intro t ht

    exact
      hgEnvelope
        t
        ⟨
          lt_trans hbOld.1 ht.1,
          ht.2
        ⟩

  have hgTailIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo b T) := by

    apply
      hgIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hbOld.1 ht.1,
        ht.2
      ⟩

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 hb

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        (h3BKMCanonicalSelectedLogGradientConstant L) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_lowTail
      hH3.navier_stokes
      hb
      hgTail
      hProfile
      hLowB

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant L

  have hB :
      0 ≤ B := by

    dsimp only [B]

    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg_of_lowTail
        hLowB

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VelocityGradientEnvelope u h t := by

    intro t ht

    dsimp only [h, B]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  have hEndpointBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          1 + |h t|
            ≤
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t)) := by

    intro t ht

    have hEt :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        b T h
        (velocityH3EnergyAt u)
        4422 :=
    h3PathCanonicalGradientGrowth_closed
      u T hH3
      b hClassB
      h
      hGradient

  let C : ℝ :=
    4422 * (B + 1)

  have hC :
      0 ≤ C := by

    dsimp only [C]

    exact
      mul_nonneg
        (by norm_num)
        (by linarith)

  have hGrowth :
      BKMLogGrowthInequalityFrom
        b T g
        (velocityH3EnergyAt u)
        C := by

    intro t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)) :=
      hEndpointBound t ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hEnergyGrowth t ht

      _ ≤
        4422
          *
        (
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t))
        )
          * velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (
              mul_le_mul_of_nonneg_left
                hEndpointAt
                (by norm_num)
            )
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        dsimp only [C]

        ring

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico b T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc b q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      hb

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    exact
      h3PathCanonicalEnergyDifferentiability_closed
        u T hH3
        b hClassB
        s hs

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      hb.2
      hgTailIntegrable
      hC
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

  have hTail :
      TerminalTailH3Control u T := by

    refine
      ⟨
        b,
        M,
        hb,
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
On a hypothetical nonextension branch, every common scalar vorticity envelope
valid on an H³ energy-class tail is nonintegrable on that tail.
-/
theorem not_integrableOn_vorticityEnvelope_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hgEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t) :
    ¬ MeasureTheory.IntegrableOn
        g
        (Set.Ioo a T) := by

  intro hgIntegrable

  exact
    hNoExtension
      (
        h3PathExtension_of_integrableVorticityEnvelopeOnEnergyClassTail
          hH3
          hClass
          hgIntegrable
          hgEnvelope
      )

/--
The obstruction persists on every strict later subtail.
-/
theorem not_integrableOn_vorticityEnvelope_on_every_strictSubtail_of_noH3PathExtension
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
          g : ℝ → ℝ,
            (
              ∀ t : ℝ,
                t ∈ Set.Ioo c T →
                  VorticityEnvelope u g t
            )
              →
            ¬ MeasureTheory.IntegrableOn
                g
                (Set.Ioo c T) := by

  intro c hc g hgEnvelope

  have hClassC :
      PreterminalH3EnergyClass u c T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hc.1)
      hc.2

  exact
    not_integrableOn_vorticityEnvelope_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClassC
      hgEnvelope

/-! ## Neutral package -/

/--
Neutral terminal BKM alternative: either the path extends smoothly, or every
common vorticity envelope on every strict terminal H³ subtail is nonintegrable.
-/
theorem smoothContinuationExtension_or_every_terminalVorticityEnvelope_nonintegrable
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
            g : ℝ → ℝ,
              (
                ∀ t : ℝ,
                  t ∈ Set.Ioo c T →
                    VorticityEnvelope u g t
              )
                →
              ¬ MeasureTheory.IntegrableOn
                  g
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
          not_integrableOn_vorticityEnvelope_on_every_strictSubtail_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
