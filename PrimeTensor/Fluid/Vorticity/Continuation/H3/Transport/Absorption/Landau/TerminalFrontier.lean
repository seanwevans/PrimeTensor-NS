import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.Loop
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportIntegrability
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Actual.Gradient.Closure

/-!
# Terminal frontier for the current canonical Landau absorption coefficient

The current Landau commutator closure supplies, pointwise on every strict H³
energy-class time,

    -T_H3(t)
      ≤
    D(t)
      +
    c_L(t) E(t),

where

    c_L(t)
      =
    4422 *
      (1 +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
          * sqrt(E(t))).

The generic path-specific absorption theorem already proves that an integrable
coefficient in such an inequality is sufficient for smooth continuation.

Therefore, for the *current* Landau closure, integrability of the canonical
coefficient on even one terminal H³ energy-class tail implies continuation.

Equivalently, hypothetical nonextension forces the current canonical Landau
coefficient to be nonintegrable on every strict terminal subtail.

This identifies the present analytic frontier without adding a new assumption:
the pointwise Landau absorption estimate is closed, but its canonical temporal
coefficient cannot lie in `L¹` on a hypothetical nonextension branch.  Any
successful improvement through this route must therefore produce a genuinely
smaller time coefficient, additional coercive cancellation, or some other
mechanism that avoids requiring integrability of the current `c_L`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Path-specific continuation from the current Landau coefficient -/

/--
If the current canonical Landau transport coefficient is integrable on one H³
energy-class tail, then the path extends smoothly across the terminal time.
-/
theorem h3PathExtension_of_integrableCanonicalLandauTransportCoefficientOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCoefficient :
      MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    h3PathExtension_of_transportDissipationAbsorptionOnTail
      hH3
      hClass
      hCoefficient
      (
        fun t ht =>
          h3TransportDissipationAbsorptionAt_of_currentLandau
            hH3
            hClass
            ht
      )

/-! ## Nonintegrability under hypothetical nonextension -/

/--
Hypothetical nonextension forces the current canonical Landau coefficient to
be nonintegrable on every H³ energy-class terminal tail.
-/
theorem not_integrableOn_canonicalLandauTransportCoefficient_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo a T) := by

  intro hCoefficient

  exact
    hNoExtension
      (
        h3PathExtension_of_integrableCanonicalLandauTransportCoefficientOnTail
          hH3
          hClass
          hCoefficient
      )

/--
Every strict subtail of an H³ energy-class tail inherits the same obstruction.
-/
theorem not_integrableOn_canonicalLandauTransportCoefficient_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo b T) := by

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hb.1)
      hb.2

  exact
    not_integrableOn_canonicalLandauTransportCoefficient_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClassB

/-! ## Positive continuation contrapositives -/

/--
Integrability of the current canonical Landau coefficient on any strict
terminal subtail forces smooth continuation.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_canonicalLandauTransportCoefficient_on_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCoefficient :
      MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo b T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hb.1)
      hb.2

  exact
    h3PathExtension_of_integrableCanonicalLandauTransportCoefficientOnTail
      hH3
      hClassB
      hCoefficient

/-! ## Neutral package -/

/--
Neutral current-Landau frontier.

Either smooth continuation exists, or the canonical coefficient produced by
the present Landau closure is nonintegrable on every strict terminal subtail.
-/
theorem smoothContinuationExtension_or_canonicalLandauCoefficient_nonintegrable_on_every_strictSubtail
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
      ∀ b : ℝ,
        b ∈ Set.Ioo a T →
        ¬ MeasureTheory.IntegrableOn
            (h3PathCanonicalLandauTransportCoefficient u)
            (Set.Ioo b T)
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · right

    intro b hb

    exact
      not_integrableOn_canonicalLandauTransportCoefficient_on_strictSubtail_of_noH3PathExtension
        hH3
        hExtension
        hClass
        hb

end

end Euclidean
end Bridge
end PrimeTensor
