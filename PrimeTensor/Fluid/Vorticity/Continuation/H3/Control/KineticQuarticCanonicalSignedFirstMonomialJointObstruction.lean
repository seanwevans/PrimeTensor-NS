import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialSixChannels

/-!
# Joint gradient-excess / six-channel obstruction for the first H³ monomial

The existing signed nonextension theorem implies, for every M >= 0 on each
strict terminal subtail,

    M * E + D < G - 3 * A₀,

where E is the physical H³ energy, D its dissipation,
G = 24 * C₁ * sqrt(E) * E₃, and A₀ is the exact first-monomial aggregate.

Taking M = 27 R and using A₀ as the sum of six signed symmetric channels
forces the unconditional quantitative disjunction

    G - D > 9 * R * E

or one of the six signed symmetric channels is strictly below -R * E.
This does NOT give either estimate automatically: it identifies exactly
which of two obstacles must persist under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- Upper excess of the canonical third-order gradient contribution over
physical H³ dissipation, expressed as a strict normalized inequality. -/
def h3PathCanonicalFirstMonomialGradientExcessAdverseAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ) : Prop :=
  9 * R * velocityH3EnergyAt u t <
    24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
      velocityH3DissipationAt u t

/-- No external gradient-absorption hypothesis is needed to isolate this
joint obstruction: on every strict terminal subtail, either the gradient
surplus is at least of order `R E`, or one of the six physical signed
velocity-component channels is more negative than `-R E`. -/
theorem h3PathCanonical_gradientExcess_or_sixChannel_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (h3PathCanonicalFirstMonomialGradientExcessAdverseAt u t R ∨
        h3PathCanonicalFirstMonomialSixChannelAdverseAt u t R) := by
  have hM : 0 ≤ 27 * R := mul_nonneg (by norm_num) hR
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_firstMonomialAggregateDeficit_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  by_cases hGradient :
      9 * R * velocityH3EnergyAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t
  · exact ⟨t, ht, Or.inl hGradient⟩
  · have hCeiling :
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t ≤
            9 * R * velocityH3EnergyAt u t :=
      le_of_not_gt hGradient
    have hNegative :
        h3PathCanonicalFirstMonomialAggregateAt u t <
          6 * (-R * velocityH3EnergyAt u t) := by
      linarith only [hDeficit, hCeiling]
    exact ⟨t, ht, Or.inr
      (h3PathCanonical_firstMonomial_sixChannel_of_negativeAggregate
        u t R hNegative)⟩

/-- The complementary, nonadverse lower-bound condition on all six signed
component channels, with no constraints on the skew components. -/
def h3PathCanonicalFirstMonomialSixChannelLowerAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ) : Prop :=
  let Q := h3PathCanonicalFirstMonomialComponentAt u t
  let B := -R * velocityH3EnergyAt u t
  B ≤ Q xAxis xAxis ∧
  B ≤ Q yAxis yAxis ∧
  B ≤ Q zAxis zAxis ∧
  B ≤ Q xAxis yAxis + Q yAxis xAxis ∧
  B ≤ Q xAxis zAxis + Q zAxis xAxis ∧
  B ≤ Q yAxis zAxis + Q zAxis yAxis

/-- Six nonadverse channel lower bounds preclude six-channel adversity. -/
theorem h3PathCanonical_sixChannelLower_not_adverse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t R : ℝ}
    (hLower : h3PathCanonicalFirstMonomialSixChannelLowerAt u t R) :
    ¬ h3PathCanonicalFirstMonomialSixChannelAdverseAt u t R := by
  intro hBad
  dsimp [h3PathCanonicalFirstMonomialSixChannelLowerAt] at hLower
  dsimp [h3PathCanonicalFirstMonomialSixChannelAdverseAt] at hBad
  rcases hLower with ⟨hxx, hyy, hzz, hxy, hxz, hyz⟩
  rcases hBad with hx | hy | hz | hxyBad | hxzBad | hyzBad
  · exact (not_lt_of_ge hxx) hx
  · exact (not_lt_of_ge hyy) hy
  · exact (not_lt_of_ge hzz) hz
  · exact (not_lt_of_ge hxy) hxyBad
  · exact (not_lt_of_ge hxz) hxzBad
  · exact (not_lt_of_ge hyz) hyzBad

/-- If all six signed velocity channels are eventually bounded below by
`-R E`, nonextension forces a quantitatively positive gradient excess on
every later subtail; no independent gradient hypothesis is inserted. -/
theorem h3PathCanonical_gradientExcess_of_sixChannelLower_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hLower : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathCanonicalFirstMonomialSixChannelLowerAt u t R) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalFirstMonomialGradientExcessAdverseAt u t R := by
  obtain ⟨t, ht, hAlt⟩ :=
    h3PathCanonical_gradientExcess_or_sixChannel_on_every_subtail
      hH3 hNoExtension hClass hb hd hR
  rcases hAlt with hGradient | hSix
  · exact ⟨t, ht, hGradient⟩
  · exact False.elim
      ((h3PathCanonical_sixChannelLower_not_adverse (hLower t ht)) hSix)

/-- Conversely, a terminal ceiling on the gradient excess forces one of
the six signed channels to be arbitrarily adverse under nonextension.
The ceiling permits a positive gradient excess of size up to `9 R E`. -/
theorem h3PathCanonical_sixChannel_of_gradientExcessCeiling_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t ≤
            9 * R * velocityH3EnergyAt u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalFirstMonomialSixChannelAdverseAt u t R := by
  obtain ⟨t, ht, hAlt⟩ :=
    h3PathCanonical_gradientExcess_or_sixChannel_on_every_subtail
      hH3 hNoExtension hClass hb hd hR
  rcases hAlt with hGradient | hSix
  · exact False.elim ((not_lt_of_ge (hCeiling t ht)) hGradient)
  · exact ⟨t, ht, hSix⟩

/-- A quantitative gradient-excess ceiling and six signed lower bounds
jointly imply H³ continuation. Neither hypothesis is claimed automatic. -/
theorem h3PathCanonical_extension_of_jointGradientCeiling_sixChannelLower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          velocityH3DissipationAt u t ≤
            9 * R * velocityH3EnergyAt u t)
    (hLower : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathCanonicalFirstMonomialSixChannelLowerAt u t R) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hSix⟩ :=
    h3PathCanonical_sixChannel_of_gradientExcessCeiling_on_every_subtail
      hH3 hNoExtension hClass hb hd hR hCeiling
  exact (h3PathCanonical_sixChannelLower_not_adverse (hLower t ht)) hSix

end Euclidean
end Bridge
end PrimeTensor
