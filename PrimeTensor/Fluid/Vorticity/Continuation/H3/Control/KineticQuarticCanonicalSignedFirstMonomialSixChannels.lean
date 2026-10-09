import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialAggregate

/-!
# Canonical first-monomial aggregate: six symmetric velocity-component channels

The preceding exact mixed-partial identities established `I₃ = 3 A₀`, with

  A₀ = ∑ j r i k l, ⟨∂ᵢ∂ₖ∂ₗuⱼ, (∂ₖ∂ₗuᵣ)(∂ᵢ∂ᵣuⱼ)⟩.

Regroup the 243 terms by the two *velocity-component* indices `(j,r)`.
The resulting 3-by-3 matrix `Q(j,r)` has a symmetric and an antisymmetric
part; the sum of the antisymmetric part is exactly zero. Consequently `A₀`
is the sum of just six signed channel aggregates: three diagonal entries
and three symmetric off-diagonal pairs.

The skew cancellation here is finite-index algebra, not a new integration by
parts or a claim of favorable sign for the surviving symmetric channels.
The earlier signed transport witness localizes to one of those six channels
under the same explicit additional gradient-absorption hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable local instance axisFintypeH3FirstMonomialSixChannels
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual signed `D³u·(D²u D²u)` first-monomial contribution
with fixed velocity-component indices `(j,r)`, summed over the three
ordered spatial derivative axes. -/
noncomputable def h3PathCanonicalFirstMonomialComponentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j r : PrimeTensor.Axis Depth.three) : ℝ :=
  ∑ i : PrimeTensor.Axis Depth.three,
    ∑ k : PrimeTensor.Axis Depth.three,
      ∑ l : PrimeTensor.Axis Depth.three,
        h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0

/-- The canonical physical monomial aggregate is the complete three-by-three
signed matrix sum of its component channels. -/
theorem h3PathCanonical_firstMonomialAggregate_eq_componentSum
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          h3PathCanonicalFirstMonomialComponentAt u t j r := by
  rfl

/-- The exchange-antisymmetric component of the physical signed matrix. -/
noncomputable def h3PathCanonicalFirstMonomialSkewComponentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j r : PrimeTensor.Axis Depth.three) : ℝ :=
  (h3PathCanonicalFirstMonomialComponentAt u t j r -
    h3PathCanonicalFirstMonomialComponentAt u t r j) / 2

/-- The exchange-symmetric component of the physical signed matrix. -/
noncomputable def h3PathCanonicalFirstMonomialSymmetricComponentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j r : PrimeTensor.Axis Depth.three) : ℝ :=
  (h3PathCanonicalFirstMonomialComponentAt u t j r +
    h3PathCanonicalFirstMonomialComponentAt u t r j) / 2

/-- Signed exchange of the two velocity indices reverses the skew channel. -/
theorem h3PathCanonical_firstMonomialSkew_exchange
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j r : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalFirstMonomialSkewComponentAt u t j r =
      -h3PathCanonicalFirstMonomialSkewComponentAt u t r j := by
  unfold h3PathCanonicalFirstMonomialSkewComponentAt
  ring

/-- All exchange-antisymmetric channels cancel *exactly* in the full
component-index sum. This is a finite-sum cancellation, not a PDE estimate. -/
theorem h3PathCanonical_firstMonomialSkew_total_eq_zero
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    (∑ j : PrimeTensor.Axis Depth.three,
      ∑ r : PrimeTensor.Axis Depth.three,
        h3PathCanonicalFirstMonomialSkewComponentAt u t j r) = 0 := by
  unfold h3PathCanonicalFirstMonomialSkewComponentAt
  simp only [axis_sum_three]
  ring

/-- Consequently the canonical aggregate is precisely the signed sum of
the exchange-symmetric velocity-component channels. -/
theorem h3PathCanonical_firstMonomialAggregate_eq_symmetricComponentSum
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          h3PathCanonicalFirstMonomialSymmetricComponentAt u t j r := by
  rw [h3PathCanonical_firstMonomialAggregate_eq_componentSum]
  unfold h3PathCanonicalFirstMonomialSymmetricComponentAt
  simp only [axis_sum_three]
  ring

/-- A nine-entry sum on three velocity axes is exactly three diagonal
entries plus the three signed off-diagonal pairs. -/
private theorem h3PathCanonical_nine_to_six_componentChannels
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ j : PrimeTensor.Axis Depth.three,
      ∑ r : PrimeTensor.Axis Depth.three, f j r) =
      (f xAxis xAxis + f yAxis yAxis + f zAxis zAxis) +
      ((f xAxis yAxis + f yAxis xAxis) +
        (f xAxis zAxis + f zAxis xAxis) +
        (f yAxis zAxis + f zAxis yAxis)) := by
  simp only [axis_sum_three]
  ring

/-- Six exact physical signed channels account for the entire type-0
aggregate: three diagonal component channels and three symmetric pairs. -/
theorem h3PathCanonical_firstMonomialAggregate_eq_sixChannels
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      (h3PathCanonicalFirstMonomialComponentAt u t xAxis xAxis +
        h3PathCanonicalFirstMonomialComponentAt u t yAxis yAxis +
        h3PathCanonicalFirstMonomialComponentAt u t zAxis zAxis) +
      ((h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis +
          h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis) +
        (h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis +
          h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis) +
        (h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis +
          h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis)) := by
  rw [h3PathCanonical_firstMonomialAggregate_eq_componentSum]
  exact h3PathCanonical_nine_to_six_componentChannels
    (h3PathCanonicalFirstMonomialComponentAt u t)

/-- A six-channel signed sum below six copies of `B` contains a real
channel strictly below `B`; no positivity is needed. -/
private theorem h3PathCanonical_sixChannel_pigeonhole
    {a b c d e f B : ℝ}
    (hSum : (a + b + c) + (d + e + f) < 6 * B) :
    a < B ∨ b < B ∨ c < B ∨ d < B ∨ e < B ∨ f < B := by
  by_contra hNone
  have ha : B ≤ a := by
    apply le_of_not_gt
    intro ha
    exact hNone (Or.inl ha)
  have hb : B ≤ b := by
    apply le_of_not_gt
    intro hb
    exact hNone (Or.inr (Or.inl hb))
  have hc : B ≤ c := by
    apply le_of_not_gt
    intro hc
    exact hNone (Or.inr (Or.inr (Or.inl hc)))
  have hd : B ≤ d := by
    apply le_of_not_gt
    intro hd
    exact hNone (Or.inr (Or.inr (Or.inr (Or.inl hd))))
  have he : B ≤ e := by
    apply le_of_not_gt
    intro he
    exact hNone (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
  have hf : B ≤ f := by
    apply le_of_not_gt
    intro hf
    exact hNone (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hf)))))
  linarith only [hSum, ha, hb, hc, hd, he, hf]

/-- A concrete six-channel adverse witness predicate. Each channel is an
actual signed spatial-energy sum of 27 canonical triple-product pairings
(or the sum of two such component entries), not an absolute-value envelope. -/
def h3PathCanonicalFirstMonomialSixChannelAdverseAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ) : Prop :=
  let Q := h3PathCanonicalFirstMonomialComponentAt u t
  let B := -R * velocityH3EnergyAt u t
  Q xAxis xAxis < B ∨
  Q yAxis yAxis < B ∨
  Q zAxis zAxis < B ∨
  Q xAxis yAxis + Q yAxis xAxis < B ∨
  Q xAxis zAxis + Q zAxis xAxis < B ∨
  Q yAxis zAxis + Q zAxis yAxis < B

/-- A sufficiently negative full canonical signed aggregate forces a
specific diagonal or symmetric off-diagonal physical component channel. -/
theorem h3PathCanonical_firstMonomial_sixChannel_of_negativeAggregate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t R : ℝ)
    (hNegative : h3PathCanonicalFirstMonomialAggregateAt u t <
      6 * (-R * velocityH3EnergyAt u t)) :
    h3PathCanonicalFirstMonomialSixChannelAdverseAt u t R := by
  rw [h3PathCanonical_firstMonomialAggregate_eq_sixChannels] at hNegative
  change
    h3PathCanonicalFirstMonomialComponentAt u t xAxis xAxis <
        -R * velocityH3EnergyAt u t ∨
    h3PathCanonicalFirstMonomialComponentAt u t yAxis yAxis <
        -R * velocityH3EnergyAt u t ∨
    h3PathCanonicalFirstMonomialComponentAt u t zAxis zAxis <
        -R * velocityH3EnergyAt u t ∨
    h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis +
      h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis <
        -R * velocityH3EnergyAt u t ∨
    h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis +
      h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis <
        -R * velocityH3EnergyAt u t ∨
    h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis +
      h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis <
        -R * velocityH3EnergyAt u t
  exact h3PathCanonical_sixChannel_pigeonhole hNegative

/-- Assuming *separately* that physical dissipation absorbs the gradient
commutator, hypothetical nonextension requires a genuinely adverse one of
six symmetric velocity-component channels arbitrarily late on every subtail. -/
theorem h3PathCanonical_sixChannel_adversity_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalFirstMonomialSixChannelAdverseAt u t R := by
  have hM : 0 ≤ 18 * R := mul_nonneg (by norm_num) hR
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_firstMonomialAggregateDeficit_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have hAbs := hAbsorption t ht
  have hNegative : h3PathCanonicalFirstMonomialAggregateAt u t <
      6 * (-R * velocityH3EnergyAt u t) := by
    linarith only [hDeficit, hAbs]
  exact ⟨t, ht,
    h3PathCanonical_firstMonomial_sixChannel_of_negativeAggregate
      u t R hNegative⟩

/-- A tail-wide lower bound on all six *symmetric* component channels,
together with gradient absorption, excludes the physical nonextension witness.
No lower bound is assumed on any exchange-antisymmetric channel. -/
theorem h3PathCanonical_extension_of_sixChannelLowerBounds
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t)
    (hLower : ∀ t : ℝ, t ∈ Set.Ioo d T →
      let Q := h3PathCanonicalFirstMonomialComponentAt u t
      let B := -R * velocityH3EnergyAt u t
      B ≤ Q xAxis xAxis ∧
      B ≤ Q yAxis yAxis ∧
      B ≤ Q zAxis zAxis ∧
      B ≤ Q xAxis yAxis + Q yAxis xAxis ∧
      B ≤ Q xAxis zAxis + Q zAxis xAxis ∧
      B ≤ Q yAxis zAxis + Q zAxis yAxis) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hBad⟩ :=
    h3PathCanonical_sixChannel_adversity_on_every_subtail
      hH3 hNoExtension hClass hb hd hR hAbsorption
  have hBounds := hLower t ht
  dsimp [h3PathCanonicalFirstMonomialSixChannelAdverseAt] at hBad
  dsimp only at hBounds
  rcases hBounds with ⟨hxx, hyy, hzz, hxy, hxz, hyz⟩
  rcases hBad with hx | hy | hz | hxyBad | hxzBad | hyzBad
  · exact (not_lt_of_ge hxx) hx
  · exact (not_lt_of_ge hyy) hy
  · exact (not_lt_of_ge hzz) hz
  · exact (not_lt_of_ge hxy) hxyBad
  · exact (not_lt_of_ge hxz) hxzBad
  · exact (not_lt_of_ge hyz) hyzBad

end Euclidean
end Bridge
end PrimeTensor
