import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTopOrderRadialEscape

/-!
# Top-order radial-tail compactness criterion

The previous checkpoint shows that high-radial full H³ dissipation is
pointwise dominated by four times the top-order fourth-radial density once the
radial gradient magnitude is at least one.

This file packages the corresponding compactness condition directly for the
physical top-order dissipation block `velocityH3Dissipation3At`.

If the top-order density is uniformly radially tight near the endpoint, choose
a top-order cutoff `R₀` at tolerance `δ/4` and replace it by `max R₀ 1`.
Every measurable set outside this enlarged cutoff lies outside `R₀` and also
lies in the region where the full density is at most four times the top-order
density. Hence the full H³ dissipation density is uniformly radially tight.

The radial-tail-only continuation theorem from the preceding compactness
reduction then applies. Thus top-order radial-tail tightness is itself
sufficient for continuation under the retained raw-Fourier `L²` Cauchy and
physical-vorticity endpoint hypotheses.

Equivalently, hypothetical nonextension forces failure of top-order radial-tail
tightness.  No quantitative rate of frequency escape is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationTopOrderRadialTailCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationTopOrderRadialTailCriterion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Top-order radial tightness -/

/--
Uniform radial-tail tightness near `T` for the physical top-order H³
dissipation density

    q(ξ)^4 |û(t,ξ)|².

The hereditary formulation over measurable subsets of the far radial region
matches the already-established full-dissipation compactness interface.
-/
def H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ R : ℝ,
      0 < R
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η
              →
            ∀ S : Set H3FourierPoint3,
              MeasurableSet S
                →
              S ⊆ (h3TerminalRadialFrequencyBelow R)ᶜ
                →
              h3TerminalPhysicalTopDissipationSetMassAt
                  hH3 hClass t ht S
                <
              δ

/-! ## Top-order tightness implies full-dissipation tightness -/

/--
Uniform radial tightness of the physical top-order dissipation density implies
uniform radial tightness of the complete physical H³ dissipation density.
-/
theorem physicalDissipationRadialTailTightAtEndpoint_of_topDissipationRadialTailTightAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTopTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
      hH3 hClass := by

  intro δ hδ

  have hQuarter :
      0 < δ / 4 := by
    linarith

  obtain
    ⟨R₀, hR₀, η, hη, hTopSmall⟩ :=
    hTopTail
      (δ / 4)
      hQuarter

  let R : ℝ :=
    max R₀ 1

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      lt_of_lt_of_le
        zero_lt_one
        (le_max_right R₀ 1)

  refine
    ⟨
      R,
      hR,
      η,
      hη,
      ?_
    ⟩

  intro t ht htNear S hS hSOutsideR

  have hR₀Le :
      R₀ ≤ R := by
    dsimp only [R]
    exact
      le_max_left R₀ 1

  have hOneLeR :
      1 ≤ R := by
    dsimp only [R]
    exact
      le_max_right R₀ 1

  have hSOutsideR₀ :
      S
        ⊆
      (h3TerminalRadialFrequencyBelow R₀)ᶜ := by

    intro ξ hξ

    have hOutsideR :=
      hSOutsideR hξ

    change
      ¬ h3FourierGradientMagnitude ξ < R
        at hOutsideR

    change
      ¬ h3FourierGradientMagnitude ξ < R₀

    intro hBelowR₀

    exact
      hOutsideR
        (lt_of_lt_of_le
          hBelowR₀
          hR₀Le)

  have hOne :
      ∀ ξ ∈ S,
        1 ≤ h3FourierGradientMagnitude ξ := by

    intro ξ hξ

    have hOutsideR :=
      hSOutsideR hξ

    change
      ¬ h3FourierGradientMagnitude ξ < R
        at hOutsideR

    have hRLe :
        R ≤ h3FourierGradientMagnitude ξ :=
      le_of_not_gt
        hOutsideR

    exact
      hOneLeR.trans
        hRLe

  have hTopMassSmall :
      h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass t ht S
        <
      δ / 4 :=
    hTopSmall
      t
      ht
      htNear
      S
      hS
      hSOutsideR₀

  have hCompare :
      h3TerminalPhysicalDissipationSetMassAt
          hH3 hClass t ht S
        ≤
      4
        *
      h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass t ht S :=
    physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
      hH3
      hClass
      ht
      S
      hS
      hOne

  have hScaled :
      4
        *
      h3TerminalPhysicalTopDissipationSetMassAt
        hH3 hClass t ht S
        <
      δ := by
    nlinarith

  exact
    lt_of_le_of_lt
      hCompare
      hScaled

/-! ## Top-order-tail continuation criterion -/

/--
Under the retained endpoint assumptions, top-order physical H³ dissipation
radial-tail tightness is sufficient for smooth continuation.

No separate full-dissipation tightness or equiintegrability hypothesis remains:
the former follows from the top-order tail bound, while the latter follows
from raw Fourier `L²` Cauchy on bounded radial regions.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTopTail :
      H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hFullTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass :=
    physicalDissipationRadialTailTightAtEndpoint_of_topDissipationRadialTailTightAtEndpoint
      hH3
      hClass
      hTopTail

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hFullTail

/-! ## Necessary top-order obstruction under hypothetical nonextension -/

/--
With raw Fourier `L²` Cauchy and one surviving physical-vorticity strong H³
endpoint retained, hypothetical nonextension forces failure of top-order
physical dissipation radial-tail tightness.
-/
theorem not_topDissipationRadialTailTight_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass := by

  intro hTopTail

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalTopDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hTopTail)

/-! ## Neutral formulation -/

/--
Neutral compactness alternative: either the H³ path extends smoothly through
`T`, or top-order physical H³ dissipation radial-tail tightness fails.

The already-proved top-order radial-escape theorem supplies an explicit escape
sequence on the nonextension branch.
-/
theorem smoothContinuationExtension_or_not_physicalTopDissipationRadialTailTight
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
    ¬ H3TerminalPhysicalTopDissipationSingleTimeRadialTailTightAtEndpoint
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
        (not_topDissipationRadialTailTight_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
