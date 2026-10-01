import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Uniform.Absolute.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Frequency.Escape.Density.Blowup

/-!
# Radial-tail compactness as the remaining physical dissipation criterion

The preceding checkpoint proves that terminal raw Fourier `L²` Cauchy control
automatically yields uniform absolute continuity of the physical H³
dissipation mass on every fixed bounded radial region.

Therefore global uniform absolute continuity is no longer an independent
compactness hypothesis once radial-tail tightness is assumed:

* choose the radial cutoff supplied by tail tightness at mass tolerance
  `δ / 2`;
* use bounded-radial uniform absolute continuity for the inside piece;
* use radial-tail tightness for the outside piece;
* split an arbitrary measurable set into its inside and outside parts.

This promotes radial-tail tightness to whole-space uniform absolute continuity.
The existing compactness continuation criterion then needs only radial-tail
tightness, besides the retained raw-Fourier `L²` Cauchy assumption and one
surviving physical-vorticity strong H³ endpoint.

Consequently, under hypothetical nonextension, radial-tail tightness itself
must fail.  The previously proved extraction theorems turn this into an
explicit radial dissipation escape sequence, and then into a pointwise
frequency-escape sequence with positive dissipation density.

These are necessary-condition statements only; they do not assert that a
nonextendible Navier--Stokes path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationRadialTailCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationRadialTailCriterion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Radial tightness promotes bounded-radial absolute continuity globally -/

/--
Under terminal raw Fourier `L²` Cauchy control, radial-tail tightness of the
physical H³ dissipation densities implies their whole-space uniform absolute
continuity near the terminal time.
-/
theorem physicalDissipationUniformAbsoluteContinuityAtEndpoint_of_velocityRawFourierL2Cauchy_of_radialTailTight
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass) :
    H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
      hH3 hClass := by

  intro δ hδ

  have hHalf :
      0 < δ / 2 := by
    linarith

  obtain
    ⟨R, hR, etaTail, hetaTail, hTailSmall⟩ :=
    hTail
      (δ / 2)
      hHalf

  have hLocal :=
    physicalDissipationUniformAbsoluteContinuityBelowRadialCutoffAtEndpoint_of_velocityRawFourierL2Cauchy
      hH3
      hClass
      hCauchy
      hR

  obtain
    ⟨alpha, halpha, etaLocal, hetaLocal, hLocalSmall⟩ :=
    hLocal
      (δ / 2)
      hHalf

  let eta : ℝ :=
    min etaTail etaLocal

  have heta :
      0 < eta := by
    dsimp only [eta]
    exact
      lt_min
        hetaTail
        hetaLocal

  refine
    ⟨
      alpha,
      halpha,
      eta,
      heta,
      ?_
    ⟩

  intro t ht htNear S hS hVolume

  have htNearTail :
      dist t T < etaTail :=
    htNear.trans_le
      (min_le_left etaTail etaLocal)

  have htNearLocal :
      dist t T < etaLocal :=
    htNear.trans_le
      (min_le_right etaTail etaLocal)

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt
          hH3
          t
          htAbs)
        ξ

  let B : Set H3FourierPoint3 :=
    h3TerminalRadialFrequencyBelow R

  have hFInt :
      Integrable f volume := by
    dsimp only [f, htAbs]
    simpa only using
      (h3TerminalSpectralDissipationSingleDensity_integrable
        hH3
        hClass
        ht)

  have hBMeas :
      MeasurableSet B := by
    dsimp only [B]
    exact
      measurableSet_h3TerminalRadialFrequencyBelow R

  have hTailPieceMeas :
      MeasurableSet (S \ B) :=
    hS.diff
      hBMeas

  have hTailPieceSubset :
      S \ B ⊆ Bᶜ := by
    intro ξ hξ
    exact hξ.2

  have hInsideSmall :
      (∫ ξ in S ∩ B, f ξ ∂volume)
        <
      δ / 2 := by

    dsimp only [f, B, htAbs]

    exact
      hLocalSmall
        t
        ht
        htNearLocal
        S
        hS
        hVolume

  have hOutsideSmall :
      (∫ ξ in S \ B, f ξ ∂volume)
        <
      δ / 2 := by

    dsimp only [f, B, htAbs] at *

    exact
      hTailSmall
        t
        ht
        htNearTail
        (S \ h3TerminalRadialFrequencyBelow R)
        hTailPieceMeas
        hTailPieceSubset

  have hSplit :
      (∫ ξ in S, f ξ ∂volume)
        =
      (∫ ξ in S ∩ B, f ξ ∂volume)
        +
      (∫ ξ in S \ B, f ξ ∂volume) := by

    have hRaw :=
      integral_inter_add_sdiff₀
        (μ := volume)
        (s := S)
        hBMeas.nullMeasurableSet
        hFInt.integrableOn

    exact
      hRaw.symm

  change
    (∫ ξ in S, f ξ ∂volume)
      <
    δ

  rw [hSplit]

  linarith

/-! ## Radial-tail-only continuation criterion -/

/--
The physical compactness continuation criterion can now be stated with
radial-tail tightness as its only dissipation compactness hypothesis.

Uniform absolute continuity is generated automatically from the retained raw
Fourier `L²` Cauchy condition on bounded radial regions and the supplied radial
tail control.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hUniform :
      H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
        hH3 hClass :=
    physicalDissipationUniformAbsoluteContinuityAtEndpoint_of_velocityRawFourierL2Cauchy_of_radialTailTight
      hH3
      hClass
      hCauchy
      hTail

  exact
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessUniformAbsoluteContinuity_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy
      hTail
      hUniform

/-! ## Hypothetical nonextension forces radial escape -/

/--
Under the retained endpoint assumptions, hypothetical nonextension forces
failure of physical H³ dissipation radial-tail tightness.
-/
theorem not_radialTailTight_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ¬ H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass := by

  intro hTail

  exact
    hNoExtension
      (smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationRadialTailTightness_of_actualVorticityStrongH3EndpointPath
        hH3
        hClass
        hPhysical
        hCauchy
        hTail)

/--
Hypothetical nonextension therefore yields an explicit radial-escape sequence:
a fixed positive amount of physical H³ dissipation mass lies beyond radial
cutoff `n+1` at times converging to the terminal time.
-/
theorem physicalDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalDissipationRadialEscapeSequence
      hH3 hClass := by

  apply
    physicalDissipationRadialEscapeSequence_of_not_radialTailTight
      hH3
      hClass

  exact
    not_radialTailTight_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy

/--
The radial mass-escape obstruction contains a pointwise frequency-escape
sequence with positive physical H³ dissipation density.
-/
theorem physicalDissipationFrequencyEscapePointSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalDissipationFrequencyEscapePointSequence
      hH3 hClass := by

  exact
    physicalDissipationFrequencyEscapePointSequence_of_radialEscapeSequence
      hH3
      hClass
      (physicalDissipationRadialEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy)

/-! ## Neutral positive formulation -/

/--
Neutral endpoint alternative: under the retained hypotheses, either the path
extends smoothly through the terminal time, or there is a pointwise terminal
sequence with radial frequency tending to infinity and positive physical H³
dissipation density.

No assertion is made here that the nonextension branch is realizable.
-/
theorem smoothContinuationExtension_or_physicalDissipationFrequencyEscapePointSequence
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
    H3TerminalPhysicalDissipationFrequencyEscapePointSequence
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
        (physicalDissipationFrequencyEscapePointSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
