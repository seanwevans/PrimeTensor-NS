import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Angular.Vanishing.Criterion

/-!
# Physical H³ dissipation angular vanishing from compactness hypotheses

The existing physical continuation criterion asks for uniform vanishing of the
single-time H³ dissipation mass in shrinking high-radial equatorial cones.
This file separates that property into the two standard analytic compactness
inputs and one purely geometric input.

* Uniform radial-tail tightness makes every measurable piece sufficiently far
  out in frequency carry small physical H³ dissipation mass, uniformly on a
  terminal time tail.
* Uniform absolute continuity of the single-time dissipation integrals makes
  every sufficiently small-measure frequency set carry small mass, again
  uniformly on a terminal time tail.
* Bounded bad-cone volume vanishing says that, after intersecting with a fixed
  radial ball, the high-radial equatorial bad cone has volume tending to zero
  with its angular aperture.

Splitting the localized bad cone at a large radial radius then gives the
physical angular-vanishing criterion already used by the continuation theorem.
The only remaining input after this checkpoint is the Euclidean bounded-cone
volume calculation.

All conclusions remain conditional continuation statements.  No singular
solution and no unconditional global regularity statement is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationAngularVanishingFromTightnessEquiintegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationAngularVanishingFromTightnessEquiintegrability :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Uniform terminal compactness hypotheses -/

/--
Uniform radial-tail tightness for the one-time physical H³ dissipation
 densities near the terminal time.

The hereditary formulation over measurable subsets of the far radial region is
convenient for localization.  For a nonnegative density it follows from the
usual uniform bound on the whole radial tail.
-/
def H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
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
              (∫ ξ in S,
                  h3TerminalSpectralDissipationSingleDensity
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
                    ξ
                  ∂volume)
                <
              δ

/--
Uniform absolute continuity of the one-time physical H³ dissipation integrals
with respect to Fourier-space volume near the terminal time.
-/
def H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ α : ℝ≥0∞,
      0 < α
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
              volume S < α
                →
              (∫ ξ in S,
                  h3TerminalSpectralDissipationSingleDensity
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
                    ξ
                  ∂volume)
                <
              δ

/--
Purely geometric bounded-frequency shrinking-cone statement.

For every fixed outer radial cutoff and every positive volume tolerance, a
sufficiently thin bad cone has small volume between the fixed inner cutoff
`ρ` and that outer cutoff.
-/
def H3TerminalLongitudinalBoundedBadConeVolumeVanishingAtCutoff
    (i : Fin 3)
    (ρ : ℝ) : Prop :=
  ∀ R : ℝ,
    ∀ α : ℝ≥0∞,
      0 < α
        →
      ∃ κ₀ : ℝ,
        0 < κ₀
          ∧
        ∀ κ : ℝ,
          0 < κ
            →
          κ < κ₀
            →
          volume
              ((h3TerminalLongitudinalAngularBadCone i κ
                  \
                h3TerminalRadialFrequencyBelow ρ)
                ∩
              h3TerminalRadialFrequencyBelow R)
            <
          α

/-! ## Compactness implies physical angular vanishing -/

/--
Radial-tail tightness, uniform absolute continuity, and bounded bad-cone volume
vanishing imply the physical single-time angular-vanishing property at the
same fixed positive radial cutoff.
-/
theorem physicalDissipationSingleTimeAngularVanishingAtEndpoint_of_radialTailTight_of_uniformAbsoluteContinuity_of_boundedBadConeVolumeVanishing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (ρ : ℝ)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass)
    (hUniformAbsoluteContinuity :
      H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
        hH3 hClass)
    (hConeVolume :
      H3TerminalLongitudinalBoundedBadConeVolumeVanishingAtCutoff
        i ρ) :
    H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
      hH3 hClass i ρ := by

  intro δ hδ

  have hHalf : 0 < δ / 2 := by
    linarith

  obtain
    ⟨R, hR, ηTail, hηTail, hTailSmall⟩ :=
    hTail (δ / 2) hHalf

  obtain
    ⟨α, hα, ηUniform, hηUniform, hUniformSmall⟩ :=
    hUniformAbsoluteContinuity (δ / 2) hHalf

  obtain
    ⟨κ₀, hκ₀, hConeSmall⟩ :=
    hConeVolume R α hα

  let η : ℝ := min ηTail ηUniform

  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min hηTail hηUniform

  refine
    ⟨κ₀, hκ₀, η, hη, ?_⟩

  intro t ht htNear κ hκ hκSmall

  have htNearTail : dist t T < ηTail :=
    htNear.trans_le (min_le_left _ _)

  have htNearUniform : dist t T < ηUniform :=
    htNear.trans_le (min_le_right _ _)

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs)
        ξ

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  let B : Set H3FourierPoint3 :=
    h3TerminalRadialFrequencyBelow R

  have hFInt : Integrable f volume := by
    dsimp only [f, htAbs]
    simpa only using
      (h3TerminalSpectralDissipationSingleDensity_integrable
        hH3 hClass ht)

  have hSMeas : MeasurableSet S := by
    dsimp only [S]
    exact
      (measurableSet_h3TerminalLongitudinalAngularBadCone i κ).diff
        (measurableSet_h3TerminalRadialFrequencyBelow ρ)

  have hBMeas : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_h3TerminalRadialFrequencyBelow R

  have hMiddleMeas : MeasurableSet (S ∩ B) :=
    hSMeas.inter hBMeas

  have hTailPieceMeas : MeasurableSet (S \ B) :=
    hSMeas.diff hBMeas

  have hMiddleVolume : volume (S ∩ B) < α := by
    dsimp only [S, B]
    exact hConeSmall κ hκ hκSmall

  have hMiddleSmall :
      (∫ ξ in S ∩ B, f ξ ∂volume)
        <
      δ / 2 := by
    dsimp only [f, htAbs]
    exact
      hUniformSmall
        t
        ht
        htNearUniform
        (S ∩ B)
        hMiddleMeas
        hMiddleVolume

  have hTailPieceSubset :
      S \ B ⊆ Bᶜ := by
    intro ξ hξ
    exact hξ.2

  have hTailPieceSmall :
      (∫ ξ in S \ B, f ξ ∂volume)
        <
      δ / 2 := by
    dsimp only [f, htAbs]
    exact
      hTailSmall
        t
        ht
        htNearTail
        (S \ B)
        hTailPieceMeas
        hTailPieceSubset

  have hSplit :
      (∫ ξ in S, f ξ ∂volume)
        =
      (∫ ξ in S ∩ B, f ξ ∂volume)
        +
      (∫ ξ in S \ B, f ξ ∂volume) := by
    have hSplit' :=
      integral_inter_add_sdiff₀
        (μ := volume)
        (s := S)
        hBMeas.nullMeasurableSet
        hFInt.integrableOn
    exact hSplit'.symm

  unfold h3TerminalPhysicalDissipationBadConeHighRadialRealMass

  change
    (∫ ξ in S, f ξ ∂volume)
      <
    δ

  rw [hSplit]

  linarith

/-! ## Direct continuation from compactness hypotheses -/

/--
If radial-tail tightness and uniform absolute continuity hold near the endpoint,
and the bounded bad-cone volume statement holds at every positive radial
cutoff, then the retained raw-Fourier `L²` Cauchy hypothesis and one surviving
physical-vorticity strong H³ endpoint imply smooth continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessEquiintegrability_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysicalVorticity :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass)
    (hUniformAbsoluteContinuity :
      H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
        hH3 hClass)
    (hConeVolume :
      ∀ ρ : ℝ,
        0 < ρ
          →
        H3TerminalLongitudinalBoundedBadConeVolumeVanishingAtCutoff
          i ρ) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  apply
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationSingleTimeAngularVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysicalVorticity
      hCauchy

  intro ρ hρ

  exact
    physicalDissipationSingleTimeAngularVanishingAtEndpoint_of_radialTailTight_of_uniformAbsoluteContinuity_of_boundedBadConeVolumeVanishing
      hH3
      hClass
      i
      ρ
      hTail
      hUniformAbsoluteContinuity
      (hConeVolume ρ hρ)

/-! ## Remaining obstruction under hypothetical nonextension -/

/--
Under the retained endpoint hypotheses and the two analytic compactness
properties, hypothetical nonextension forces failure of the purely geometric
bounded bad-cone volume property at some positive radial cutoff.

The next checkpoint is therefore reduced to proving that bounded Euclidean
bad-cone volume vanishing is automatic.
-/
theorem exists_not_boundedBadConeVolumeVanishing_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessEquiintegrability_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysicalVorticity :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hTail :
      H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
        hH3 hClass)
    (hUniformAbsoluteContinuity :
      H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
        hH3 hClass) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ¬ H3TerminalLongitudinalBoundedBadConeVolumeVanishingAtCutoff
          i ρ := by

  by_contra hNoFailure

  push_neg at hNoFailure

  have hExtension :=
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationTightnessEquiintegrability_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysicalVorticity
      hCauchy
      hTail
      hUniformAbsoluteContinuity
      hNoFailure

  exact hNoExtension hExtension

end

end Euclidean
end Bridge
end PrimeTensor
