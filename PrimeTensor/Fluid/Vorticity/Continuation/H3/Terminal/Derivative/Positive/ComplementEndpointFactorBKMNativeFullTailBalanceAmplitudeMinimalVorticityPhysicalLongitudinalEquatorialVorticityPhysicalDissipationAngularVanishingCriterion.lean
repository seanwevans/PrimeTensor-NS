import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationScalarLowerBound

/-!
# Physical H³ dissipation angular-vanishing continuation criterion

The preceding checkpoints reduce the surviving high-radial endpoint obstruction
to a single-time concentration of the *physical* H³ dissipation density in
shrinking equatorial cones.

This file records the complementary positive criterion.

At one fixed positive radial cutoff `ρ`, assume that for every `δ > 0` there is
a sufficiently thin equatorial cone and a sufficiently late terminal tail on
which the localized one-time physical H³ dissipation mass is `< δ`, uniformly
in the strict time slice.  Then each of the two single-time masses controlling
the spectral pair defect is small.  The elementary pair estimate from the
previous files therefore gives the spectral dissipation-difference angular
vanishing property.

Consequently, if this physical angular equiintegrability holds at every
positive radial cutoff, then the retained raw-Fourier `L²` Cauchy hypothesis
and one surviving physical-vorticity strong H³ endpoint imply smooth
continuation.

Conversely, under hypothetical nonextension the already isolated high-radial
branch forces failure of this physical single-time angular-vanishing property
at some positive radial cutoff.  This is a characterization of the remaining
obstruction, not an assertion that the obstruction actually occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationAngularVanishingCriterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationAngularVanishingCriterion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Physical single-time angular vanishing -/

/--
Uniform angular equiintegrability of the one-time physical H³ dissipation mass
near the terminal time, at one fixed positive radial cutoff.
-/
def H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (ρ : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ κ₀ : ℝ,
      0 < κ₀
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η
              →
            ∀ κ : ℝ,
              0 < κ
                →
              κ < κ₀
                →
              h3TerminalPhysicalDissipationBadConeHighRadialRealMass
                  hH3 i κ ρ t
                  ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
                <
              δ

/-! ## Physical angular vanishing implies spectral pair angular vanishing -/

/--
Uniform single-time physical dissipation angular vanishing controls the
pair-difference spectral dissipation obstruction at the same radial cutoff.
-/
theorem spectralDissipationDifferenceAngularVanishingAtEndpoint_of_physicalDissipationSingleTimeAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (ρ : ℝ)
    (hPhysical :
      H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
        hH3 hClass i ρ) :
    H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
      hH3 i ρ := by

  intro δ hδ

  obtain ⟨κ₀, hκ₀, ηPhysical, hηPhysical, hSmall⟩ :=
    hPhysical (δ / 16) (by positivity)

  let ηTail : ℝ := (T - a) / 2

  have hηTail : 0 < ηTail := by
    dsimp only [ηTail]
    have haT : a < T := hClass.terminal_start.2
    linarith

  let η : ℝ := min ηPhysical ηTail

  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min hηPhysical hηTail

  refine ⟨κ₀, hκ₀, η, hη, ?_⟩

  intro s t hs ht hsNear htNear κ hκ hκSmall

  have hsNearPhysical : dist s T < ηPhysical :=
    hsNear.trans_le (min_le_left _ _)

  have htNearPhysical : dist t T < ηPhysical :=
    htNear.trans_le (min_le_left _ _)

  have hsNearTail : dist s T < ηTail :=
    hsNear.trans_le (min_le_right _ _)

  have htNearTail : dist t T < ηTail :=
    htNear.trans_le (min_le_right _ _)

  have hsTail : s ∈ Set.Ioo a T := by
    have hsDiffNeg : s - T < 0 := sub_neg.mpr hs.2
    have hsNearTail' := hsNearTail
    rw [Real.dist_eq, abs_of_neg hsDiffNeg] at hsNearTail'
    dsimp only [ηTail] at hsNearTail'
    constructor
    · linarith
    · exact hs.2

  have htTail : t ∈ Set.Ioo a T := by
    have htDiffNeg : t - T < 0 := sub_neg.mpr ht.2
    have htNearTail' := htNearTail
    rw [Real.dist_eq, abs_of_neg htDiffNeg] at htNearTail'
    dsimp only [ηTail] at htNearTail'
    constructor
    · linarith
    · exact ht.2

  have hMs :=
    hSmall s hsTail hsNearPhysical κ hκ hκSmall

  have hMt :=
    hSmall t htTail htNearPhysical κ hκ hκSmall

  let Ms : ℝ :=
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass
      hH3 i κ ρ s
      ⟨lt_trans hClass.terminal_start.1 hsTail.1, hsTail.2⟩

  let Mt : ℝ :=
    h3TerminalPhysicalDissipationBadConeHighRadialRealMass
      hH3 i κ ρ t
      ⟨lt_trans hClass.terminal_start.1 htTail.1, htTail.2⟩

  have hMs' : Ms < δ / 16 := by
    simpa only [Ms] using hMs

  have hMt' : Mt < δ / 16 := by
    simpa only [Mt] using hMt

  have hReal : 8 * (Ms + Mt) < δ := by
    linarith

  have hPairEq :=
    physicalDissipationPairBadConeHighRadialMajorantMass_eq_ofReal_eight_mul_realMass_add
      hH3 hClass hsTail htTail i κ ρ

  dsimp only at hPairEq

  have hPairLt :
      h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
          hH3 i κ ρ s t
          ⟨lt_trans hClass.terminal_start.1 hsTail.1, hsTail.2⟩
          ⟨lt_trans hClass.terminal_start.1 htTail.1, htTail.2⟩
        <
      ENNReal.ofReal δ := by
    calc
      h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
          hH3 i κ ρ s t
          ⟨lt_trans hClass.terminal_start.1 hsTail.1, hsTail.2⟩
          ⟨lt_trans hClass.terminal_start.1 htTail.1, htTail.2⟩
          =
        ENNReal.ofReal (8 * (Ms + Mt)) := by
          simpa only [Ms, Mt] using hPairEq
      _ < ENNReal.ofReal δ := by
        exact
          (ENNReal.ofReal_lt_ofReal_iff hδ).2
            hReal

  have hControlLe :
      h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i κ ρ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht)
        ≤
      h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
          hH3 i κ ρ s t
          ⟨lt_trans hClass.terminal_start.1 hsTail.1, hsTail.2⟩
          ⟨lt_trans hClass.terminal_start.1 htTail.1, htTail.2⟩ := by
    simpa only using
      (spectralDissipationDifferenceControlMass_le_physicalDissipationPairMajorantMass
        hH3 i κ ρ s t hs ht)

  exact hControlLe.trans_lt hPairLt

/-! ## Direct physical continuation criterion -/

/--
If the one-time physical H³ dissipation is uniformly angularly vanishing near
`T` at every positive radial cutoff, then the retained raw-Fourier `L²` Cauchy
hypothesis and one surviving physical-vorticity endpoint give smooth
continuation.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_physicalDissipationSingleTimeAngularVanishing_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysicalVorticity :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hDissipationAngular :
      ∀ ρ : ℝ,
        0 < ρ
          →
        H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
          hH3 hClass i ρ) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  apply
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_spectralDissipationDifferenceAngularVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysicalVorticity
      hCauchy

  intro ρ hρ

  exact
    spectralDissipationDifferenceAngularVanishingAtEndpoint_of_physicalDissipationSingleTimeAngularVanishingAtEndpoint
      hH3
      hClass
      i
      ρ
      (hDissipationAngular ρ hρ)

/-! ## Necessary failure of physical angular vanishing under nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity endpoint force failure of
the physical single-time dissipation angular-vanishing criterion at some
positive radial cutoff.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_physicalDissipationSingleTimeAngularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ
          ∧
        ¬ H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
          hH3 hClass i ρ := by

  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hNotSpectral⟩ :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_spectralDissipationAngularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  intro hPhysicalAngular

  exact
    hNotSpectral
      (spectralDissipationDifferenceAngularVanishingAtEndpoint_of_physicalDissipationSingleTimeAngularVanishingAtEndpoint
        hH3
        hClass
        i
        ρ
        hPhysicalAngular)

end

end Euclidean
end Bridge
end PrimeTensor
