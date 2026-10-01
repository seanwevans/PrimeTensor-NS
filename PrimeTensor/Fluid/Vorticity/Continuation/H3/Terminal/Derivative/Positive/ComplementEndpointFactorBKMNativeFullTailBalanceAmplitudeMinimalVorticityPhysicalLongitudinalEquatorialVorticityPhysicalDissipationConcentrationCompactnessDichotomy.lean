import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationBoundedBadConeVolumeVanishing

/-!
# Physical dissipation concentration--compactness dichotomy

The bounded-cone geometry is now automatic.  Thus, under the retained
raw-Fourier L² Cauchy hypothesis and one surviving physical-vorticity strong
H³ endpoint, hypothetical nonextension can persist only if one of the two
analytic compactness mechanisms fails.

This file converts those failures into explicit terminal sequences.

* Failure of radial-tail tightness gives a fixed positive amount of physical
  H³ dissipation mass on measurable sets lying outside radial cutoff `n+1`.
* Failure of uniform absolute continuity gives a fixed positive amount of
  physical H³ dissipation mass on measurable sets whose Fourier-space volume
  is smaller than `1/(n+1)`.

In both branches the selected times converge to the terminal time.

This is a concentration--compactness alternative only.  It does not assert
that either obstruction is realizable by a singular Navier--Stokes solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationConcentrationCompactnessDichotomy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationConcentrationCompactnessDichotomy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Localized one-time mass -/

/-- Real physical H³ dissipation mass of a measurable Fourier-space set at one
strict energy-class time. -/
noncomputable def h3TerminalPhysicalDissipationSetMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (S : Set H3FourierPoint3) : ℝ :=
  ∫ ξ in S,
    h3TerminalSpectralDissipationSingleDensity
      (h3TerminalVelocitySpectralStateAt
        hH3
        t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
      ξ
    ∂volume

/-! ## Two explicit compactness-failure sequence packages -/

/--
Radial escape of physical H³ dissipation.

A fixed positive mass survives on measurable sets lying outside the radial
cutoff `n+1`, at times approaching the terminal time.
-/
def H3TerminalPhysicalDissipationRadialEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ τ : ℕ → ℝ,
      ∃ S : ℕ → Set H3FourierPoint3,
        (
          ∀ n : ℕ,
            ∃ ht : τ n ∈ Set.Ioo a T,
              dist (τ n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              MeasurableSet (S n)
                ∧
              S n
                  ⊆
                (h3TerminalRadialFrequencyBelow
                    ((n : ℝ) + 1))ᶜ
                ∧
              δ
                  ≤
                h3TerminalPhysicalDissipationSetMassAt
                  hH3 hClass (τ n) ht (S n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)

/--
Small-volume concentration of physical H³ dissipation.

A fixed positive mass survives on measurable sets whose volume is smaller than
the explicit scale `1/(n+1)`, at times approaching the terminal time.
-/
def H3TerminalPhysicalDissipationSmallVolumeConcentrationSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ τ : ℕ → ℝ,
      ∃ S : ℕ → Set H3FourierPoint3,
        (
          ∀ n : ℕ,
            ∃ ht : τ n ∈ Set.Ioo a T,
              dist (τ n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              MeasurableSet (S n)
                ∧
              volume (S n)
                  <
                ENNReal.ofReal
                  ((1 : ℝ) / ((n : ℝ) + 1))
                ∧
              δ
                  ≤
                h3TerminalPhysicalDissipationSetMassAt
                  hH3 hClass (τ n) ht (S n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)

/-! ## Terminal localization utility -/

private theorem tendsto_terminal_of_dist_lt_one_div_natSucc
    {T : ℝ}
    {τ : ℕ → ℝ}
    (hτ :
      ∀ n : ℕ,
        dist (τ n) T
          <
        (1 : ℝ) / ((n : ℝ) + 1)) :
    Tendsto τ atTop (𝓝 T) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩

  intro n hn

  have hDenN :
      0 < (N : ℝ) + 1 := by
    positivity

  have hInvN :
      (1 : ℝ) / ((n : ℝ) + 1)
        ≤
      1 / ((N : ℝ) + 1) := by
    exact
      one_div_le_one_div_of_le
        hDenN
        (by
          have hCast :
              (N : ℝ) ≤ n := by
            exact_mod_cast hn
          linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by
    have hNPlus :
        1 / ε < (N : ℝ) + 1 := by
      linarith [hN]

    have hMul :
        1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hε).1 hNPlus

    exact
      (div_lt_iff₀ hDenN).2
        (by
          simpa only [mul_comm, one_mul] using hMul)

  exact
    lt_trans
      (hτ n)
      (lt_of_le_of_lt hInvN hSmallN)

/-! ## Extract radial escape from failure of tail tightness -/

/--
Failure of terminal radial-tail tightness yields an explicit radial-escape
sequence with fixed positive dissipation mass.
-/
theorem physicalDissipationRadialEscapeSequence_of_not_radialTailTight
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFailure :
      ¬ H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
          hH3 hClass) :
    H3TerminalPhysicalDissipationRadialEscapeSequence
      hH3 hClass := by

  classical

  unfold
    H3TerminalPhysicalDissipationSingleTimeRadialTailTightAtEndpoint
      at hFailure

  push Not at hFailure

  obtain ⟨δ, hδ, hFailure⟩ :=
    hFailure

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          ∃ S : Set H3FourierPoint3,
            ∃ ht : t ∈ Set.Ioo a T,
              dist t T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              MeasurableSet S
                ∧
              S
                  ⊆
                (h3TerminalRadialFrequencyBelow
                    ((n : ℝ) + 1))ᶜ
                ∧
              δ
                  ≤
                h3TerminalPhysicalDissipationSetMassAt
                  hH3 hClass t ht S := by

    intro n

    have hR :
        0 < (n : ℝ) + 1 := by
      positivity

    have hη :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    obtain
      ⟨t, ht, hNear, S, hSMeas, hSSubset, hMass⟩ :=
      hFailure
        ((n : ℝ) + 1)
        hR
        ((1 : ℝ) / ((n : ℝ) + 1))
        hη

    refine
      ⟨
        t,
        S,
        ht,
        hNear,
        hSMeas,
        hSSubset,
        ?_
      ⟩

    exact hMass

  choose τ S ht hData using hChoice

  have hτTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_dist_lt_one_div_natSucc
      (fun n => (hData n).1)

  refine
    ⟨
      δ,
      hδ,
      τ,
      S,
      ?_,
      hτTendsto
    ⟩

  intro n

  exact
    ⟨
      ht n,
      hData n
    ⟩

/-! ## Extract concentration from failure of uniform absolute continuity -/

/--
Failure of uniform absolute continuity yields an explicit terminal sequence of
sets with vanishing prescribed volume scale and fixed positive dissipation
mass.
-/
theorem physicalDissipationSmallVolumeConcentrationSequence_of_not_uniformAbsoluteContinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFailure :
      ¬ H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
          hH3 hClass) :
    H3TerminalPhysicalDissipationSmallVolumeConcentrationSequence
      hH3 hClass := by

  classical

  unfold
    H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityAtEndpoint
      at hFailure

  push Not at hFailure

  obtain ⟨δ, hδ, hFailure⟩ :=
    hFailure

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          ∃ S : Set H3FourierPoint3,
            ∃ ht : t ∈ Set.Ioo a T,
              dist t T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              MeasurableSet S
                ∧
              volume S
                  <
                ENNReal.ofReal
                  ((1 : ℝ) / ((n : ℝ) + 1))
                ∧
              δ
                  ≤
                h3TerminalPhysicalDissipationSetMassAt
                  hH3 hClass t ht S := by

    intro n

    let α : ℝ≥0∞ :=
      ENNReal.ofReal
        ((1 : ℝ) / ((n : ℝ) + 1))

    have hScale :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    have hα :
        0 < α := by
      dsimp only [α]
      exact ENNReal.ofReal_pos.2 hScale

    have hη :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      exact hScale

    obtain
      ⟨t, ht, hNear, S, hSMeas, hSVolume, hMass⟩ :=
      hFailure
        α
        hα
        ((1 : ℝ) / ((n : ℝ) + 1))
        hη

    refine
      ⟨
        t,
        S,
        ht,
        hNear,
        hSMeas,
        ?_,
        ?_
      ⟩

    · simpa only [α] using hSVolume

    · exact hMass

  choose τ S ht hData using hChoice

  have hτTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_dist_lt_one_div_natSucc
      (fun n => (hData n).1)

  refine
    ⟨
      δ,
      hδ,
      τ,
      S,
      ?_,
      hτTendsto
    ⟩

  intro n

  exact
    ⟨
      ht n,
      hData n
    ⟩

/-! ## Concentration--compactness obstruction under hypothetical nonextension -/

/--
After the bounded-cone geometry has been discharged, hypothetical nonextension
forces one of two explicit physical H³ dissipation mechanisms:

* radial escape to arbitrarily large frequencies; or
* concentration on Fourier-space sets of arbitrarily small volume.

The assumptions are exactly the retained raw-Fourier L² Cauchy hypothesis and
one surviving physical-vorticity strong H³ endpoint used by the preceding
compactness continuation theorem.
-/
theorem physicalDissipationRadialEscape_or_smallVolumeConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        hH3 hClass
      ∨
    H3TerminalPhysicalDissipationSmallVolumeConcentrationSequence
        hH3 hClass := by

  rcases
      radialTailTight_or_uniformAbsoluteContinuity_fails_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy
    with hTail | hConcentration

  · exact
      Or.inl
        (physicalDissipationRadialEscapeSequence_of_not_radialTailTight
          hH3 hClass hTail)

  · exact
      Or.inr
        (physicalDissipationSmallVolumeConcentrationSequence_of_not_uniformAbsoluteContinuity
          hH3 hClass hConcentration)

/--
Neutral formulation: under the retained endpoint hypotheses, either the path
extends smoothly through `T`, or physical H³ dissipation exhibits radial
escape, or it exhibits small-volume concentration.
-/
theorem smoothContinuationExtension_or_physicalDissipationRadialEscape_or_smallVolumeConcentration
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
    H3TerminalPhysicalDissipationRadialEscapeSequence
        hH3 hClass
      ∨
    H3TerminalPhysicalDissipationSmallVolumeConcentrationSequence
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (physicalDissipationRadialEscape_or_smallVolumeConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
