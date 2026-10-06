import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Frequency.Escape.Density.Blowup

/-!
# Pointwise concentration--compactness on the canonical final witness

The same-witness concentration--compactness theorem gives a subsequence of the
canonical physical-dissipation sequence `σ` on which either

* fixed positive dissipation mass escapes past radial scale `n+1`, or
* fixed positive mass concentrates on sets of volume below `1/(n+1)`.

This file applies the already-proved point-extraction lemmas without replacing
that witness.

* Radial mass escape gives a frequency `ξ n` on the exact selected time
  `σ (m n)`, with radial magnitude at least `n+1` and positive dissipation
  density.
* Small-volume concentration gives a frequency `ξ n` on the exact selected
  time `σ (m n)` where dissipation density exceeds `δ (n+1)` and therefore
  diverges.

Thus the final concentration--compactness alternative becomes pointwise while
retaining the canonical single-time witness and its explicit reindexer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
Pointwise frequency escape realized on a subsequence of a prescribed terminal
time sequence.
-/
def H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop
        ∧
      ∃ ξ : ℕ → H3FourierPoint3,
        ∃ hτ :
          ∀ n : ℕ,
            σ (m n) ∈ Set.Ioo a T,
          (
            ∀ n : ℕ,
              dist (σ (m n)) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              (n : ℝ) + 1
                  ≤
                h3FourierGradientMagnitude (ξ n)
                ∧
              0
                  <
                h3TerminalSpectralDissipationSingleDensity
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (σ (m n))
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hτ n).1,
                      (hτ n).2
                    ⟩)
                  (ξ n)
          )
            ∧
          Tendsto
            (fun n : ℕ => σ (m n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              h3FourierGradientMagnitude (ξ n))
            atTop
            atTop

/--
Pointwise dissipation-density blowup realized on a subsequence of a prescribed
terminal time sequence.
-/
def H3TerminalPhysicalDissipationDensityBlowupPointSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop
        ∧
      ∃ ξ : ℕ → H3FourierPoint3,
        ∃ hτ :
          ∀ n : ℕ,
            σ (m n) ∈ Set.Ioo a T,
          (
            ∀ n : ℕ,
              dist (σ (m n)) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              δ * ((n : ℝ) + 1)
                  <
                h3TerminalSpectralDissipationSingleDensity
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (σ (m n))
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hτ n).1,
                      (hτ n).2
                    ⟩)
                  (ξ n)
          )
            ∧
          Tendsto
            (fun n : ℕ => σ (m n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalSpectralDissipationSingleDensity
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (σ (m n))
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hτ n).1,
                      (hτ n).2
                    ⟩)
                  (ξ n)
            )
            atTop
            atTop

private theorem tendsto_atTop_of_natSucc_le_finalWitness
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) + 1 ≤ f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2 ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt M

  filter_upwards [eventually_ge_atTop N] with n hn

  have hCast :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

  have hM :
      M < (n : ℝ) + 1 := by
    linarith

  exact
    le_trans
      hM.le
      (hf n)

private theorem tendsto_atTop_of_pos_mul_natSucc_lt_finalWitness
    {δ : ℝ}
    (hδ : 0 < δ)
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        δ * ((n : ℝ) + 1) < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2 ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (M / δ)

  filter_upwards [eventually_ge_atTop N] with n hn

  have hCast :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

  have hMND :
      M < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).1 hN

  have hNDle :
      (N : ℝ) * δ
        ≤
      ((n : ℝ) + 1) * δ := by

    exact
      mul_le_mul_of_nonneg_right
        (by linarith)
        hδ.le

  have hMScale :
      M < δ * ((n : ℝ) + 1) := by

    have h :=
      lt_of_lt_of_le
        hMND
        hNDle

    simpa only [mul_comm] using
      h

  exact
    le_of_lt
      (lt_trans hMScale (hf n))

/--
A radial-escape subsequence of `σ` contains a pointwise frequency-escape
subsequence of the same `σ`.
-/
theorem physicalDissipationFrequencyEscapePointSubsequenceOf_of_radialEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
      hH3 hClass σ := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      S,
      hData,
      hSigmaM
    ⟩ :=
    hEscape

  have hChoice :
      ∀ n : ℕ,
        ∃ ξ : H3FourierPoint3,
          ∃ ht :
            σ (m n) ∈ Set.Ioo a T,
            dist (σ (m n)) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
              ∧
            (n : ℝ) + 1
                ≤
              h3FourierGradientMagnitude ξ
              ∧
            0
                <
              h3TerminalSpectralDissipationSingleDensity
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (σ (m n))
                  ⟨
                    lt_trans hClass.terminal_start.1
                      ht.1,
                    ht.2
                  ⟩)
                ξ := by

    intro n

    obtain
      ⟨
        ht,
        hNear,
        hSMeas,
        hSSubset,
        hMass
      ⟩ :=
      hData n

    have hMassPos :
        0
          <
        h3TerminalPhysicalDissipationSetMassAt
          hH3 hClass (σ (m n)) ht (S n) :=
      lt_of_lt_of_le
        hδ
        hMass

    obtain
      ⟨
        ξ,
        hξS,
        hξPositive
      ⟩ :=
      exists_mem_positive_spectralDissipationDensity_of_positive_setMass
        hH3
        hClass
        ht
        (S n)
        hSMeas
        hMassPos

    have hOutside :=
      hSSubset
        hξS

    have hRadial :
        (n : ℝ) + 1
          ≤
        h3FourierGradientMagnitude ξ := by

      change
        ¬
          h3FourierGradientMagnitude ξ
            <
          (n : ℝ) + 1
        at hOutside

      exact
        le_of_not_gt
          hOutside

    exact
      ⟨
        ξ,
        ht,
        hNear,
        hRadial,
        hξPositive
      ⟩

  choose ξ hτ hPoint using hChoice

  have hRadialTop :
      Tendsto
        (
          fun n : ℕ =>
            h3FourierGradientMagnitude (ξ n)
        )
        atTop
        atTop :=
    tendsto_atTop_of_natSucc_le_finalWitness
      (fun n => (hPoint n).2.1)

  exact
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      ξ,
      hτ,
      hPoint,
      hSigmaM,
      hRadialTop
    ⟩

/--
A small-volume concentration subsequence of `σ` contains a pointwise
dissipation-density blowup subsequence of the same `σ`.
-/
theorem physicalDissipationDensityBlowupPointSubsequenceOf_of_smallVolumeConcentrationSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hConcentration :
      H3TerminalPhysicalDissipationSmallVolumeConcentrationSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalDissipationDensityBlowupPointSubsequenceOf
      hH3 hClass σ := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      S,
      hData,
      hSigmaM
    ⟩ :=
    hConcentration

  have hChoice :
      ∀ n : ℕ,
        ∃ ξ : H3FourierPoint3,
          ∃ ht :
            σ (m n) ∈ Set.Ioo a T,
            dist (σ (m n)) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
              ∧
            δ * ((n : ℝ) + 1)
                <
              h3TerminalSpectralDissipationSingleDensity
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (σ (m n))
                  ⟨
                    lt_trans hClass.terminal_start.1
                      ht.1,
                    ht.2
                  ⟩)
                ξ := by

    intro n

    obtain
      ⟨
        ht,
        hNear,
        hSMeas,
        hVolume,
        hMass
      ⟩ :=
      hData n

    obtain
      ⟨
        ξ,
        _hξS,
        hDensity
      ⟩ :=
      exists_mem_spectralDissipationDensity_gt_linear_of_smallVolume_setMass
        hH3
        hClass
        ht
        (S n)
        hSMeas
        hδ
        n
        hVolume
        hMass

    exact
      ⟨
        ξ,
        ht,
        hNear,
        hDensity
      ⟩

  choose ξ hτ hPoint using hChoice

  have hDensityTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt
                hH3
                (σ (m n))
                ⟨
                  lt_trans hClass.terminal_start.1
                    (hτ n).1,
                  (hτ n).2
                ⟩)
              (ξ n)
        )
        atTop
        atTop :=
    tendsto_atTop_of_pos_mul_natSucc_lt_finalWitness
      hδ
      (fun n => (hPoint n).2)

  exact
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      ξ,
      hτ,
      hPoint,
      hSigmaM,
      hDensityTop
    ⟩

/--
The concentration--compactness alternative on the final canonical physical
witness can be sharpened pointwise without replacing that witness.

Either a subsequence of the returned `σ` carries frequencies escaping to
infinity with positive dissipation density, or a subsequence of that same `σ`
carries pointwise spectral dissipation density diverging to infinity.
-/
theorem exists_fixed_terminalSequence_with_pointwisePhysicalDissipationConcentrationCompactnessDichotomy_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          (
            H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
                hH3 hClass σ
              ∨
            H3TerminalPhysicalDissipationDensityBlowupPointSubsequenceOf
                hH3 hClass σ
          ) := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hDichotomy
    ⟩ :=
    exists_fixed_terminalSequence_with_physicalDissipationConcentrationCompactnessDichotomy_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hPointwise :
      H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
          hH3 hClass σ
        ∨
      H3TerminalPhysicalDissipationDensityBlowupPointSubsequenceOf
          hH3 hClass σ := by

    rcases hDichotomy with hEscape | hConcentration

    · exact
        Or.inl
          (
            physicalDissipationFrequencyEscapePointSubsequenceOf_of_radialEscapeSubsequenceOf
              hH3
              hClass
              σ
              hEscape
          )

    · exact
        Or.inr
          (
            physicalDissipationDensityBlowupPointSubsequenceOf_of_smallVolumeConcentrationSubsequenceOf
              hH3
              hClass
              σ
              hConcentration
          )

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPointwise
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
