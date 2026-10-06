import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Pointwise.Component

/-!
# Local bounded-frequency spectral ceiling on the canonical final witness

The synchronized compactness reduction now leaves only two pointwise
possibilities on the canonical physical-dissipation witness:

* radial frequency escape; or
* one fixed spectral component whose square amplitude diverges while the
  sampled frequencies remain eventually bounded.

The second branch is precisely a failure of local bounded-frequency pointwise
control of the terminal spectral family.  This file isolates that missing
compactness hypothesis explicitly.

The resulting criterion is deliberately neutral: if local spectral pointwise
boundedness is available near the endpoint, hypothetical nonextension forces
frequency escape.  No claim is made here that the local pointwise bound follows
from the current H³ hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
Uniform pointwise boundedness of every weighted spectral velocity component on
each fixed bounded frequency region, uniformly for strict times sufficiently
near `T`.
-/
def H3TerminalVelocitySpectralComponentLocallyBoundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ R : ℝ,
    0 ≤ R →
    ∃ C : ℝ,
      0 ≤ C
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η →
            ∀ j : Fin 3,
              ∀ ξ : H3FourierPoint3,
                h3FourierGradientMagnitude ξ ≤ R →
                h3TerminalSpectralStateComponentSquareAmplitude
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ⟨
                        lt_trans hClass.terminal_start.1 ht.1,
                        ht.2
                      ⟩)
                    j
                    ξ
                  ≤
                C

/--
An eventually bounded-frequency fixed-component blowup sequence contradicts
local spectral component boundedness at the endpoint.
-/
theorem not_boundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf_of_velocitySpectralComponentLocallyBoundedAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLocalBound :
      H3TerminalVelocitySpectralComponentLocallyBoundedAtEndpoint
        hH3 hClass)
    (σ : ℕ → ℝ)
    (hSigma :
      Tendsto σ atTop (𝓝 T)) :
    ¬
      H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf
        hH3 hClass σ := by

  intro hBlowup

  obtain
    ⟨
      R,
      hR,
      j,
      m,
      hmTop,
      ξ,
      hτ,
      _hNear,
      hFreqBound,
      hSigmaM,
      hComponentTop
    ⟩ :=
    hBlowup

  obtain
    ⟨
      C,
      hC,
      η,
      hη,
      hBound
    ⟩ :=
    hLocalBound
      R
      hR

  have hTimeNear :
      ∀ᶠ n : ℕ in atTop,
        dist (σ (m n)) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hSigmaM.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using hn

  have hComponentBound :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalSpectralStateComponentSquareAmplitude
            (h3TerminalVelocitySpectralStateAt
              hH3
              (σ (m n))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ n).1,
                (hτ n).2
              ⟩)
            j
            (ξ n)
          ≤
        C := by

    filter_upwards
      [hTimeNear, hFreqBound]
      with n hNear hFreq

    exact
      hBound
        (σ (m n))
        (hτ n)
        hNear
        j
        (ξ n)
        hFreq

  have hComponentLarge :
      ∀ᶠ n : ℕ in atTop,
        C + 1
          <
        h3TerminalSpectralStateComponentSquareAmplitude
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ (m n))
            ⟨
              lt_trans hClass.terminal_start.1
                (hτ n).1,
              (hτ n).2
            ⟩)
          j
          (ξ n) :=
    hComponentTop.eventually
      (eventually_gt_atTop (C + 1))

  obtain
    ⟨n, hUpper, hLower⟩ :=
    (hComponentBound.and hComponentLarge).exists

  linarith

/--
With local bounded-frequency pointwise spectral control, the canonical final
compactness obstruction cannot use the bounded-frequency fixed-component
branch.  Hypothetical nonextension therefore forces radial frequency escape on
a subsequence of the same canonical physical witness.
-/
theorem exists_fixed_terminalSequence_with_frequencyEscape_of_velocitySpectralComponentLocallyBoundedAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hLocalBound :
      H3TerminalVelocitySpectralComponentLocallyBoundedAtEndpoint
        hH3 hClass)
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
          H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hFinal
    ⟩ :=
    exists_fixed_terminalSequence_with_frequencyEscape_or_boundedFrequencyFixedSpectralComponentBlowup_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hEscape :
      H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
        hH3 hClass σ := by

    rcases hFinal with hEscape | hBlowup

    · exact hEscape

    · exact
        False.elim
          (
            (
              not_boundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf_of_velocitySpectralComponentLocallyBoundedAtEndpoint
                hH3
                hClass
                hLocalBound
                σ
                hSigma
            )
              hBlowup
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
      hEscape
    ⟩

/--
Neutral continuation formulation.

Either the solution extends smoothly through `T`, or the local
bounded-frequency spectral-component ceiling fails, or the canonical physical
dissipation witness has radial frequency escape.
-/
theorem smoothContinuationExtension_or_not_velocitySpectralComponentLocallyBoundedAtEndpoint_or_fixedTerminalFrequencyEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    ¬
      H3TerminalVelocitySpectralComponentLocallyBoundedAtEndpoint
        hH3 hClass
      ∨
    (
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
            H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
              hH3 hClass σ
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · right

    by_cases hLocalBound :
        H3TerminalVelocitySpectralComponentLocallyBoundedAtEndpoint
          hH3 hClass

    · right

      exact
        exists_fixed_terminalSequence_with_frequencyEscape_of_velocitySpectralComponentLocallyBoundedAtEndpoint_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
          hH3
          hClass
          hPhysical
          hCauchy
          hLocalBound
          hExtension
          hε

    · exact
        Or.inl
          hLocalBound

end

end Euclidean
end Bridge
end PrimeTensor
