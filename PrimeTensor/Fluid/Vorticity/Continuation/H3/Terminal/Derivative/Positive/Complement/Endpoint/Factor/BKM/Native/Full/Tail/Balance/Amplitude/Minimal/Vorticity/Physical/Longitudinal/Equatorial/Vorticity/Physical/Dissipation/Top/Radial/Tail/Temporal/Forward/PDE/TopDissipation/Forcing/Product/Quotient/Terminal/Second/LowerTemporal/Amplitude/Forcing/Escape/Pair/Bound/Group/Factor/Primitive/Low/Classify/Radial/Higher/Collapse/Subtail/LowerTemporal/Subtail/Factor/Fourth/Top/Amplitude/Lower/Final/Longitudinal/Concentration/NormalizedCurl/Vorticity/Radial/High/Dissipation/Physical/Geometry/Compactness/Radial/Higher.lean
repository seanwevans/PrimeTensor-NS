import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade

/-!
# Higher radial cascade on the canonical physical witness

The canonical final witness now has a same-witness radial escape subsequence:
a fixed positive amount of full physical H³ dissipation survives outside radial
cutoff `n+1` at times `σ (m n)`.

Outside that cutoff, full dissipation controls the top fourth-radial block up
to the universal factor four.  The standard radial domination estimate then
forces every strictly higher extended radial moment to satisfy

    ofReal ((((n+1)^2)^r) * δ) ≤ higherMoment_r (σ (m n))

for one fixed `δ > 0`, simultaneously for every `r ≠ 0`.

Thus every higher radial moment diverges along the same reindexed canonical
single-time sequence.  No fresh terminal sequence is introduced.
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
Every strictly higher extended radial moment diverges along a subsequence of a
prescribed canonical terminal sequence.
-/
def H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
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
      ∃ hτ :
        ∀ n : ℕ,
          σ (m n) ∈ Set.Ioo a T,
        (
          ∀ n : ℕ,
            dist (σ (m n)) T
              <
            (1 : ℝ) / ((n : ℝ) + 1)
        )
          ∧
        Tendsto
          (fun n : ℕ => σ (m n))
          atTop
          (𝓝 T)
          ∧
        ∀ r : ℕ,
          r ≠ 0
            →
          (
            (
              ∀ n : ℕ,
                ENNReal.ofReal
                  (
                    (((n : ℝ) + 1) ^ 2) ^ r
                      *
                    δ
                  )
                  ≤
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass r (σ (m n)) (hτ n)
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalExtendedHigherRadialMomentAt
                    hH3 hClass r (σ (m n)) (hτ n)
              )
              atTop
              (𝓝 ∞)
          )

/--
A same-witness full physical-dissipation radial escape subsequence forces the
whole higher-radial hierarchy to diverge along that exact subsequence.
-/
theorem extendedHigherRadialMomentUniversalEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
      hH3 hClass σ := by

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
        ∃ ht :
          σ (m n) ∈ Set.Ioo a T,
          dist (σ (m n)) T
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
              hH3 hClass (σ (m n)) ht (S n) := by

    intro n
    exact hData n

  choose ht hNear hSMeas hOutside hMass using hChoice

  let δTop : ℝ :=
    δ / 4

  have hδTop :
      0 < δTop := by
    dsimp only [δTop]
    positivity

  have hTopMass :
      ∀ n : ℕ,
        δTop
          ≤
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (σ (m n)) (ht n) (S n) := by

    intro n

    have hOne :
        ∀ ξ ∈ S n,
          1 ≤ h3FourierGradientMagnitude ξ := by

      intro ξ hξ

      have hOutsideξ :=
        hOutside n hξ

      have hRadial :
          (n : ℝ) + 1
            ≤
          h3FourierGradientMagnitude ξ := by

        change
          ¬
            h3FourierGradientMagnitude ξ
              <
            (n : ℝ) + 1
          at hOutsideξ

        exact
          le_of_not_gt
            hOutsideξ

      have hOneLe :
          1 ≤ (n : ℝ) + 1 := by

        have hn0 :
            0 ≤ (n : ℝ) := by
          exact_mod_cast Nat.zero_le n

        linarith

      exact
        hOneLe.trans
          hRadial

    have hCompare :
        h3TerminalPhysicalDissipationSetMassAt
            hH3 hClass (σ (m n)) (ht n) (S n)
          ≤
        4 *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (σ (m n)) (ht n) (S n) :=
      physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
        hH3
        hClass
        (ht n)
        (S n)
        (hSMeas n)
        hOne

    dsimp only [δTop]

    linarith [hMass n]

  refine
    ⟨
      δTop,
      hδTop,
      m,
      hmTop,
      ht,
      hNear,
      hSigmaM,
      ?_
    ⟩

  intro r hr

  have hLower :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            (((n : ℝ) + 1) ^ 2) ^ r
              *
            δTop
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass r (σ (m n)) (ht n) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hR :
        0 ≤ R := by
      dsimp only [R]
      positivity

    have hFactorNonneg :
        0 ≤ (R ^ 2) ^ r :=
      pow_nonneg
        (sq_nonneg R)
        r

    have hMassScaled :
        (R ^ 2) ^ r * δTop
          ≤
        (R ^ 2) ^ r
          *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (σ (m n)) (ht n) (S n) :=
      mul_le_mul_of_nonneg_left
        (hTopMass n)
        hFactorNonneg

    have hOfRealScaled :
        ENNReal.ofReal
          ((R ^ 2) ^ r * δTop)
          ≤
        ENNReal.ofReal
          (
            (R ^ 2) ^ r
              *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (σ (m n)) (ht n) (S n)
          ) :=
      ENNReal.ofReal_le_ofReal
        hMassScaled

    have hExtended :=
      ofReal_radial_sq_pow_mul_topDissipationSetMass_le_extendedHigherRadialMoment_of_setOutside
        hH3
        hClass
        r
        (ht n)
        hR
        (S n)
        (hSMeas n)
        (hOutside n)

    exact
      hOfRealScaled.trans
        hExtended

  have hRadius :
      Tendsto
        (fun n : ℕ => (n : ℝ) + 1)
        atTop
        atTop := by

    exact
      tendsto_atTop_add_const_right
        atTop
        (1 : ℝ)
        tendsto_natCast_atTop_atTop

  have hSquare :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) ^ 2)
        atTop
        atTop := by

    simpa only [pow_two] using
      hRadius.atTop_mul_atTop₀
        hRadius

  have hPowerMap :
      Tendsto
        (fun x : ℝ => x ^ r)
        atTop
        atTop :=
    tendsto_pow_atTop
      hr

  have hPower :
      Tendsto
        (
          fun n : ℕ =>
            (((n : ℝ) + 1) ^ 2) ^ r
        )
        atTop
        atTop :=
    hPowerMap.comp
      hSquare

  have hRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            (((n : ℝ) + 1) ^ 2) ^ r
              *
            δTop
        )
        atTop
        atTop := by

    have hScaled :=
      hPower.const_mul_atTop
        hδTop

    simpa only [mul_comm] using
      hScaled

  have hOfRealLowerTop :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                (((n : ℝ) + 1) ^ 2) ^ r
                  *
                δTop
              )
        )
        atTop
        (𝓝 ∞) := by

    exact
      ENNReal.tendsto_ofReal_atTop.comp
        hRealLowerTop

  have hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass r (σ (m n)) (ht n)
        )
        atTop
        (𝓝 ∞) := by

    exact
      tendsto_nhds_top_mono'
        hOfRealLowerTop
        hLower

  exact
    ⟨
      hLower,
      hMomentTop
    ⟩

/--
The final resolved-PDE canonical physical witness has one cofinal subsequence
on which every strictly higher radial moment diverges simultaneously.
-/
theorem exists_fixed_terminalSequence_with_canonicalHigherRadialMomentUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
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
      hEscape
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalPhysicalDissipationRadialEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hHigher :
      H3TerminalPhysicalExtendedHigherRadialMomentUniversalEscapeSubsequenceOf
        hH3 hClass σ :=
    extendedHigherRadialMomentUniversalEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
      hH3
      hClass
      σ
      hEscape

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hHigher
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
