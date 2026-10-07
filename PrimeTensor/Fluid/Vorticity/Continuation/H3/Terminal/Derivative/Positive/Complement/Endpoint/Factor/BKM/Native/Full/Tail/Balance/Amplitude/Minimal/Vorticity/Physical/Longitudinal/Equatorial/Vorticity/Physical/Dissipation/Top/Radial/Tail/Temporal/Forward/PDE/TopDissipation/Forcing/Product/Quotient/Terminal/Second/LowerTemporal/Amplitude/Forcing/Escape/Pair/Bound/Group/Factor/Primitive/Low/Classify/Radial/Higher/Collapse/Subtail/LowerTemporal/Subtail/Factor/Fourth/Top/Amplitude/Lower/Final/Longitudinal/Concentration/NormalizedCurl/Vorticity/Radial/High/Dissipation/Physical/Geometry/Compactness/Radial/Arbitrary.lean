import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Arbitrary.Coercive.Radial.Weight

/-!
# Arbitrary coercive radial cascade on the canonical physical witness

The canonical final physical witness now has a radial-escape subsequence
`σ (m n)` carrying a fixed positive amount of full H³ dissipation outside
radius `n+1`.

Full dissipation controls the top fourth-radial block by the universal factor
four.  Once that top mass is retained, the existing arbitrary-floor estimate
shows that any real radial weight `w` satisfying only

    w(r) -> +∞

must produce a divergent extended weighted top-dissipation moment along this
same subsequence.

No monotonicity, nonnegativity, polynomial structure, or fresh terminal
sequence is required.
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
Every real coercive radial weight diverges along one subsequence of a
prescribed canonical terminal sequence.
-/
def H3TerminalPhysicalArbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf
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
        ∀ w : ℝ → ℝ,
          H3TerminalArbitraryCoerciveRadialWeight w
            →
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
                  hH3 hClass w (σ (m n)) (hτ n)
            )
            atTop
            (𝓝 ∞)

/--
A same-witness full physical-dissipation radial escape subsequence forces every
real coercive radial weighted top-dissipation moment to diverge along that
exact subsequence.
-/
theorem arbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalArbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf
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

  intro w hw

  apply
    ENNReal.tendsto_nhds_top_iff_nat.2

  intro k

  let L : ℝ :=
    ((k : ℝ) + 1) / δTop

  have hL :
      0 < L := by

    dsimp only [L]

    exact
      div_pos
        (by positivity)
        hδTop

  have hWeightEventually :
      ∀ᶠ r : ℝ in atTop,
        L < w r :=
    hw.tendsto_atTop.eventually
      (eventually_gt_atTop L)

  obtain
    ⟨R₀, hR₀⟩ :=
    eventually_atTop.1
      hWeightEventually

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

  have hCutoffPast :
      ∀ᶠ n : ℕ in atTop,
        R₀ ≤ (n : ℝ) + 1 :=
    hRadius.eventually
      (eventually_ge_atTop R₀)

  filter_upwards [hCutoffPast] with n hn

  have hFloor :
      ∀ r : ℝ,
        (n : ℝ) + 1 ≤ r
          →
        L ≤ w r := by

    intro r hr

    exact
      le_of_lt
        (hR₀ r
          (hn.trans hr))

  have hSetLower :=
    ofReal_floor_mul_topDissipationSetMass_le_extendedRadialWeightedTopDissipationMoment_of_setOutside'
      hH3
      hClass
      w
      (ht n)
      hL.le
      hFloor
      (S n)
      (hSMeas n)
      (hOutside n)

  have hMassScaled :
      L * δTop
        ≤
      L *
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (σ (m n)) (ht n) (S n) :=
    mul_le_mul_of_nonneg_left
      (hTopMass n)
      hL.le

  have hOfRealMassScaled :
      ENNReal.ofReal
        (L * δTop)
        ≤
      ENNReal.ofReal
        (
          L *
            h3TerminalPhysicalTopDissipationSetMassAt
              hH3 hClass (σ (m n)) (ht n) (S n)
        ) :=
    ENNReal.ofReal_le_ofReal
      hMassScaled

  have hLower :
      ENNReal.ofReal
        (L * δTop)
        ≤
      h3TerminalPhysicalExtendedRadialWeightedTopDissipationMomentAt
        hH3 hClass w (σ (m n)) (ht n) :=
    hOfRealMassScaled.trans
      hSetLower

  have hCancel :
      L * δTop
        =
      (k : ℝ) + 1 := by

    dsimp only [L]

    field_simp [ne_of_gt hδTop]

  have hNatStrict :
      (k : ℝ≥0∞)
        <
      ENNReal.ofReal
        ((k : ℝ) + 1) := by

    simpa only [
      ENNReal.ofReal_natCast
    ] using
      (
        (
          ENNReal.ofReal_lt_ofReal_iff
            (by positivity :
              0 < (k : ℝ) + 1)
        ).2
          (by linarith :
            (k : ℝ) < (k : ℝ) + 1)
      )

  rw [hCancel] at hLower

  exact
    hNatStrict.trans_le
      hLower

/--
The final resolved-PDE canonical physical witness has one cofinal subsequence
on which every real coercive radial weighted top-dissipation moment diverges.
-/
theorem exists_fixed_terminalSequence_with_canonicalArbitraryCoerciveRadialWeightUniversalEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalArbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf
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

  have hWeighted :
      H3TerminalPhysicalArbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf
        hH3 hClass σ :=
    arbitraryCoerciveRadialWeightUniversalEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
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
      hWeighted
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
