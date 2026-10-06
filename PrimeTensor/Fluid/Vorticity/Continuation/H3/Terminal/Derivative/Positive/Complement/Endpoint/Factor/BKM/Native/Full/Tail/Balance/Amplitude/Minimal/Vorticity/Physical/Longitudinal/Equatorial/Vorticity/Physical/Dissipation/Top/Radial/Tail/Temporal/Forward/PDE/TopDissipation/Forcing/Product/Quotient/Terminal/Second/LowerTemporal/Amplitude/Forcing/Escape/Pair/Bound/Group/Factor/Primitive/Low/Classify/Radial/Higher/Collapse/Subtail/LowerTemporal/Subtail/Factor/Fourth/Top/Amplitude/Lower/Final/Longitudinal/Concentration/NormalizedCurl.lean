import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Curl.Mass

/-!
# Synchronize the final witness with normalized-curl equatorial mass

The final resolved-PDE witness now carries, on one common terminal sequence,

* total H³-energy escape;
* same-index longitudinal spectral H³ escape;
* a cofinal pair `p n ≤ q n` whose longitudinal difference retains a fixed
  positive amount of mass in the shrinking equatorial cone.

The surviving physical-vorticity strong-H³ endpoint makes the transverse
velocity pair strongly H³ Cauchy.  Since `τ (p n), τ (q n) -> T`, the
transverse square defect is eventually small on this exact same cofinal pair.

Combining that eventual transverse smallness with the integrated normalized
curl inequality upgrades the already synchronized longitudinal bad-cone mass
to a uniform normalized-curl bad-cone lower bound on the same pair.

No additional subsequence is introduced.
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
A fixed positive longitudinal bad-cone defect together with a small transverse
global defect forces positive normalized longitudinal curl-pair mass on the
same cone.
-/
theorem normalizedLongitudinalCurlPairBadConeSquareDefect_gt_sixteenth_of_longitudinalBadCone_and_transverseSmall
    {i : Fin 3}
    {κ ε : ℝ}
    (hκ : 0 < κ)
    (hκHalf : κ ≤ 1 / 2)
    (hε : 0 < ε)
    (G H : H3SpectralFinVectorState)
    (hLong :
      ε ^ 2 / 2
        <
      h3TerminalLongitudinalBadConeSquareDefect
        i κ G H)
    (hTransGlobal :
      h3TerminalTransverseSpectralNormSquareMagnitude
          i G H
        <
      ε ^ 2 / 2) :
    ε ^ 2 / 16
      <
    h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
      i κ G H := by

  have hTransBad :
      h3TerminalTransverseBadConeSquareDefect
          i κ G H
        <
      ε ^ 2 / 2 := by

    have hLe :=
      transverseBadConeSquareDefect_le_globalNormSquare
        i κ G H

    exact
      lt_of_le_of_lt
        hLe
        hTransGlobal

  have hTransBadNonneg :
      0
        ≤
      h3TerminalTransverseBadConeSquareDefect
        i κ G H := by

    unfold h3TerminalTransverseBadConeSquareDefect

    apply integral_nonneg

    intro ξ

    fin_cases i <;>
      simp [
        h3TerminalTransverseSpectralSquareMagnitude
      ] <;>
      positivity

  have hIntegrated :=
    half_one_sub_sq_mul_longitudinalBadCone_le_normalizedCurlPairBadCone_add_sq_mul_transverseBadCone
      (i := i)
      hκ
      G H

  have hκsq :
      κ ^ 2
        ≤
      1 / 4 := by

    nlinarith [
      sq_nonneg κ
    ]

  have hCoef :
      3 / 8
        ≤
      (1 / 2 : ℝ) * (1 - κ ^ 2) := by

    nlinarith

  have hCoefPos :
      0
        <
      (1 / 2 : ℝ) * (1 - κ ^ 2) := by

    nlinarith

  have hMainLower :
      3 * ε ^ 2 / 16
        <
      (1 / 2 : ℝ)
          *
        (1 - κ ^ 2)
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ G H := by

    have hFirst :
        3 * ε ^ 2 / 16
          ≤
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        (ε ^ 2 / 2) := by

      nlinarith [
        sq_nonneg ε
      ]

    have hSecond :
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        (ε ^ 2 / 2)
          <
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ G H := by

      exact
        mul_lt_mul_of_pos_left
          hLong
          hCoefPos

    exact
      lt_of_le_of_lt
        hFirst
        hSecond

  have hErrUpper :
      κ ^ 2
          *
        h3TerminalTransverseBadConeSquareDefect
          i κ G H
        <
      ε ^ 2 / 8 := by

    calc
      κ ^ 2
            *
          h3TerminalTransverseBadConeSquareDefect
            i κ G H
          ≤
        (1 / 4 : ℝ)
            *
          h3TerminalTransverseBadConeSquareDefect
            i κ G H :=
              mul_le_mul_of_nonneg_right
                hκsq
                hTransBadNonneg

      _ <
        (1 / 4 : ℝ) * (ε ^ 2 / 2) :=
          mul_lt_mul_of_pos_left
            hTransBad
            (by norm_num)

      _ =
        ε ^ 2 / 8 := by
          ring

  linarith

/--
On the exact cofinal pair already selected from the final resolved-PDE witness,
normalized longitudinal curl-pair bad-cone mass is uniformly positive for all
sufficiently large indices.

The original `τ`, `p`, and `q` are retained; only an eventual threshold `N` is
introduced.
-/
theorem exists_fixed_terminalSequence_with_eventual_normalizedCurlEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          ∃ p q : ℕ → ℕ,
            (∀ n : ℕ, n ≤ p n)
              ∧
            (∀ n : ℕ, p n ≤ q n)
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ =>
                velocityH3EnergyAt u (τ n))
              atTop atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  norm
                    (
                      h3TerminalVelocityComponentSpectralStateAt
                        hH3
                        i
                        (τ n)
                        ⟨
                          lt_trans hClass.terminal_start.1 (hτ n).1.1,
                          (hτ n).1.2
                        ⟩
                    )
              )
              atTop
              atTop
              ∧
            Tendsto
              (fun n : ℕ => τ (p n))
              atTop
              (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ => τ (q n))
              atTop
              (𝓝 T)
              ∧
            ∃ N : ℕ,
              1 ≤ N
                ∧
              ∀ n : ℕ,
                N ≤ n →
                  ε ^ 2 / 16
                    <
                  h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
                    i
                    ((1 : ℝ) / ((n : ℝ) + 1))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (τ (q n))
                      ⟨
                        lt_trans hClass.terminal_start.1
                          (hτ (q n)).1.1,
                        (hτ (q n)).1.2
                      ⟩)
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (τ (p n))
                      ⟨
                        lt_trans hClass.terminal_start.1
                          (hτ (p n)).1.1,
                        (hτ (p n)).1.2
                      ⟩) := by

  obtain
    ⟨
      j₀,
      τ,
      hτ,
      p,
      q,
      hnp,
      hpq,
      hTau,
      hEnergyTop,
      hLongTop,
      hTauP,
      hTauQ,
      hBad
    ⟩ :=
    exists_fixed_terminalSequence_with_cofinal_shrinkingEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  let hStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1.1,
        (hτ n).1.2
      ⟩

  obtain
    ⟨
      η,
      hη,
      hTransNear
    ⟩ :=
    transverseSpectralNormSquareMagnitude_lt_half_sq_of_actualVorticityStrongH3EndpointPath
      hH3
      hPhysical
      hε

  have hPMetric := hTauP
  rw [Metric.tendsto_atTop] at hPMetric

  obtain
    ⟨NP, hPNear⟩ :=
    hPMetric
      η
      hη

  have hQMetric := hTauQ
  rw [Metric.tendsto_atTop] at hQMetric

  obtain
    ⟨NQ, hQNear⟩ :=
    hQMetric
      η
      hη

  let N : ℕ :=
    max 1 (max NP NQ)

  have hN1 :
      1 ≤ N := by
    dsimp only [N]
    exact
      le_max_left 1 (max NP NQ)

  refine
    ⟨
      j₀,
      τ,
      hτ,
      p,
      q,
      hnp,
      hpq,
      hTau,
      hEnergyTop,
      hLongTop,
      hTauP,
      hTauQ,
      N,
      hN1,
      ?_
    ⟩

  intro n hn

  have hOneN :
      1 ≤ n :=
    hN1.trans hn

  have hNPN :
      NP ≤ N := by
    dsimp only [N]
    exact
      le_trans
        (le_max_left NP NQ)
        (le_max_right 1 (max NP NQ))

  have hNQN :
      NQ ≤ N := by
    dsimp only [N]
    exact
      le_trans
        (le_max_right NP NQ)
        (le_max_right 1 (max NP NQ))

  have hNPn :
      NP ≤ n :=
    hNPN.trans hn

  have hNQn :
      NQ ≤ n :=
    hNQN.trans hn

  have hpNear :
      dist (τ (p n)) T < η :=
    hPNear
      n
      hNPn

  have hqNear :
      dist (τ (q n)) T < η :=
    hQNear
      n
      hNQn

  let κ : ℝ :=
    (1 : ℝ) / ((n : ℝ) + 1)

  have hκ :
      0 < κ := by
    dsimp only [κ]
    positivity

  have hκHalf :
      κ ≤ 1 / 2 := by

    have hCast :
        (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hOneN

    have hDen :
        (2 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith

    dsimp only [κ]

    exact
      one_div_le_one_div_of_le
        (by norm_num)
        hDen

  have hGlobalTrans :
      h3TerminalTransverseSpectralNormSquareMagnitude
          i
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q n))
            (hStrict (q n)))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p n))
            (hStrict (p n)))
        <
      ε ^ 2 / 2 := by

    exact
      hTransNear
        (τ (q n))
        (hStrict (q n))
        (τ (p n))
        (hStrict (p n))
        hqNear
        hpNear

  have hLong :
      ε ^ 2 / 2
        <
      h3TerminalLongitudinalBadConeSquareDefect
        i κ
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q n))
          (hStrict (q n)))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p n))
          (hStrict (p n))) := by

    have h :=
      hBad n

    simpa only [κ, hStrict] using
      h

  have hCurl :=
    normalizedLongitudinalCurlPairBadConeSquareDefect_gt_sixteenth_of_longitudinalBadCone_and_transverseSmall
      hκ
      hκHalf
      hε
      (h3TerminalVelocitySpectralStateAt
        hH3
        (τ (q n))
        (hStrict (q n)))
      (h3TerminalVelocitySpectralStateAt
        hH3
        (τ (p n))
        (hStrict (p n)))
      hLong
      hGlobalTrans

  simpa only [κ, hStrict] using
    hCurl

end

end Euclidean
end Bridge
end PrimeTensor
