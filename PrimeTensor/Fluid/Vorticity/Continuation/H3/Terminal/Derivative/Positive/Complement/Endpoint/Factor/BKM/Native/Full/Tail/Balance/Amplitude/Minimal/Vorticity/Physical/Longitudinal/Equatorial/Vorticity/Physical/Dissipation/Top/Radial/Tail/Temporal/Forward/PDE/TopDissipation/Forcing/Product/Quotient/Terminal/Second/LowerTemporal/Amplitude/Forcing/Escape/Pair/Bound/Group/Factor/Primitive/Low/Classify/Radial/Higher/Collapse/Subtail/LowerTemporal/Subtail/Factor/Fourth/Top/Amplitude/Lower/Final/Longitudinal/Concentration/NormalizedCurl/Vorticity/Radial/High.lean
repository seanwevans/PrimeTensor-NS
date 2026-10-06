import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Raw.Vorticity.High.Radial.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Infrared.Vanishing.From.Raw.L2.Cauchy

/-!
# Eliminate the infrared branch on the synchronized final witness

The synchronized witness has one fixed complementary normalized-vorticity
component and, for every positive radial cutoff, a frozen low/high radial
alternative.

Set the cutoff to `ρ = 1`.

The low-radial branch is incompatible with the terminal raw-Fourier `L²`
Cauchy hypothesis: below unit frequency the normalized-vorticity defect is
bounded by sixteen times the raw velocity square defect, while the latter
vanishes for the two synchronized terminal sequences.

Hence only the high-radial branch survives.  The existing radial multiplier
estimate then upgrades its normalized-vorticity mass to a quantitative raw
vorticity high-radial square-mass lower bound.

The original `τ`, `p`, `q`, fixed complementary component, and strictly
increasing selector are all retained.
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
Under raw-Fourier `L²` Cauchy, the synchronized final witness cannot remain in
the unit-cutoff infrared branch.  Along the same fixed complementary component
and subsequence it therefore carries positive raw-vorticity mass above unit
radial frequency in the shrinking equatorial cone.
-/
theorem exists_fixed_terminalSequence_with_fixed_complementary_highRadialRawVorticity_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
            ∃ r : Fin 3,
              r ≠ i
                ∧
              ∃ k : ℕ → ℕ,
                StrictMono k
                  ∧
                Tendsto
                  (fun n : ℕ => τ (p (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => τ (q (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
                  )
                  atTop
                  (𝓝 0)
                  ∧
                (
                  ∀ n : ℕ,
                    ENNReal.ofReal (ε ^ 2 / 64)
                      <
                    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
                      i r
                      ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                      1
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (q (k n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (q (k n))).1.1,
                          (hτ (q (k n))).1.2
                        ⟩)
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (p (k n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (p (k n))).1.1,
                          (hτ (p (k n))).1.2
                        ⟩)
                ) := by

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
      r,
      hrNe,
      k,
      hKMono,
      hTauPK,
      hTauQK,
      hAperture,
      hBranch
    ⟩ :=
    exists_fixed_terminalSequence_with_fixed_complementary_normalizedVorticity_fixedRadialBranch_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε
      (ρ := (1 : ℝ))
      zero_lt_one

  let hStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1.1,
        (hτ n).1.2
      ⟩

  have hHigh :
      ∀ n : ℕ,
        ε ^ 2 / 64
          <
        h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
          i r
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (k n)))
            (hStrict (q (k n))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (k n)))
            (hStrict (p (k n)))) := by

    rcases hBranch with hLow | hHigh

    · exfalso

      have hDelta :
          0 < ε ^ 2 / 1024 := by
        positivity

      obtain
        ⟨η, hη, hRawSmall⟩ :=
        hCauchy
          (ε ^ 2 / 1024)
          hDelta

      have hPMetric := hTauPK
      rw [Metric.tendsto_atTop] at hPMetric

      obtain
        ⟨NP, hPNear⟩ :=
        hPMetric
          η
          hη

      have hQMetric := hTauQK
      rw [Metric.tendsto_atTop] at hQMetric

      obtain
        ⟨NQ, hQNear⟩ :=
        hQMetric
          η
          hη

      let n : ℕ :=
        max NP NQ

      have hNPn :
          NP ≤ n := by
        dsimp only [n]
        exact
          le_max_left NP NQ

      have hNQn :
          NQ ≤ n := by
        dsimp only [n]
        exact
          le_max_right NP NQ

      have hpNear :
          dist (τ (p (k n))) T < η :=
        hPNear
          n
          hNPn

      have hqNear :
          dist (τ (q (k n))) T < η :=
        hQNear
          n
          hNQn

      let G :=
        h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (k n)))
          (hStrict (q (k n)))

      let H :=
        h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (k n)))
          (hStrict (p (k n)))

      have hRaw :
          h3TerminalRawVelocityFourierTotalSquareDefect G H
            <
          ε ^ 2 / 1024 := by

        dsimp only [G, H]

        exact
          hRawSmall
            (τ (q (k n)))
            (τ (p (k n)))
            (hStrict (q (k n)))
            (hStrict (p (k n)))
            hqNear
            hpNear

      have hLowLe :
          h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
              i r
              ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
              1
              G H
            ≤
          16 *
            h3TerminalRawVelocityFourierTotalSquareDefect
              G H :=
        normalizedVorticityComponentBadConeLowRadialSquareDefect_one_le_sixteen_mul_rawVelocityFourierTotalSquareDefect
          i
          r
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          G H

      have hLowN :
          ε ^ 2 / 64
            <
          h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
              i r
              ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
              1
              G H := by

        dsimp only [G, H]

        exact
          hLow n

      nlinarith

    · exact
        hHigh

  have hRawHigh :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i r
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (k n)))
            (hStrict (q (k n))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (k n)))
            (hStrict (p (k n)))) := by

    intro n

    have h :=
      rawVorticityComponentBadConeHighRadialSquareMass_gt_of_normalizedVorticityComponentBadConeHighRadialSquareDefect_gt
        (ρ := (1 : ℝ))
        zero_lt_one
        (by positivity : 0 ≤ ε ^ 2 / 64)
        i
        r
        ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (k n)))
          (hStrict (q (k n))))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (k n)))
          (hStrict (p (k n))))
        (hHigh n)

    simpa only [one_pow, one_mul] using
      h

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
      r,
      hrNe,
      k,
      hKMono,
      hTauPK,
      hTauQK,
      hAperture,
      ?_
    ⟩

  intro n

  have h :=
    hRawHigh n

  simpa only [hStrict] using
    h

end

end Euclidean
end Bridge
end PrimeTensor
