import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Scalar.Lower.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Equatorial.Polarization

/-!
# Package the final single-time physical dissipation geometry

The synchronized resolved-PDE witness now carries a single strict-time
physical H³ dissipation concentration sequence at unit radial cutoff.

This file records two consequences on exactly that same sequence.

* The localized mass gives a uniform ordinary real lower bound for the total
  physical H³ dissipation.
* Every frequency selected from the shrinking bad-cone/high-radial region is
  asymptotically equatorially polarized: its normalized longitudinal
  derivative symbol tends to zero.

No further subsequence or replacement terminal witness is introduced.

After this package, the remaining obstruction is a concentration--compactness
question for the physical H³ dissipation measure: radial escape versus
small-volume concentration.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

theorem exists_fixed_terminalSequence_with_singleTimePhysicalDissipationGeometry_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                      ∀ n : ℕ,
                        ε ^ 2 / 64
                          <
                        16 * velocityH3DissipationAt u (σ n)
                    )
                      ∧
                    (
                      ∀ ξ : ℕ → H3FourierPoint3,
                        (
                          ∀ n : ℕ,
                            ξ n ∈
                              h3TerminalLongitudinalAngularBadCone
                                  i
                                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                                \
                              h3TerminalRadialFrequencyBelow 1
                        )
                          →
                        Tendsto
                          (
                            fun n : ℕ =>
                              norm
                                (
                                  h3TerminalNormalizedDerivativeSymbol
                                    i
                                    (ξ n)
                                )
                          )
                          atTop
                          (𝓝 0)
                    )
                      ∧
                    ¬
                      H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
                        hH3 hClass i 1 := by

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
      σ,
      hσ,
      hSigma,
      hLocal,
      hNotVanishing
    ⟩ :=
    exists_fixed_terminalSequence_with_singleTimePhysicalDissipationConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hScalar :
      ∀ n : ℕ,
        ε ^ 2 / 64
          <
        16 * velocityH3DissipationAt u (σ n) := by

    intro n

    let htAbs :
        σ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1
          (hσ n).1,
        (hσ n).2
      ⟩

    have hMassLe :
        h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3
            i
            ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
            1
            (σ n)
            htAbs
          ≤
        ENNReal.ofReal
          (velocityH3DissipationAt u (σ n)) := by

      exact
        h3TerminalPhysicalDissipationBadConeHighRadialMass_le_ofReal_dissipation
          hH3
          hClass
          (hσ n)
          i
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1

    have hENN :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        16 *
          ENNReal.ofReal
            (velocityH3DissipationAt u (σ n)) := by

      exact
        (hLocal n).trans_le
          (
            mul_le_mul_of_nonneg_left
              hMassLe
              (by positivity)
          )

    have hDNonneg :
        0 ≤ velocityH3DissipationAt u (σ n) :=
      velocityH3DissipationAt_nonneg
        u
        (σ n)

    have hDPos :
        0 < velocityH3DissipationAt u (σ n) := by

      by_contra hNotPos

      have hDLe :
          velocityH3DissipationAt u (σ n) ≤ 0 :=
        le_of_not_gt
          hNotPos

      have hDZero :
          velocityH3DissipationAt u (σ n) = 0 :=
        le_antisymm
          hDLe
          hDNonneg

      rw [hDZero] at hENN
      norm_num at hENN

    have hScaled :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        ENNReal.ofReal
          (
            16 *
              velocityH3DissipationAt u (σ n)
          ) := by

      calc
        ENNReal.ofReal (ε ^ 2 / 64)
            <
          16 *
            ENNReal.ofReal
              (velocityH3DissipationAt u (σ n)) :=
          hENN

        _ =
          ENNReal.ofReal
            (
              16 *
                velocityH3DissipationAt u (σ n)
            ) := by

          rw [
            ENNReal.ofReal_mul
              (by norm_num : (0 : ℝ) ≤ 16)
          ]
          norm_num

    exact
      (
        ENNReal.ofReal_lt_ofReal_iff
          (
            mul_pos
              (by norm_num : (0 : ℝ) < 16)
              hDPos
          )
      ).1
        hScaled

  have hPolarization :
      ∀ ξ : ℕ → H3FourierPoint3,
        (
          ∀ n : ℕ,
            ξ n ∈
              h3TerminalLongitudinalAngularBadCone
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                \
              h3TerminalRadialFrequencyBelow 1
        )
          →
        Tendsto
          (
            fun n : ℕ =>
              norm
                (
                  h3TerminalNormalizedDerivativeSymbol
                    i
                    (ξ n)
                )
          )
          atTop
          (𝓝 0) := by

    intro ξ hξ

    apply
      squeeze_zero'

    · exact
        Filter.Eventually.of_forall
          (
            fun n =>
              norm_nonneg
                (
                  h3TerminalNormalizedDerivativeSymbol
                    i
                    (ξ n)
                )
          )

    · exact
        Filter.Eventually.of_forall
          (
            fun n =>
              le_of_lt
                (
                  norm_normalizedLongitudinalDerivativeSymbol_lt_of_mem_badCone
                    ((hξ n).1)
                )
          )

    · exact
        hAperture

  exact
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
      σ,
      hσ,
      hSigma,
      hLocal,
      hScalar,
      hPolarization,
      hNotVanishing
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
