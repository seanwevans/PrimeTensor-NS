import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth

/-!
# Collapse the last forcing derivative branches

The canonical terminal `q F_j` and `q² F_j` paths are now differentiable at
every strict preterminal time.  Therefore the two forcing-driven derivative
obstructions in the fixed physical PDE channel alternative cannot occupy
their nondifferentiability branches.

Under hypothetical nonextension, one fixed coordinate consequently has one of
four cofinally unbounded Hilbert pairings:

1. lower-temporal;
2. top-dissipation;
3. fourth-temporal;
4. sixth-diffusion.

No auxiliary forcing nondifferentiability branch remains.
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
Under hypothetical nonextension, one fixed coordinate carries a cofinally
unbounded Hilbert pairing in one of the four resolved physical PDE channels.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_pairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  2 *
                    inner ℝ
                      (h3TerminalResolvedLowerTemporalHilbertState
                        hH3 hClass j₀ r)
                      (
                        deriv
                          (h3TerminalResolvedLowerTemporalHilbertState
                            hH3 hClass j₀)
                          r
                      )
                )
      )
        ∨
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  ∑ k : Fin 3,
                    2 *
                      inner ℝ
                        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                          hH3 hClass k r)
                        (
                          deriv
                            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                              hH3 hClass k)
                            r
                        )
                )
      )
        ∨
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  2 *
                    inner ℝ
                      (h3TerminalResolvedFourthTemporalHilbertState
                        hH3 hClass j₀ r)
                      (
                        deriv
                          (h3TerminalResolvedFourthTemporalHilbertState
                            hH3 hClass j₀)
                          r
                      )
                )
      )
        ∨
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  2 *
                    inner ℝ
                      (h3TerminalResolvedSixthDiffusionHilbertState
                        hH3 hClass j₀ r)
                      (
                        deriv
                          (h3TerminalResolvedSixthDiffusionHilbertState
                            hH3 hClass j₀)
                          r
                      )
                )
      ) := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_forcingDerivativeReduced_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      ?_
    ⟩

  rcases hBranch with hLower | hTop | hFourth | hSixth

  · exact
      Or.inl
        (
          lowerTemporal_pairing_cofinallyUnbounded_of_forcingDrivenHilbertDerivativeObstruction
            hH3 hClass j₀ hLower
        )

  · exact
      Or.inr
        (
          Or.inl hTop
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inl
                (
                  fourthTemporal_pairing_cofinallyUnbounded_of_forcingDrivenHilbertDerivativeObstruction
                    hH3 hClass j₀ hFourth
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr hSixth
            )
        )

/--
Neutral continuation form after eliminating both weighted-forcing
nondifferentiability branches.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_pairingCofinallyUnbounded
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
    (
      ∃ j₀ : Fin 3,
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    2 *
                      inner ℝ
                        (h3TerminalResolvedLowerTemporalHilbertState
                          hH3 hClass j₀ r)
                        (
                          deriv
                            (h3TerminalResolvedLowerTemporalHilbertState
                              hH3 hClass j₀)
                            r
                        )
                  )
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    ∑ k : Fin 3,
                      2 *
                        inner ℝ
                          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                            hH3 hClass k r)
                          (
                            deriv
                              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                                hH3 hClass k)
                              r
                          )
                  )
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    2 *
                      inner ℝ
                        (h3TerminalResolvedFourthTemporalHilbertState
                          hH3 hClass j₀ r)
                        (
                          deriv
                            (h3TerminalResolvedFourthTemporalHilbertState
                              hH3 hClass j₀)
                            r
                        )
                  )
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    2 *
                      inner ℝ
                        (h3TerminalResolvedSixthDiffusionHilbertState
                          hH3 hClass j₀ r)
                        (
                          deriv
                            (h3TerminalResolvedSixthDiffusionHilbertState
                              hH3 hClass j₀)
                            r
                        )
                  )
        )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_pairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
