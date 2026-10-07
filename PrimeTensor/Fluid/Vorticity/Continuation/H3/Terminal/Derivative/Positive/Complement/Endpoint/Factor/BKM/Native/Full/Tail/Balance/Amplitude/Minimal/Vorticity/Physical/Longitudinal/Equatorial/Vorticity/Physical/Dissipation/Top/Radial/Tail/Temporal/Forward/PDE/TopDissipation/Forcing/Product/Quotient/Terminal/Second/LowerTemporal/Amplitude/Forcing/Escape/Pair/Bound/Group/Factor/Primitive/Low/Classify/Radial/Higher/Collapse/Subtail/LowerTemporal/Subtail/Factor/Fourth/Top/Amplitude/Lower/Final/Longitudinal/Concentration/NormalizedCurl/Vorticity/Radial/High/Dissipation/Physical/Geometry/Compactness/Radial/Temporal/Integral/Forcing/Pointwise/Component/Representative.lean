import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative

/-!
# Canonical raw third-radial forcing mass rate

The frozen canonical forcing component has an exact raw Fourier representative:
on every strict time,

    rawMass_j(t) = ‖F'''_j(t)‖₂².

Hence the reciprocal shrinking-interval lower bound obtained for the fixed
third-radial Hilbert component transfers without loss to the raw nonlinear PDE
mass itself.

No new subsequence is introduced beyond the finite coordinate extraction
already present in the canonical component witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

def H3TerminalPhysicalTopDissipationFixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              Tendsto
                  (fun n : ℕ => s (φ n))
                  atTop
                  (𝓝 T)
                ∧
              Tendsto
                  (fun n : ℕ => σ (m (q (φ n))))
                  atTop
                  (𝓝 T)
                ∧
              (
                ∀ n : ℕ,
                  s (φ n) < σ (m (q (φ n)))
              )
                ∧
              (
                ∀ n : ℕ,
                  r (φ n) ∈
                    Set.Icc
                      (s (φ n))
                      (σ (m (q (φ n))))
              )
                ∧
              Tendsto
                  (fun n : ℕ => r (φ n))
                  atTop
                  (𝓝 T)
                ∧
              (
                ∀ n : ℕ,
                  δ
                      /
                    (
                      6
                        *
                      (2 * Real.pi) ^ 6
                        *
                      (
                        σ (m (q (φ n)))
                          -
                        s (φ n)
                      )
                    )
                    <
                  h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
                    hH3 hClass j₀ (r (φ n))
              )
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
                      hH3 hClass j₀ (r (φ n))
                )
                atTop
                atTop

theorem fixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf_of_fixedComponentCanonicalPointwiseRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hFixed :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      hmTop,
      hqTop,
      hPhiMono,
      s,
      r,
      hs,
      hσ,
      hsPhi,
      hSigmaPhi,
      hForward,
      hr,
      hrPhi,
      hRate,
      hNormTop
    ⟩ :=
    hFixed

  have hrClass :
      ∀ n : ℕ,
        r (φ n) ∈ Set.Ioo a T := by

    intro n

    exact
      ⟨
        lt_of_lt_of_le
          (hs (φ n)).1
          (hr n).1,
        lt_of_le_of_lt
          (hr n).2
          (hσ (m (q (φ n)))).2
      ⟩

  have hRawRate :
      ∀ n : ℕ,
        δ
            /
          (
            6
              *
            (2 * Real.pi) ^ 6
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
          hH3 hClass j₀ (r (φ n)) := by

    intro n

    rw [
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
        hH3
        hClass
        (hrClass n)
        j₀
    ]

    exact
      hRate n

  have hSqTop :
      Tendsto
        (
          fun n : ℕ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j₀ (r (φ n))‖ : ℝ
            ) ^ 2
        )
        atTop
        atTop := by

    exact
      (
        tendsto_pow_atTop
          (α := ℝ)
          (by norm_num : (2 : ℕ) ≠ 0)
      ).comp
        hNormTop

  have hEventuallyEq :
      (
        fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
            hH3 hClass j₀ (r (φ n))
      )
        =ᶠ[atTop]
      (
        fun n : ℕ =>
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j₀ (r (φ n))‖ : ℝ
          ) ^ 2
      ) := by

    exact
      Filter.Eventually.of_forall
        (
          fun n =>
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
              hH3
              hClass
              (hrClass n)
              j₀
        )

  have hRawTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
              hH3 hClass j₀ (r (φ n))
        )
        atTop
        atTop :=

    hSqTop.congr'
      hEventuallyEq.symm

  exact
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      hmTop,
      hqTop,
      hPhiMono,
      s,
      r,
      hs,
      hσ,
      hsPhi,
      hSigmaPhi,
      hForward,
      hr,
      hrPhi,
      hRawRate,
      hRawTop
    ⟩

theorem exists_fixed_terminalSequence_with_canonicalFixedThirdRadialForcingRawFourierMassRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf
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
      hFixed
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalFixedThirdRadialForcingComponentRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hRaw :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf_of_fixedComponentCanonicalPointwiseRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hFixed

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hRaw
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
