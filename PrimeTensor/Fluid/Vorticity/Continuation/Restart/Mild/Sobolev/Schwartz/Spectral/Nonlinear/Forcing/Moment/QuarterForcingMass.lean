import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.ZerothForcingMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterFrozenFubini

/-!
# Quantitative quarter raw Fourier mass of the selected nonlinear forcing

The frozen selected `9/4` terminal kernel leaves exactly a quarter Fourier
weight on the terminal forcing after the second heat moment is integrated in
source time.

The qualitative quarter-moment integrability is already closed in
`NineQuarterFrozenFubini`, using

    |ξ|^(1/4) ≤ 1 + |ξ|.

This file makes that estimate numerical.  If

    m₀(N) = ∫ |N(ξ)|,
    m₁(N) = ∫ |ξ| |N(ξ)|,

then

    m_{1/4}(N) ≤ m₀(N) + m₁(N).

For the selected forcing both terms now have explicit envelopes:

    m₀(N_t) ≤ B₀(ν,A,t),
    m₁(N_t) ≤ B₁(ν,A,t).

Hence

    m_{1/4}(N_t)
      ≤
    B₀(ν,A,t) + B₁(ν,A,t).

This is exactly the scalar input needed by the quantitative frozen `9/4`
Duhamel endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quarter raw Fourier mass of one complete finite Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceQuarterMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ ((1 : ℝ) / 4) *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- Explicit selected-state quarter forcing envelope. -/
noncomputable def h3SelectedForcingQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3SelectedForcingL1Envelope ν A t +
    h3SelectedForcingFirstMomentEnvelope ν A t

/-- A quarter raw Fourier mass is bounded by zeroth plus first raw Fourier
masses. -/
theorem h3RawFinLerayOuterProductDivergenceQuarterMass_le_L1Mass_add_firstMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hQuarter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((1 : ℝ) / 4) *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3))
    (hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceQuarterMass U V i
      ≤
    h3RawFinLerayOuterProductDivergenceL1Mass U V i +
      h3RawFinLerayOuterProductDivergenceFirstMass U V i := by
  have hZero :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ +
            ‖ξ‖ *
              ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hZero.add hFirst

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ ((1 : ℝ) / 4) *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ +
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
    filter_upwards with ξ

    have hN0 :
        0 ≤ ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
      norm_nonneg _

    calc
      ‖ξ‖ ^ ((1 : ℝ) / 4) *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        (1 + ‖ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_quarter_rpow_le_one_add_norm ξ)
          hN0
      _ =
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ +
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
        ring

  have hIntegral :=
    integral_mono_ae hQuarter hMajor hDom

  unfold h3RawFinLerayOuterProductDivergenceQuarterMass
  unfold h3RawFinLerayOuterProductDivergenceL1Mass
  unfold h3RawFinLerayOuterProductDivergenceFirstMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ ((1 : ℝ) / 4) *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖h3RawFinLerayOuterProductDivergence U V i ξ‖ +
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
      rw [integral_add hZero hFirst]

/-- The selected terminal forcing quarter mass is bounded by the sum of the
explicit zeroth and first forcing envelopes. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceQuarterMass
        (W t) (W t) i
      ≤
    h3SelectedForcingQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hQuarter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((1 : ℝ) / 4) *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hBase :=
    h3RawFinLerayOuterProductDivergenceQuarterMass_le_L1Mass_add_firstMass
      (W t) (W t) i hQuarter hFirst

  have hZero :=
    h3RawFinLerayOuterProductDivergence_selectedRestart_L1Mass_le
      hν U₀ hA hU₀ ht htR i

  have hOne :=
    h3RawFinLerayOuterProductDivergence_selectedRestart_firstMass_le
      hν U₀ hA hU₀ ht htR i

  unfold h3SelectedForcingQuarterMomentEnvelope

  exact
    le_trans hBase
      (add_le_add hZero hOne)

end
end Euclidean
end Bridge
end PrimeTensor
