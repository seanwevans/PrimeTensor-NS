import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Curl.Concentration
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Freeze one recurrent normalized curl channel

The shrinking equatorial concentration checkpoint gives a uniform lower bound

    ε² / 16

for the sum of the two normalized curl channels involving the surviving
longitudinal velocity coordinate.

This file separates those two channels explicitly.  Their bad-cone masses add
exactly to the previously defined normalized longitudinal curl-pair mass.
Therefore at every index at least one channel carries more than `ε² / 32`.

There are only two channels.  Infinite pigeonhole then freezes one channel on
an infinite, hence cofinal, set of indices.  Thus under hypothetical
nonextension with one surviving physical-vorticity strong-H³ endpoint there is
one fixed normalized curl channel that repeatedly carries a uniform positive
amount of square mass in thinner and thinner equatorial cones.

This is still a conditional necessary mechanism, not an existence theorem for
singular solutions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedCurlChannel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The two longitudinal curl channels -/

/--
The two normalized curl amplitudes involving longitudinal coordinate `i`.

`k = 0` and `k = 1` enumerate the two pairwise curl channels containing `i`.
-/
def h3TerminalNormalizedLongitudinalCurlChannelAmplitude
    (i : Fin 3)
    (k : Fin 2)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  if i = 0 then
    if k = 0 then
      h3TerminalNormalizedCurl01Amplitude ξ g
    else
      h3TerminalNormalizedCurl02Amplitude ξ g
  else if i = 1 then
    if k = 0 then
      h3TerminalNormalizedCurl01Amplitude ξ g
    else
      h3TerminalNormalizedCurl12Amplitude ξ g
  else
    if k = 0 then
      h3TerminalNormalizedCurl02Amplitude ξ g
    else
      h3TerminalNormalizedCurl12Amplitude ξ g

/--
The longitudinal normalized curl-pair square is exactly the sum of its two
named channel squares.
-/
theorem normalizedLongitudinalCurlPairSquareMagnitude_eq_channel_zero_add_one
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude i ξ g
      =
    ‖h3TerminalNormalizedLongitudinalCurlChannelAmplitude
        i (0 : Fin 2) ξ g‖ ^ 2
      +
    ‖h3TerminalNormalizedLongitudinalCurlChannelAmplitude
        i (1 : Fin 2) ξ g‖ ^ 2 := by

  fin_cases i <;>
    simp [
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude,
      h3TerminalNormalizedLongitudinalCurlChannelAmplitude
    ]

/-! ## Channel square integrability -/

private theorem normalizedLongitudinalCurlChannelSquare_aestronglyMeasurable
    (i : Fin 3)
    (k : Fin 2)
    (G H : H3SpectralFinVectorState) :
    AEStronglyMeasurable
      (
        fun ξ : H3FourierPoint3 =>
          norm
            (
              h3TerminalNormalizedLongitudinalCurlChannelAmplitude
                i k ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
      )
      volume := by

  let μ :
      Measure[
        measureSpaceOfInnerProductSpace.toMeasurableSpace
      ] H3FourierPoint3 :=
    volume

  change
    AEStronglyMeasurable
      (
        fun ξ : H3FourierPoint3 =>
          norm
            (
              h3TerminalNormalizedLongitudinalCurlChannelAmplitude
                i k ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
      )
      μ

  have hD :
      ∀ j : Fin 3,
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedDerivativeSymbol j ξ)
          μ := by
    intro j
    exact
      (measurable_h3TerminalNormalizedDerivativeSymbol j).aestronglyMeasurable

  have hG :
      ∀ j : Fin 3,
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            h3TerminalSpectralDifferenceAt G H j ξ)
          μ := by
    intro j
    unfold h3TerminalSpectralDifferenceAt
    exact
      (MeasureTheory.Lp.aestronglyMeasurable (G j)).sub
        (MeasureTheory.Lp.aestronglyMeasurable (H j))

  have h01 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl01Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl01Amplitude
    exact
      ((hD 1).mul (hG 0)).sub
        ((hD 0).mul (hG 1))

  have h02 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl02Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl02Amplitude
    exact
      ((hD 2).mul (hG 0)).sub
        ((hD 0).mul (hG 2))

  have h12 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl12Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl12Amplitude
    exact
      ((hD 2).mul (hG 1)).sub
        ((hD 1).mul (hG 2))

  have h01sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl01Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h01.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  have h02sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl02Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h02.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  have h12sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl12Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h12.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  fin_cases i <;>
    fin_cases k <;>
    simp [
      h3TerminalNormalizedLongitudinalCurlChannelAmplitude
    ] <;>
    assumption

private theorem normalizedLongitudinalCurlChannelSquare_integrable
    (i : Fin 3)
    (k : Fin 2)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (
        fun ξ : H3FourierPoint3 =>
          norm
            (
              h3TerminalNormalizedLongitudinalCurlChannelAmplitude
                i k ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
      )
      volume := by

  have h0 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 0) (H 0)

  have h1 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 1) (H 1)

  have h2 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 2) (H 2)

  have hMajor :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            4 *
              (
                ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
                  +
                ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
                  +
                ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
              )
        )
        volume :=
    ((h0.add h1).add h2).const_mul 4

  apply
    Integrable.mono'
      hMajor
      (
        normalizedLongitudinalCurlChannelSquare_aestronglyMeasurable
          i k G H
      )

  filter_upwards with ξ

  have hPair :
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
          i ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt G H j ξ)
        ≤
      4 *
        (
          ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
            +
          ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
            +
          ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
        ) :=
    normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
      i ξ
      (fun j =>
        h3TerminalSpectralDifferenceAt G H j ξ)

  have hChannelLePair :
      norm
        (
          h3TerminalNormalizedLongitudinalCurlChannelAmplitude
            i k ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2
        ≤
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
        i ξ
        (fun j =>
          h3TerminalSpectralDifferenceAt G H j ξ) := by

    fin_cases i <;>
      fin_cases k <;>
      simp [
        h3TerminalNormalizedLongitudinalCurlChannelAmplitude,
        h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
      ] <;>
      positivity

  have hNonneg :
      0
        ≤
      norm
        (
          h3TerminalNormalizedLongitudinalCurlChannelAmplitude
            i k ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2 :=
    sq_nonneg _

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hNonneg
  ]

  exact
    le_trans
      hChannelLePair
      hPair

/-! ## Individual bad-cone channel mass -/

/--
Square mass of one of the two normalized longitudinal curl channels on the
angular bad cone.
-/
noncomputable def h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
    (i : Fin 3)
    (k : Fin 2)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    norm
      (
        h3TerminalNormalizedLongitudinalCurlChannelAmplitude
          i k ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt G H j ξ)
      ) ^ 2

/--
The normalized longitudinal curl-pair bad-cone mass is exactly the sum of its
two individual channel masses.
-/
theorem normalizedLongitudinalCurlPairBadConeSquareDefect_eq_channel_zero_add_one
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
        i κ G H
      =
    h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i (0 : Fin 2) κ G H
      +
    h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i (1 : Fin 2) κ G H := by

  have h0 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedLongitudinalCurlChannelAmplitude
                  i (0 : Fin 2) ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        (volume.restrict
          (h3TerminalLongitudinalAngularBadCone i κ)) :=
    (
      normalizedLongitudinalCurlChannelSquare_integrable
        i (0 : Fin 2) G H
    ).mono_measure
      Measure.restrict_le_self

  have h1 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedLongitudinalCurlChannelAmplitude
                  i (1 : Fin 2) ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        (volume.restrict
          (h3TerminalLongitudinalAngularBadCone i κ)) :=
    (
      normalizedLongitudinalCurlChannelSquare_integrable
        i (1 : Fin 2) G H
    ).mono_measure
      Measure.restrict_le_self

  unfold
    h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
    h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect

  simp_rw [
    normalizedLongitudinalCurlPairSquareMagnitude_eq_channel_zero_add_one
  ]

  exact
    integral_add h0 h1

/--
If the pair mass is larger than `C`, then one of its two individual channel
masses is larger than `C/2`.
-/
theorem exists_normalizedLongitudinalCurlChannelBadConeSquareDefect_gt_half_of_pair
    (i : Fin 3)
    (κ C : ℝ)
    (G H : H3SpectralFinVectorState)
    (hPair :
      C
        <
      h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
        i κ G H) :
    ∃ k : Fin 2,
      C / 2
        <
      h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i k κ G H := by

  by_contra hNo

  simp only [
    not_exists,
    not_lt
  ] at hNo

  have h0 :=
    hNo (0 : Fin 2)

  have h1 :=
    hNo (1 : Fin 2)

  rw [
    normalizedLongitudinalCurlPairBadConeSquareDefect_eq_channel_zero_add_one
  ] at hPair

  linarith

/-! ## Freeze one recurrent channel -/

/--
Along the shrinking equatorial normalized-curl concentration sequence, one
fixed channel recurs cofinally often with square mass above `ε²/32`.
-/
theorem exists_cofinally_recurrent_normalizedLongitudinalCurlChannel_on_shrinkingEquatorialCone_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          Tendsto s atTop (𝓝 T)
            ∧
          Tendsto t atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (1 : ℝ) / ((n : ℝ) + 2)
            )
            atTop
            (𝓝 0)
            ∧
          ∃ k : Fin 2,
            ∀ N : ℕ,
              ∃ n : ℕ,
                N ≤ n
                  ∧
                ε ^ 2 / 32
                    <
                  h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
                    i k
                    ((1 : ℝ) / ((n : ℝ) + 2))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (s n)
                      (hs n))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (t n)
                      (ht n)) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hPairData
    ⟩ :=
    exists_shrinkingEquatorialCone_normalizedLongitudinalCurlPairBadConeSquareDefect_sequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  have hChannelChoice :
      ∀ n : ℕ,
        ∃ k : Fin 2,
          ε ^ 2 / 32
            <
          h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
            i k
            ((1 : ℝ) / ((n : ℝ) + 2))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (s n)
              (hs n))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (t n)
              (ht n)) := by

    intro n

    have hPair :=
      (hPairData n).2.2

    have hOne :=
      exists_normalizedLongitudinalCurlChannelBadConeSquareDefect_gt_half_of_pair
        i
        ((1 : ℝ) / ((n : ℝ) + 2))
        (ε ^ 2 / 16)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (s n)
          (hs n))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (t n)
          (ht n))
        hPair

    obtain ⟨k, hk⟩ :=
      hOne

    refine
      ⟨
        k,
        ?_
      ⟩

    convert hk using 1 <;> ring

  choose channel hChannelMass using hChannelChoice

  obtain
    ⟨
      kStar,
      hInfinite
    ⟩ :=
    Finite.exists_infinite_fiber
      channel

  rw [Set.infinite_coe_iff] at hInfinite

  have hCofinal :
      ∀ N : ℕ,
        ∃ n : ℕ,
          N ≤ n
            ∧
          ε ^ 2 / 32
              <
            h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
              i kStar
              ((1 : ℝ) / ((n : ℝ) + 2))
              (h3TerminalVelocitySpectralStateAt
                hH3
                (s n)
                (hs n))
              (h3TerminalVelocitySpectralStateAt
                hH3
                (t n)
                (ht n)) := by

    intro N

    obtain
      ⟨
        n,
        hnFiber,
        hNn
      ⟩ :=
      Set.Infinite.exists_gt
        hInfinite
        N

    have hChannelEq :
        channel n = kStar := by
      change channel n = kStar at hnFiber
      exact hnFiber

    have hMass :=
      hChannelMass n

    rw [
      hChannelEq
    ] at hMass

    exact
      ⟨
        n,
        Nat.le_of_lt hNn,
        hMass
      ⟩

  exact
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      kStar,
      hCofinal
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
