import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialNormalizedCurlMass

/-!
# Shrinking equatorial concentration of normalized curl

The preceding checkpoint proved a fixed-aperture statement: under hypothetical
nonextension together with one surviving physical-vorticity strong-H³ endpoint,
for every `0 < κ ≤ 1/2` and every `ε > 0`, arbitrarily close to `T` there are
two strict times whose normalized longitudinal curl-pair square mass on the
angular bad cone exceeds `ε² / 16`.

This file diagonalizes that statement with

    κ_n = 1 / (n + 2).

The shift by two ensures `κ_n ≤ 1/2` for every index, including `n = 0`.
We obtain strict terminal sequences `s_n,t_n -> T`, apertures `κ_n -> 0`,
and the uniform lower bound

    ε² / 16
      <
    normalized-curl-pair bad-cone mass

for every `n`.

This remains a conditional necessary mechanism under hypothetical
nonextension.  It does not assert existence of a singular solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedCurlConcentration
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Under hypothetical nonextension and one surviving physical-vorticity
strong-H³ endpoint, every `ε > 0` admits two strict terminal sequences
`s_n,t_n -> T` such that the normalized curl pair involving the longitudinal
coordinate keeps more than `ε²/16` square mass in the shrinking equatorial
bad cone of aperture

    κ_n = 1/(n+2).
-/
theorem exists_shrinkingEquatorialCone_normalizedLongitudinalCurlPairBadConeSquareDefect_sequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
          (
            ∀ n : ℕ,
              dist (s n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 2)
                ∧
              dist (t n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 2)
                ∧
              ε ^ 2 / 16
                  <
                h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
                  i
                  ((1 : ℝ) / ((n : ℝ) + 2))
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (s n)
                    (hs n))
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (t n)
                    (ht n))
          ) := by

  have hChoice :
      ∀ n : ℕ,
        ∃
          s : ℝ,
          ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
            ∃
              t : ℝ,
              ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
                dist s T
                    <
                  (1 : ℝ) / ((n : ℝ) + 2)
                  ∧
                dist t T
                    <
                  (1 : ℝ) / ((n : ℝ) + 2)
                  ∧
                ε ^ 2 / 16
                    <
                  h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
                    i
                    ((1 : ℝ) / ((n : ℝ) + 2))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      s
                      hs)
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ht) := by

    intro n

    have hκ :
        0
          <
        (1 : ℝ) / ((n : ℝ) + 2) := by
      positivity

    have hκHalf :
        (1 : ℝ) / ((n : ℝ) + 2)
          ≤
        1 / 2 := by

      have hn0 :
          (0 : ℝ)
            ≤
          (n : ℝ) := by
        positivity

      have hn :
          (2 : ℝ)
            ≤
          (n : ℝ) + 2 := by
        linarith

      exact
        one_div_le_one_div_of_le
          (by norm_num)
          hn

    exact
      exists_arbitrarilyLate_normalizedLongitudinalCurlPairBadConeSquareDefect_gt_sixteenth_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hκ
        hκHalf
        hε
        ((1 : ℝ) / ((n : ℝ) + 2))
        hκ

  choose s hs t ht hData using hChoice

  have hBase :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1)
        )
        atTop
        (𝓝 0) := by

    simpa only [
      Nat.cast_add,
      Nat.cast_one
    ] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hInv :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 2)
        )
        atTop
        (𝓝 0) := by

    have hShift :=
      hBase.comp
        (tendsto_add_atTop_nat 1)

    convert hShift using 1

    funext n

    norm_num [
      Nat.cast_add,
      Nat.cast_one
    ]

    ring

  have hNearT :
      ∀
        f : ℕ → ℝ,
        (
          ∀ n : ℕ,
            dist (f n) T
              <
            (1 : ℝ) / ((n : ℝ) + 2)
        ) →
        Tendsto f atTop (𝓝 T) := by

    intro f hf

    have hInvMetric := hInv

    rw [Metric.tendsto_atTop] at hInvMetric
    rw [Metric.tendsto_atTop]

    intro δ hδ

    obtain
      ⟨
        N : ℕ,
        hN
      ⟩ :=
      hInvMetric
        δ
        hδ

    refine
      ⟨
        N,
        ?_
      ⟩

    intro n hn

    have hAperture :
        (1 : ℝ) / ((n : ℝ) + 2)
          <
        δ := by

      have hDist :=
        hN n hn

      rw [
        Real.dist_eq,
        sub_zero,
        abs_of_pos
          (by positivity :
            0 < (1 : ℝ) / ((n : ℝ) + 2))
      ] at hDist

      exact hDist

    exact
      lt_trans
        (hf n)
        hAperture

  have hSTendsto :
      Tendsto s atTop (𝓝 T) :=
    hNearT
      s
      (fun n =>
        (hData n).1)

  have hTTendsto :
      Tendsto t atTop (𝓝 T) :=
    hNearT
      t
      (fun n =>
        (hData n).2.1)

  refine
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hInv,
      ?_
    ⟩

  intro n

  exact
    hData n

end

end Euclidean
end Bridge
end PrimeTensor
